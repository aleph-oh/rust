use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::work_queue::WorkQueue;
use rustc_data_structures::{fx::FxHashMap, sync::HashMapExt};
use rustc_index::IndexSlice;
use rustc_index::{bit_set::BitSet, IndexVec};
use rustc_middle::mir::{self, BasicBlock, Location};
use smallvec::SmallVec;

use crate::fmt::DebugWithContext;

rustc_index::newtype_index! {
    #[debug_format = "t({})"]
    pub struct Task {}
}

impl<C> DebugWithContext<C> for Task {}

rustc_index::newtype_index! {
    #[debug_format = "sp({})"]
    pub struct Spindle {}
}

/// A temporary representation of the data associated with a task.
/// See [TaskData] for a different representation which simplifies
/// some operations and rules out some invalid states.
struct TaskDataBuilder {
    /// The spindles in this task.
    spindles: SmallVec<[Spindle; 2]>,
    /// The parent of this task. None if this task is the root task.
    parent: Option<Task>,
    /// The children of this task.
    children: SmallVec<[Task; 2]>,
    /// The [Location] where this task reattaches to the continuation of the spawning detach.
    /// None if this task is the root task.
    last_location: Option<Location>,
}

#[derive(Debug)]
enum InvalidTaskData {
    MissingLastLocation,
    MissingParent,
}

impl TaskDataBuilder {
    /// Create a new [TaskDataBuilder] which is the root of the task tree and has no parent.
    fn root() -> Self {
        Self {
            spindles: SmallVec::new(),
            parent: None,
            children: SmallVec::new(),
            last_location: None,
        }
    }

    /// Create a new task in `tasks` which is a child of `parent` and return the child task.
    fn new_child(tasks: &mut IndexVec<Task, TaskDataBuilder>, parent: Task) -> Task {
        let child_data = TaskDataBuilder {
            spindles: SmallVec::new(),
            parent: Some(parent),
            children: SmallVec::new(),
            last_location: None,
        };
        let child = tasks.push(child_data);
        let parent_data = &mut tasks[parent];
        parent_data.children.push(child);
        child
    }

    fn build(self, num_tasks: usize, num_spindles: usize) -> Result<TaskData, InvalidTaskData> {
        let kind = match (self.parent, self.last_location) {
            (None, None) => Ok(TaskKind::Root),
            (Some(parent), Some(last_location)) => Ok(TaskKind::Child { parent, last_location }),
            (None, _) => Err(InvalidTaskData::MissingParent),
            (_, None) => Err(InvalidTaskData::MissingLastLocation),
        }?;

        let mut children = BitSet::new_empty(num_tasks);
        for child in self.children {
            children.insert(child);
        }

        let mut spindles = BitSet::new_empty(num_spindles);
        for spindle in self.spindles {
            spindles.insert(spindle);
        }
        Ok(TaskData { spindles, children, kind })
    }
}

/// Whether a task is the root task of the function or a descendant of the root task.
pub enum TaskKind {
    Root,
    Child { parent: Task, last_location: Location },
}

impl TaskKind {
    /// Finds the parent of this task, returning None if it doesn't exist.
    pub fn parent(&self) -> Option<Task> {
        if let Self::Child { parent, .. } = self { Some(*parent) } else { None }
    }

    /// Finds the last location of this task, returning None if it doesn't exist.
    pub fn last_location(&self) -> Option<Location> {
        if let Self::Child { last_location, .. } = self { Some(*last_location) } else { None }
    }
}

/// The data associated with a task, including which spindles compose it and information
/// about the relationship of this task to other tasks.
pub struct TaskData {
    /// The spindles in this task.
    pub spindles: BitSet<Spindle>,
    /// The children of this task.
    pub children: BitSet<Task>,
    /// Whether this is a root or child task.
    pub kind: TaskKind,
}

#[derive(Copy, Clone, Debug)]
enum SpindleKind {
    Normal,
    Phi,
}

impl SpindleKind {
    fn is_phi(&self) -> bool {
        if let SpindleKind::Phi = self { true } else { false }
    }
}

#[derive(Copy, Clone)]
struct SpindleDataBuilder {
    task: Task,
    entry: BasicBlock,
    kind: SpindleKind,
}

/// The data associated with a spindle, including which basic blocks it contains, the entry,
/// and which task the spindle belongs to.
#[derive(Debug)]
pub struct SpindleData {
    task: Task,
    entry: BasicBlock,
    #[allow(dead_code)]
    kind: SpindleKind,
    blocks: SmallVec<[BasicBlock; 2]>,
}

impl From<SpindleDataBuilder> for SpindleData {
    fn from(SpindleDataBuilder { task, entry, kind }: SpindleDataBuilder) -> Self {
        Self { task, entry, kind, blocks: SmallVec::new() }
    }
}

fn cleanup_blocks(body: &mir::Body<'_>) -> BitSet<BasicBlock> {
    let mut cleanup_blocks = BitSet::new_empty(body.basic_blocks.len());
    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        if bb_data.is_cleanup {
            cleanup_blocks.insert(bb);
        }
    }
    cleanup_blocks
}

/// Compute the blocks reachable from blocks labeled as cleanup.
///
/// We expect that all basic blocks b in the returned subgraph U
/// are either cleanup blocks or b.predecessors() is a subset of the nodes of U.
fn unwind_subgraph(body: &mir::Body<'_>) -> BitSet<BasicBlock> {
    let mut queue = WorkQueue::with_none(body.basic_blocks.len());
    queue.extend(
        body.basic_blocks
            .iter_enumerated()
            .filter_map(|(bb, bb_data)| bb_data.is_cleanup.then(|| bb)),
    );
    let mut subgraph = BitSet::new_empty(body.basic_blocks.len());

    // Do a breadth-first search to find all blocks reachable from blocks labeled as cleanup.
    while let Some(block) = queue.pop() {
        subgraph.insert(block);
        queue.extend(body.basic_blocks[block].terminator().successors());
    }

    // Check the reachability condition.
    let predecessors = body.basic_blocks.predecessors();
    for block in subgraph.iter().filter(|block| !body.basic_blocks[*block].is_cleanup) {
        // We now need to know that all predecessors of this block are in the subgraph.
        assert!(predecessors[block].iter().all(|pred| subgraph.contains(*pred)));
    }
    subgraph
}

/// A temporary representation of the Tapir tasks and spindles in a function body.
/// See [TaskInfo] for the finalized representation, stripped of associated state
/// which is only used during construction.
struct TaskInfoBuilder<'body, 'tcx> {
    body: &'body mir::Body<'tcx>,
    tasks: IndexVec<Task, TaskDataBuilder>,
    spindles: IndexVec<Spindle, SpindleDataBuilder>,
    block_tasks: FxHashMap<BasicBlock, Task>,
    block_spindles: FxHashMap<BasicBlock, Spindle>,
    unwind_subgraph: BitSet<BasicBlock>,
    cleanup_blocks: BitSet<BasicBlock>,
}

/// [TaskInfo] represents information about a function body's Tapir tasks and spindles
/// to enable analysis of which tasks are running concurrently with a given basic block.
pub struct TaskInfo {
    /// Pool of tasks, including associated data.
    tasks: IndexVec<Task, TaskData>,
    /// Pool of spindles, including associated data.
    spindles: IndexVec<Spindle, SpindleData>,
    /// Mapping from `BasicBlock` to the `Spindle` containing it, or None if no such `BasicBlock` exists.
    block_spindles: IndexVec<BasicBlock, Option<Spindle>>,
}

impl<'body, 'tcx> TaskInfoBuilder<'body, 'tcx> {
    /// Find the task associated with `block`, panicking if there is no such task.
    fn expect_task(&self, block: BasicBlock) -> Task {
        *self.block_tasks.get(&block).expect("expected block to have task!")
    }

    /// Find the parent task of `task`, panicking if `task` is an invalid index
    /// or the task has no parent.
    fn expect_parent_task(&self, task: Task) -> Task {
        self.tasks[task].parent.expect("expected task to have parent!")
    }

    /// Label `block` with `spindle` if it's not already labeled, expecting
    /// the existing spindle to be a phi spindle if it is.
    fn label_spindle_if_not_labeled(&mut self, block: BasicBlock, spindle: Spindle) {
        self.block_spindles
            .entry(block)
            .and_modify(|existing| assert!(self.spindles[*existing].kind.is_phi()))
            .or_insert(spindle);
    }

    /// Associate a new phi spindle in `task` with `block`.
    /// Panics if `block` is already associated with a spindle.
    fn associate_phi_spindle(&mut self, block: BasicBlock, task: Task) {
        self.block_spindles
            .entry(block)
            .and_modify(|spindle| {
                panic!(
                    "expected block to not have spindle associated with it already but found {:?}!",
                    spindle
                )
            })
            .or_insert_with(|| {
                self.spindles.push(SpindleDataBuilder {
                    task,
                    entry: block,
                    kind: SpindleKind::Phi,
                })
            });
    }

    /// Associate a new normal spindle with `block`, no-op if
    /// `block` is already associated with a phi spindle.
    /// Panics if `block` is already associated with a non-phi spindle.
    fn associate_new_spindle(&mut self, block: BasicBlock) {
        let task = self.expect_task(block);
        self.block_spindles
            .entry(block)
            .and_modify(|spindle| {
                assert!(self.spindles[*spindle].kind.is_phi());
            })
            .or_insert_with(|| {
                self.spindles.push(SpindleDataBuilder {
                    task,
                    entry: block,
                    kind: SpindleKind::Normal,
                })
            });
    }

    /// Label `block` with `task`.
    fn label_block_task(&mut self, block: BasicBlock, task: Task) {
        self.block_tasks.insert_same(block, task);
    }

    /// Modify this [TaskInfo] by recording a `Detach` where the spawned task is `spawned_task`,
    /// and the continuation is `continuation`.
    /// Precondition: tasks exist for spawned_task and continuation.
    fn spindle_detach_to(&mut self, spawned_task: BasicBlock, continuation: BasicBlock) {
        // We assume that the task state has already been updated.
        self.associate_new_spindle(spawned_task);
        self.associate_new_spindle(continuation);
    }

    /// Modify this [TaskInfo] by recording a `Reattach` where the continuation is `continuation`.
    /// Additionally record this reattach as terminating at `location`.
    fn spindle_reattach_to(&mut self, _location: Location, _continuation: BasicBlock) {
        // We don't have to do anything about the spindle state.
        // The last location was already initialized too.
    }

    /// Modify this [TaskInfo] by recording a `Sync` where the target is `target`.
    fn spindle_sync_to(&mut self, target: BasicBlock) {
        // Make a new spindle if one doesn't already exist.
        // We sometimes need a phi spindle?
        self.associate_new_spindle(target);
    }

    /// Modify this [TaskInfo] by recording a `SwitchInt` where the targets are given by `targets`.
    fn spindle_switch_int_to(&mut self, targets: impl Iterator<Item = BasicBlock>) {
        targets.for_each(|t| {
            self.associate_new_spindle(t);
        });
    }

    fn assign_tasks(body: &'body mir::Body<'tcx>) -> Self {
        let mut builder = Self {
            body,
            tasks: IndexVec::new(),
            spindles: IndexVec::new(),
            block_tasks: FxHashMap::default(),
            block_spindles: FxHashMap::default(),
            unwind_subgraph: unwind_subgraph(body),
            cleanup_blocks: cleanup_blocks(body),
        };

        for (block, block_data) in mir::traversal::reverse_postorder(body) {
            if builder.unwind_subgraph.contains(block) {
                continue;
            }

            let block_tasks_len = builder.block_tasks.len();
            let current_task = *builder.block_tasks.entry(block).or_insert_with(|| {
                assert!(
                    block_tasks_len == 0,
                    "expected the first task to be the only orphan task! block_tasks_len = {}",
                    block_tasks_len
                );

                builder.tasks.push(TaskDataBuilder::root())
            });

            let location = Location { block, statement_index: block_data.statements.len() };
            let terminator = block_data.terminator();
            match &terminator.kind {
                mir::TerminatorKind::Detach { spawned_task, continuation } => {
                    // Add a new task for the spawned task.
                    let new_task = TaskDataBuilder::new_child(&mut builder.tasks, current_task);
                    builder.label_block_task(*spawned_task, new_task);
                    builder.label_block_task(*continuation, current_task);
                }

                mir::TerminatorKind::Reattach { continuation } => {
                    let parent = builder.expect_parent_task(current_task);
                    // Traversal order means that the continuation should already have been
                    // labeled.
                    let continuation_task = builder.expect_task(*continuation);
                    assert_eq!(continuation_task, parent);

                    if let Some(last_location) = builder.tasks[current_task].last_location {
                        assert_eq!(
                            last_location, location,
                            "expected last location to be consistent with provided location!"
                        );
                    } else {
                        builder.tasks[current_task].last_location = Some(location);
                    }
                }

                _ => {
                    terminator.successors().for_each(|t| {
                        if !builder.cleanup_blocks.contains(t) {
                            // Same task.
                            builder.label_block_task(t, current_task);
                        }
                    })
                }
            }
        }

        builder
    }

    fn assign_phis_speculatively(&mut self) -> &mut Self {
        self.body.basic_blocks.predecessors().iter_enumerated().for_each(
            |(block, predecessors)| {
                if predecessors.len() >= 2 && !self.unwind_subgraph.contains(block) {
                    let task = self.expect_task(block);
                    self.associate_phi_spindle(block, task);
                }
            },
        );
        self
    }

    fn assign_normal_spindles(&mut self) -> &mut Self {
        // Iterate over the blocks of body in reverse post-order.
        for (block, block_data) in mir::traversal::reverse_postorder(self.body) {
            if self.unwind_subgraph.contains(block) {
                continue;
            }

            // We expect this to only happen once. Add an assertion at some point.
            let current_task = *self
                .block_tasks
                .entry(block)
                .or_insert_with(|| self.tasks.push(TaskDataBuilder::root()));

            // We also expect this to only happen once.
            let current_spindle = *self.block_spindles.entry(block).or_insert_with(|| {
                self.spindles.push(SpindleDataBuilder {
                    task: current_task,
                    entry: block,
                    kind: SpindleKind::Normal,
                })
            });

            let location = Location { block, statement_index: block_data.statements.len() };
            let terminator = block_data.terminator();
            match &terminator.kind {
                mir::TerminatorKind::Detach { spawned_task, continuation } => {
                    self.spindle_detach_to(*spawned_task, *continuation);
                }

                mir::TerminatorKind::Reattach { continuation } => {
                    self.spindle_reattach_to(location, *continuation);
                }

                mir::TerminatorKind::Sync { target } => {
                    self.spindle_sync_to(*target);
                }

                mir::TerminatorKind::SwitchInt { discr: _, targets } => {
                    self.spindle_switch_int_to(targets.all_targets().iter().copied());
                }

                _ => {
                    terminator.successors().for_each(|t| {
                        if !self.cleanup_blocks.contains(t) {
                            // Same spindle.
                            self.label_spindle_if_not_labeled(t, current_spindle);
                        }
                    })
                }
            }
        }
        self
    }

    fn despeculate_phi_spindles(&mut self) -> BitSet<Spindle> {
        fn has_switch_int_predecessor(
            builder: &TaskInfoBuilder<'_, '_>,
            block: BasicBlock,
            predecessors: &IndexSlice<BasicBlock, SmallVec<[BasicBlock; 4]>>,
        ) -> bool {
            predecessors[block].iter().any(|pred| {
                matches!(
                    builder.body.basic_blocks[*pred].terminator().kind,
                    mir::TerminatorKind::SwitchInt { .. }
                )
            })
        }

        struct RemapSpindle {
            from: Spindle,
            to: Spindle,
        }

        // Query instability is fine here since we iterate over speculative_phis, but this function
        // is only called as a subroutine and is called until it no longer returns true.
        // R is the set of redundant speculative phi spindles (a subset of speculative_phis).
        // An application is remapping a redundant speculative phi spindle to its predecessors' spindle.
        // For the order of iteration over speculative_phis to matter, there must be some redundant speculative phi
        // that cannot be discovered from a particular order of applications of all replacements of spindles in R.
        // (If this did not exist, then trivially all speculative phis are discovered by any order of applications.)
        // However, all orders of application of R end in an equivalent state since they are each non-interfering:
        // spindles are disjoint! This means that any discovered spindles must be discoverable from any order of
        // application of R since an additional application can never make a redundant speculative phi non-redundant.
        // The set of discovered redundant speculative phis monotonically increases (as long as one of those spindles
        // is not applied). Therefore, the ordering of application cannot matter, since as long as all initial
        // spindles in R are applied, the same set of redundant speculative phis will be discovered.
        #[allow(rustc::potential_query_instability)]
        fn find_redundant_speculative_phi(
            builder: &TaskInfoBuilder<'_, '_>,
            speculative_phis: &FxHashSet<Spindle>,
            predecessors: &IndexSlice<BasicBlock, SmallVec<[BasicBlock; 4]>>,
        ) -> Option<RemapSpindle> {
            speculative_phis.iter().copied().find_map(|spindle| {
                let entry = builder.spindles[spindle].entry;
                let Some((first_pred, rest_preds)) = predecessors[entry].split_first() else {
                    return None;
                };

                let first_pred_spindle = builder.block_spindles[first_pred];
                // If all predecessors have the same spindle as the first predecessor's spindle,
                // we know that all predecessors are part of the same spindle -> can replace with
                // that spindle.
                rest_preds
                    .iter()
                    .all(|pred| builder.block_spindles[pred] == first_pred_spindle)
                    .then(|| RemapSpindle { from: spindle, to: first_pred_spindle })
            })
        }

        // We don't care about the ordering of the blocks in each vector contained in
        // spindle_blocks (only used for inserting into block_spindles later, which is
        // a map from block to spindle and doesn't care about iteration order).
        #[allow(rustc::potential_query_instability)]
        fn build_spindle_blocks(
            spindles: &IndexSlice<Spindle, SpindleDataBuilder>,
            block_spindles: &FxHashMap<BasicBlock, Spindle>,
        ) -> IndexVec<Spindle, Vec<BasicBlock>> {
            let mut spindle_blocks = IndexVec::from_elem(vec![], &spindles);
            for (block, spindle) in block_spindles {
                spindle_blocks[*spindle].push(*block);
            }
            spindle_blocks
        }

        let predecessors = self.body.basic_blocks.predecessors();

        let mut speculative_phis: FxHashSet<_> = self
            .spindles
            .iter_enumerated()
            .filter(|(_spindle, spindle_data)| {
                spindle_data.kind.is_phi()
                    && !has_switch_int_predecessor(self, spindle_data.entry, predecessors)
            })
            .map(|(spindle, _spindle_data)| spindle)
            .collect();

        // First, collect a set of all phi spindles. These spindles may have predecessors which are
        // actually all the same and no SwitchInt predecessor, in which case we don't need a phi.

        let mut spindle_blocks = build_spindle_blocks(&self.spindles, &self.block_spindles);
        let mut removed_spindles = BitSet::new_empty(self.spindles.len());

        // Now we need to find the speculative phi nodes that can actually be converted. This means
        // we need to find a speculative phi node that has predecessors which are all in the same spindle.
        // We also already checked that it didn't have a SwitchInt immediate predecessor.
        while let Some(RemapSpindle { from, to }) =
            find_redundant_speculative_phi(self, &speculative_phis, predecessors)
        {
            // Reassign all blocks in from to be in to instead.
            let (from_blocks, to_blocks) = spindle_blocks.pick2_mut(from, to);
            to_blocks.reserve(from_blocks.len());
            from_blocks.drain(..).for_each(|block| {
                self.block_spindles.insert(block, to);
                to_blocks.push(block);
            });
            let from_was_present = speculative_phis.remove(&from);
            assert!(from_was_present);
            let removed_spindles_did_not_contain_from = removed_spindles.insert(from);
            assert!(removed_spindles_did_not_contain_from);
        }

        // After the above loop ends, there should be no more redundant speculative phis.
        removed_spindles
    }

    fn remove_empty_spindles(&mut self, removed_spindles: &BitSet<Spindle>) -> &mut Self {
        // When we iterate over block_spindles, we always iterate over all of them, so iteration order can't
        // matter. We have no state dependent on which iterations have executed already.
        #[allow(rustc::potential_query_instability)]
        fn remap_spindles(
            block_spindles: &mut FxHashMap<BasicBlock, Spindle>,
            new_indices: &[isize],
        ) {
            block_spindles.values_mut().for_each(|spindle| {
                let new_index = new_indices[spindle.as_usize()];
                assert!(new_index >= 0);
                *spindle = Spindle::from_usize(new_index as usize);
            });
        }

        let new_indices: Vec<_> = self
            .spindles
            .indices()
            // This gives the numerical version of the bitvector so we can do math on it later.
            .map(|spindle| {
                let removed = if removed_spindles.contains(spindle) { 1 } else { 0 };
                (spindle, removed)
            })
            // This scan should give us an iterator that yields values like:
            // (for the second value of the tuple)
            // [0, 0, 1, 0, 0, 1, 1, 1] -> [0, 0, -1, -1, -1, -2, -3, -4]
            .scan(0isize, |acc, (original_spindle, removed)| {
                *acc -= removed;
                Some((original_spindle, *acc))
            })
            // Now we need to compute the actual indices:
            // [0, 0, -1, -1, -1, -2, -3, -4] -> [0, 1, 1, 2, 3, 3, 3, 3]
            // Note that we need isize because if the first element is removed,
            // we'll end up with negative values. We do expect that for any index
            // where removed_spindles is 0, the output of this iterator gives a
            // non-negative value.
            .map(|(original_spindle, offset)| (original_spindle.as_usize() as isize) + offset)
            .collect();
        let mut new_spindles: IndexVec<Spindle, SpindleDataBuilder> =
            IndexVec::with_capacity(self.spindles.len() - removed_spindles.domain_size());
        for (spindle, spindle_data) in self.spindles.drain_enumerated(..) {
            if !removed_spindles.contains(spindle) {
                new_spindles.push(spindle_data);
            }
        }
        remap_spindles(&mut self.block_spindles, &new_indices);
        self.spindles = new_spindles;
        self
    }

    /// Construct a [TaskInfoBuilder] from `body`.
    #[instrument(level = "debug", skip(body))]
    pub fn from_body(body: &'body mir::Body<'tcx>) -> Self {
        let mut builder = Self::assign_tasks(body);
        let removed_spindles =
            // Phase 2: speculative phi spindle assignment. Insert a phi spindle at any basic block
            // with more than 2 predecessors, and propagate the spindles in all non-branching control
            // flow cases. At branching control flow it's a no-op.
            builder.assign_phis_speculatively()
                // Phase 3: normal spindle insertion. From the entry block, insert spindles where unassigned
                // or for branching. If blocks are already labeled with phi spindles, don't change that label.
                .assign_normal_spindles()
                // Phase 4: phi spindle despeculation. For each phi spindle, if all predecessors of the entry block
                // are in the same spindle, reassign all blocks in the phi spindle to the normal spindle predecessor.
                // This should only be applied to phi spindles which are not immediately preceded by a SwitchInt,
                // since SwitchInt must create a new spindle for each target even if all predecessors to the basic block
                // are different spindles.
                .despeculate_phi_spindles();
        // Phase 5: garbage collection. Delete the spindles with no blocks in them and remap the spindle vector
        // and map atomically.
        builder.remove_empty_spindles(&removed_spindles);

        for (spindle, spindle_data) in builder.spindles.iter_enumerated() {
            builder.tasks[spindle_data.task].spindles.push(spindle);
        }

        builder
    }

    fn validate_spindle_bounds(task_info: &TaskInfo) {
        for spindle in task_info.block_spindles.iter().copied().filter_map(|spindle| spindle) {
            assert!(
                spindle.as_usize() < task_info.spindles.len(),
                "spindle = {:?} but # spindles = {}",
                spindle,
                task_info.spindles.len()
            );
        }
    }

    fn validate_parent_child_relationship(task_info: &TaskInfo, task: Task) {
        // All children of this task should have this task marked as a parent.
        let task_data = &task_info.tasks[task];
        for child_data in task_data.children.iter().map(|child| &task_info.tasks[child]) {
            assert_eq!(
                child_data.kind.parent(),
                Some(task),
                "expected child to have parent as task!"
            );
        }

        // This task's parent should contain this task as a child.
        if let Some(parent) = task_data.kind.parent() {
            let parent_data = &task_info.tasks[parent];
            assert!(parent_data.children.contains(task), "expected parent to have child as task!");
        }
    }

    fn validate_domain_sizes(task_info: &TaskInfo) {
        let (task, other_tasks) = task_info.tasks.split_first().expect("expected at least 1 task!");
        for other_task in other_tasks {
            assert_eq!(
                task.children.domain_size(),
                other_task.children.domain_size(),
                "expected consistent domain size between task children!"
            );
            assert_eq!(
                task.spindles.domain_size(),
                other_task.spindles.domain_size(),
                "expected consistent domain size between task spindles!"
            );
        }

        assert_eq!(task.children.domain_size(), task_info.tasks.len());
        assert_eq!(task.spindles.domain_size(), task_info.spindles.len());
    }

    #[allow(rustc::potential_query_instability)]
    // Iteration order doesn't actually matter here. The map has unique keys by definition
    // so inserting into block_spindles this way is order-independent.
    fn convert_block_spindles(
        block_spindles_map: &FxHashMap<BasicBlock, Spindle>,
        basic_block_count: usize,
    ) -> IndexVec<BasicBlock, Option<Spindle>> {
        let mut block_spindles = IndexVec::from_elem_n(None, basic_block_count);
        for (basic_block, spindle) in block_spindles_map {
            block_spindles[*basic_block] = Some(*spindle);
        }

        block_spindles
    }

    fn validate_unwind_subgraph_spindles(
        block_spindles: &IndexSlice<BasicBlock, Option<Spindle>>,
        unwind_subgraph: &BitSet<BasicBlock>,
    ) {
        for (block, spindle) in block_spindles.iter_enumerated() {
            assert!(
                spindle.is_some() || unwind_subgraph.contains(block),
                "only blocks in the unwind subgraph should have no spindle!"
            );
        }

        for block in unwind_subgraph.iter() {
            assert!(
                block_spindles[block].is_none(),
                "all blocks in unwind subgraph should have no spindle!"
            );
        }
    }

    fn convert_spindles(
        spindles: &IndexSlice<Spindle, SpindleDataBuilder>,
        block_spindles: &IndexSlice<BasicBlock, Option<Spindle>>,
    ) -> IndexVec<Spindle, SpindleData> {
        let mut new_spindles = IndexVec::from_fn_n(
            |i|
                // We'll add the entry block now and initialize blocks later.
                SpindleData::from(spindles[i]),
            spindles.len(),
        );
        for (block, spindle) in block_spindles
            .iter_enumerated()
            .filter_map(|(block, spindle)| spindle.map(|spindle| (block, spindle)))
        {
            new_spindles[spindle].blocks.push(block);
        }
        new_spindles
    }

    fn validate_spindle_connected(body: &'body mir::Body<'tcx>, spindle: &SpindleData) {
        let mut queue = WorkQueue::with_none(body.basic_blocks.len());
        let mut seen = BitSet::new_empty(body.basic_blocks.len());
        let spindle_blocks = {
            let mut spindle_blocks = BitSet::new_empty(body.basic_blocks.len());
            for block in &spindle.blocks {
                spindle_blocks.insert(*block);
            }
            spindle_blocks
        };

        queue.insert(spindle.entry);
        while let Some(block) = queue.pop() {
            seen.insert(block);
            // Now we want to add all edges from this block that are part of the spindle.
            for target in body.basic_blocks[block].terminator().successors() {
                if spindle_blocks.contains(target) && !seen.contains(target) {
                    queue.insert(target);
                }
            }
        }

        // Now, the seen set should exactly match the spindle blocks.
        assert_eq!(
            spindle_blocks, seen,
            "expected blocks in spindle to be same as blocks seen by traversing spindle!"
        );
    }

    /// Validate this [TaskInfoBuilder] and construct a [TaskInfo] from it.
    #[instrument(level = "debug", skip(self))]
    pub fn build(self, basic_block_count: usize) -> TaskInfo {
        let Self {
            body,
            tasks,
            spindles,
            block_tasks: _,
            block_spindles,
            unwind_subgraph,
            cleanup_blocks: _,
        } = self;

        let num_tasks = tasks.len();
        let tasks: IndexVec<Task, TaskData> = tasks
            .into_iter()
            .map(|task_data| {
                task_data
                    .build(num_tasks, spindles.len())
                    .expect("expected task data invariants to be upheld!")
            })
            .collect();

        let block_spindles =
            TaskInfoBuilder::convert_block_spindles(&block_spindles, basic_block_count);

        let spindles = TaskInfoBuilder::convert_spindles(&spindles, &block_spindles);

        let task_info = TaskInfo { tasks, spindles, block_spindles };
        // Domain sizes should agree with IndexVec sizes.
        TaskInfoBuilder::validate_domain_sizes(&task_info);

        // All hashmap values should also be in bounds.
        TaskInfoBuilder::validate_spindle_bounds(&task_info);

        // Parent-child relationships should agree within tasks.
        for task in task_info.tasks.indices() {
            TaskInfoBuilder::validate_parent_child_relationship(&task_info, task);
        }

        // Every block should have some spindle unless it's in the unwind subgraph,
        // and all blocks in the unwind subgraph should have no spindle.
        TaskInfoBuilder::validate_unwind_subgraph_spindles(
            &task_info.block_spindles,
            &unwind_subgraph,
        );

        // Check that all spindles are connected.
        for spindle in &task_info.spindles {
            TaskInfoBuilder::validate_spindle_connected(body, spindle);
        }

        task_info
    }
}

impl TaskInfo {
    /// Find the task associated with `block`, panicking if there is no such task.
    pub fn expect_task(&self, block: BasicBlock) -> Task {
        let spindle = self.expect_spindle(block);
        self.spindles[spindle].task
    }

    /// Find the [Location] where `task` reattaches to its parent, panicking if
    /// `task` is an invalid index or the task is the root task.
    pub fn expect_last_location(&self, task: Task) -> Location {
        self.tasks[task]
            .kind
            .last_location()
            .expect("expected task to have last location, but was root!")
    }

    /// Find the spindle associated with `block`, panicking if there is no such spindle.
    pub fn expect_spindle(&self, block: BasicBlock) -> Spindle {
        self.block_spindles
            .get(block)
            .copied()
            .flatten()
            .expect("expected spindle to be defined for basic block!")
    }

    /// Find the descendants of `task`.
    pub fn descendants(&self, task: Task) -> Box<dyn Iterator<Item = Task> + '_> {
        let task_data = &self.tasks[task];
        Box::new(
            task_data.children.iter().flat_map(|t| std::iter::once(t).chain(self.descendants(t))),
        )
    }

    /// Build a [TaskInfo] from the given [mir::Body].
    pub fn from_body<'a, 'tcx>(body: &'a mir::Body<'tcx>) -> Self {
        TaskInfoBuilder::from_body(body).build(body.basic_blocks.len())
    }

    pub fn num_tasks(&self) -> usize {
        self.tasks.len()
    }
}

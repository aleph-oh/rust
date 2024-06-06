use std::collections::hash_map::Entry;

use rustc_data_structures::work_queue::WorkQueue;
use rustc_data_structures::{fx::FxHashMap, sync::HashMapExt};
use rustc_index::IndexSlice;
use rustc_index::{bit_set::BitSet, IndexVec};
use rustc_middle::mir::{self, BasicBlock, Location};
use smallvec::SmallVec;

rustc_index::newtype_index! {
    #[debug_format = "t({})"]
    pub struct Task {}
}

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

pub struct TaskData {
    /// The spindles in this task.
    pub spindles: BitSet<Spindle>,
    /// The children of this task.
    pub children: BitSet<Task>,
    /// Whether this is a root or child task.
    pub kind: TaskKind,
}

struct SpindleDataBuilder {
    task: Task,
    entry: BasicBlock,
}

struct SpindleData {
    task: Task,
    entry: BasicBlock,
    blocks: SmallVec<[BasicBlock; 2]>,
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

struct TaskInfoBuilder<'body, 'tcx> {
    body: &'body mir::Body<'tcx>,
    tasks: IndexVec<Task, TaskDataBuilder>,
    spindles: IndexVec<Spindle, SpindleDataBuilder>,
    block_tasks: FxHashMap<BasicBlock, Task>,
    block_spindles: FxHashMap<BasicBlock, Spindle>,
    unwind_subgraph: BitSet<BasicBlock>,
    cleanup_blocks: BitSet<BasicBlock>,
}

pub struct TaskInfo {
    /// Pool of tasks, including associated data.
    tasks: IndexVec<Task, TaskData>,
    /// Pool of spindles, including associated data.
    spindles: IndexVec<Spindle, SpindleData>,
    /// Mapping from `BasicBlock` to the `Spindle` containing it, or None if no such `BasicBlock` exists.
    block_spindles: IndexVec<BasicBlock, Option<Spindle>>,
}

impl<'body, 'tcx> TaskInfoBuilder<'body, 'tcx> {
    /// Find the parent task of `task`, panicking if `task` is an invalid index
    /// or the task has no parent.
    pub fn expect_parent_task(&self, task: Task) -> Task {
        self.tasks[task].parent.expect("expected task to have parent!")
    }

    /// Associate a new spindle in `task` with `block`.
    fn associate_new_spindle(&mut self, block: BasicBlock, task: Task) {
        let spindle = self.spindles.push(SpindleDataBuilder { task, entry: block });
        self.block_spindles.insert_same(block, spindle);
    }

    /// Label `block` with `task`.
    fn label_block_task(&mut self, block: BasicBlock, task: Task) {
        self.block_tasks.insert_same(block, task);
    }

    /// Label `block` with `spindle`.
    fn label_block_spindle(&mut self, block: BasicBlock, spindle: Spindle) {
        self.block_spindles.insert_same(block, spindle);
    }

    /// Modify this [TaskInfo] by recording a `Detach` where the current task is `current_task`,
    /// the spawned task is `spawned_task`, and the continuation is `continuation`.
    fn detach_to(
        &mut self,
        current_task: Task,
        spawned_task: BasicBlock,
        continuation: BasicBlock,
    ) {
        // First, update our task state.
        let new_task = TaskDataBuilder::new_child(&mut self.tasks, current_task);
        self.label_block_task(spawned_task, new_task);
        self.label_block_task(continuation, current_task);

        // Next, add spindles for both the spawned task and the continuation.
        self.associate_new_spindle(spawned_task, new_task);
        self.associate_new_spindle(continuation, current_task);
    }

    /// Modify this [TaskInfo] by recording a `Reattach` where the current task is `current_task`
    /// and the continuation is `continuation`. Additionally record this reattach as terminating
    /// at `location`.
    fn reattach_to(&mut self, location: Location, current_task: Task, continuation: BasicBlock) {
        // The task should be whatever task the continuation already had. Make sure
        // this agrees with the current task's parent is.
        let parent = self.expect_parent_task(current_task);
        self.label_block_task(continuation, parent);
        // We don't need to change anything about the spindle state, and it should
        // already have been assigned from the handling of detach.

        // We also associate the location as the last location of the task.
        // If it's already set, make sure it agrees.
        if let Some(last_location) = self.tasks[current_task].last_location {
            assert_eq!(
                last_location, location,
                "expected last location to be consistent with provided location!"
            );
        } else {
            self.tasks[current_task].last_location = Some(location);
        }
    }

    /// Modify this [TaskInfo] by recording a `Sync` where the current task is `current_task`
    /// and the target is `target`.
    fn sync_to(&mut self, current_task: Task, target: BasicBlock) {
        // Make a new spindle if one doesn't already exist.
        // We sometimes need a phi spindle?
        if let Entry::Vacant(e) = self.block_spindles.entry(target) {
            let new_spindle =
                self.spindles.push(SpindleDataBuilder { task: current_task, entry: target });
            e.insert(new_spindle);
        }
        // We don't have to do anything for tasks. After a sync, it's still the same task.
        self.label_block_task(target, current_task);
    }

    /// Modify this [TaskInfo] by recording a `SwitchInt` where the current task is `current_task`
    /// and the targets are given by `targets`.
    fn switch_int_to(&mut self, current_task: Task, targets: impl Iterator<Item = BasicBlock>) {
        targets.for_each(|t| {
            self.associate_new_spindle(t, current_task);
            // Associate the current task with each of the jump targets.
            self.label_block_task(t, current_task);
        });
    }

    /// Construct a [TaskInfoBuilder] from `body`.
    pub fn from_body(body: &'body mir::Body<'tcx>) -> Self {
        let mut builder = Self {
            body,
            tasks: IndexVec::new(),
            spindles: IndexVec::new(),
            block_tasks: FxHashMap::default(),
            block_spindles: FxHashMap::default(),
            unwind_subgraph: unwind_subgraph(body),
            cleanup_blocks: cleanup_blocks(body),
        };

        for (block, block_data) in mir::traversal::preorder(body) {
            if builder.unwind_subgraph.contains(block) {
                continue;
            }

            let block_tasks_empty = builder.block_tasks.is_empty();
            let current_task = *builder.block_tasks.entry(block).or_insert_with(|| {
                assert!(block_tasks_empty, "expected the first task to be the only orphan task!");

                builder.tasks.push(TaskDataBuilder::root())
            });

            let block_spindles_empty = builder.block_spindles.is_empty();
            let current_spindle = *builder.block_spindles.entry(block).or_insert_with(|| {
                assert!(
                    block_spindles_empty,
                    "expected the first spindle to be the only non-associated spindle!"
                );
                builder.spindles.push(SpindleDataBuilder { task: current_task, entry: block })
            });

            let location = Location { block, statement_index: block_data.statements.len() };
            let terminator = block_data.terminator();
            match &terminator.kind {
                mir::TerminatorKind::Detach { spawned_task, continuation } => {
                    builder.detach_to(current_task, *spawned_task, *continuation);
                }

                mir::TerminatorKind::Reattach { continuation } => {
                    builder.reattach_to(location, current_task, *continuation);
                }

                mir::TerminatorKind::Sync { target } => {
                    builder.sync_to(current_task, *target);
                }

                mir::TerminatorKind::SwitchInt { discr: _, targets } => {
                    builder.switch_int_to(current_task, targets.all_targets().iter().copied());
                }

                _ => {
                    terminator.successors().for_each(|t| {
                        if !builder.cleanup_blocks.contains(t) {
                            // Same spindle, same task.
                            builder.label_block_task(block, current_task);
                            builder.label_block_spindle(block, current_spindle);
                        }
                    })
                }
            }
        }

        for (spindle, spindle_data) in builder.spindles.iter_enumerated() {
            builder.tasks[spindle_data.task].spindles.push(spindle);
        }

        builder
    }

    fn validate_spindle_bounds(task_info: &TaskInfo) {
        for spindle in task_info.block_spindles.indices() {
            assert!(spindle.as_usize() < task_info.spindles.len());
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
            |i| {
                let SpindleDataBuilder { task, entry } = &spindles[i];
                // We'll add the entry block to blocks later.
                SpindleData { task: *task, entry: *entry, blocks: SmallVec::new() }
            },
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
        assert_eq!(spindle_blocks, seen);
    }

    //  Convert the [TaskInfoBuilder] into a [TaskInfo].
    pub fn build(self, basic_block_count: usize) -> TaskInfo {
        let Self {
            body,
            tasks,
            spindles,
            block_tasks: _,
            block_spindles,
            unwind_subgraph,
            cleanup_blocks,
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

    /// Find the parent task of `task`, panicking if `task` is an invalid index
    /// or the task has no parent.
    pub fn expect_parent_task(&self, task: Task) -> Task {
        self.tasks[task].kind.parent().expect("expected task to have parent, but was root!")
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
        Box::new(task_data.children.iter().flat_map(|t| self.descendants(t)))
    }

    // Should be fine to only sync children in terms of dataflow state to restore?
    // So maybe we don't need descendants?
    pub fn children(&self, task: Task) -> impl Iterator<Item = Task> + '_ {
        self.tasks[task].children.iter()
    }

    pub fn from_body<'a, 'tcx>(body: &'a mir::Body<'tcx>) -> Self {
        TaskInfoBuilder::from_body(body).build(body.basic_blocks.len())
    }
}

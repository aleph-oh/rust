use std::collections::hash_map::Entry;

use rustc_data_structures::work_queue::WorkQueue;
use rustc_data_structures::{fx::FxHashMap, sync::HashMapExt};
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

struct TaskData {
    pub spindles: SmallVec<[Spindle; 2]>,
    pub parent: Option<Task>,
    pub children: SmallVec<[Task; 2]>,
    pub last_location: Option<Location>,
}

impl TaskData {
    /// Create a new [TaskData] which is the root of the task tree and has no parent.
    fn root() -> Self {
        Self {
            spindles: SmallVec::new(),
            parent: None,
            children: SmallVec::new(),
            last_location: None,
        }
    }

    /// Create a new task in `tasks` which is a child of `parent` and return the child task.
    fn new_child(tasks: &mut IndexVec<Task, TaskData>, parent: Task) -> Task {
        let child_data = TaskData {
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
}

// Empty for now, we'll add associated data to this as we need it.
struct SpindleData {
    task: Task,
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

pub struct TaskInfo {
    tasks: IndexVec<Task, TaskData>,
    spindles: IndexVec<Spindle, SpindleData>,
    block_tasks: FxHashMap<BasicBlock, Task>,
    block_spindles: FxHashMap<BasicBlock, Spindle>,
}

impl TaskInfo {
    /// Find the task associated with `block`, panicking if there is no such task.
    pub fn expect_task(&self, block: BasicBlock) -> Task {
        *self.block_tasks.get(&block).expect("expected task to be defined for basic block!")
    }

    /// Find the parent task of `task`, panicking if `task` is an invalid index
    /// or the task has no parent.
    pub fn expect_parent_task(&self, task: Task) -> Task {
        self.tasks[task].parent.expect("expected task to have parent!")
    }

    /// Find the spindle associated with `block`, panicking if there is no such spindle.
    pub fn expect_spindle(&self, block: BasicBlock) -> Spindle {
        *self.block_spindles.get(&block).expect("expected spindle to be defined for basic block!")
    }

    /// Find the descendants of `task`.
    pub fn descendants(&self, task: Task) -> Box<dyn Iterator<Item = Task> + '_> {
        let task_data = &self.tasks[task];
        Box::new(task_data.children.iter().flat_map(|t| self.descendants(*t)))
    }

    /// Associate a new spindle in `task` with `block`.
    fn associate_new_spindle(&mut self, block: BasicBlock, task: Task) {
        let spindle = self.spindles.push(SpindleData { task });
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
        let new_task = TaskData::new_child(&mut self.tasks, current_task);
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
            let new_spindle = self.spindles.push(SpindleData { task: current_task });
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

    /// Construct a [TaskInfo] from `body`.
    pub fn from_body<'a, 'tcx>(body: &'a mir::Body<'tcx>) -> Self {
        let mut task_info = Self {
            tasks: IndexVec::new(),
            spindles: IndexVec::new(),
            block_tasks: FxHashMap::default(),
            block_spindles: FxHashMap::default(),
        };

        let unwind_subgraph = unwind_subgraph(body);
        let cleanup_blocks = cleanup_blocks(body);

        for (block, block_data) in mir::traversal::preorder(body) {
            if unwind_subgraph.contains(block) {
                continue;
            }

            let block_tasks_empty = task_info.block_tasks.is_empty();
            let current_task = *task_info.block_tasks.entry(block).or_insert_with(|| {
                assert!(block_tasks_empty, "expected the first task to be the only orphan task!");

                task_info.tasks.push(TaskData::root())
            });

            let block_spindles_empty = task_info.block_spindles.is_empty();
            let current_spindle = *task_info.block_spindles.entry(block).or_insert_with(|| {
                assert!(
                    block_spindles_empty,
                    "expected the first spindle to be the only non-associated spindle!"
                );
                task_info.spindles.push(SpindleData { task: current_task })
            });

            let location = Location { block, statement_index: block_data.statements.len() };
            let terminator = block_data.terminator();
            match &terminator.kind {
                mir::TerminatorKind::Detach { spawned_task, continuation } => {
                    task_info.detach_to(current_task, *spawned_task, *continuation);
                }

                mir::TerminatorKind::Reattach { continuation } => {
                    task_info.reattach_to(location, current_task, *continuation);
                }

                mir::TerminatorKind::Sync { target } => {
                    task_info.sync_to(current_task, *target);
                }

                mir::TerminatorKind::SwitchInt { discr: _, targets } => {
                    task_info.switch_int_to(current_task, targets.all_targets().iter().copied());
                }

                _ => {
                    terminator.successors().for_each(|t| {
                        if !cleanup_blocks.contains(t) {
                            // Same spindle, same task.
                            task_info.label_block_task(block, current_task);
                            task_info.label_block_spindle(block, current_spindle);
                        }
                    })
                }
            }
        }

        for (spindle, spindle_data) in task_info.spindles.iter_enumerated() {
            task_info.tasks[spindle_data.task].spindles.push(spindle);
        }

        task_info
    }
}

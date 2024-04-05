use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::work_queue::WorkQueue;
use rustc_index::bit_set::BitSet;
use rustc_index::IndexVec;
use rustc_middle::mir::{self, BasicBlock, Location};

// We want a visitor that generates a tree of tasks. A task is a child of another task if it was detached from that task
// as the spawned task, while the continuation is part of the same task as the block it detached from. We can then label
// basic blocks with their task.
rustc_index::newtype_index! {
    #[debug_format = "t({})"]
    pub struct Task {}
}

struct TaskData {
    /// Represents the task which spawned this task. Is only None if this task is an orphan, i.e. the original task in the function.
    pub parent: Option<Task>,
    /// Represents all child tasks that may be spawned by this task.
    pub children: Vec<Task>,
    /// Represents all locations which this task might end at where control will not be returned to it.
    pub last_locations: Vec<Location>,
}

pub struct TaskTree {
    tasks: IndexVec<Task, TaskData>,
    basic_blocks: FxHashMap<BasicBlock, Task>,
    unwind_subgraph: BitSet<BasicBlock>,
    cleanup_blocks: BitSet<BasicBlock>,
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
    let mut cleanup_blocks = BitSet::new_empty(body.basic_blocks.len());

    // Do a breadth-first search to find all blocks reachable from blocks labeled as cleanup.
    while let Some(block) = queue.pop() {
        cleanup_blocks.insert(block);
        queue.extend(body.basic_blocks[block].terminator().successors());
    }

    // Check the reachability condition.
    let predecessors = body.basic_blocks.predecessors();
    for block in cleanup_blocks.iter().filter(|block| !body.basic_blocks[*block].is_cleanup) {
        // We now need to know that all predecessors of this block are in the subgraph.
        assert!(predecessors[block].iter().all(|pred| cleanup_blocks.contains(*pred)));
    }
    cleanup_blocks
}

impl TaskTree {
    /// Label the block as part of the given task, panicking if it's already mapped to a different task.
    ///
    /// This makes sense whenever the block might have been labeled with a task already, but you
    /// should always expect that task to be the same: no basic block should be part of two tasks.
    fn label_block(&mut self, block: BasicBlock, task: Task) {
        assert!(
            !self.unwind_subgraph.contains(block),
            "expected not to label block in unwind subgraph: unwind subgraph is {:?}, block is {:?}",
            self.unwind_subgraph,
            block
        );
        match self.basic_blocks.entry(block) {
            std::collections::hash_map::Entry::Occupied(other_task)
                if *other_task.get() != task =>
            {
                panic!(
                    "expected the task for this block to be the same as the task given: was {:?}, expected {:?}!",
                    *other_task.get(),
                    task
                )
            }
            // In all other cases, we know that it's safe to do this b/c either the mapping doesn't exist,
            // and or_insert will just do the insertion, or the mapping does exist and is the same,
            // so we don't care that the insertion won't happen.
            e => e.or_insert(task),
        };
    }

    /// Check invariants of the TaskTree.
    #[allow(rustc::potential_query_instability)]
    pub fn validate(&self) {
        // We're okay with using .values() here because order doesn't matter and we're intentionally trying to check our invariants,
        // so if we do see a failure it's not like the order we see a failure in really matters to the end user since it's an ICE anyways.
        self.basic_blocks.values().for_each(|task| {
            if let Some(task_data) = self.tasks.get(*task) {
                for last_location in &task_data.last_locations {
                    let last_block = last_location.block;
                    // We need the block with the corresponding last location to be part of the corresponding task.
                    let mapped_task = self
                        .basic_blocks
                        .get(&last_block)
                        .expect("expected last location's block to have a corresponding task!");
                    assert_eq!(mapped_task, task, "expected last_location's block to have the same task as the task it's a last location for!");
                }
            }
        });

        let number_of_orphan_tasks = self.tasks.iter().filter(|task| task.parent.is_none()).count();
        assert_eq!(
            number_of_orphan_tasks, 1,
            "expected exactly 1 orphan task since there should be 1 initially-unlabeled task but found {}!",
            number_of_orphan_tasks
        );
    }

    fn task(&self, block: BasicBlock) -> Option<Task> {
        self.basic_blocks.get(&block).copied()
    }

    /// Get the task for the given location, panicking if it doesn't exist.
    pub fn expect_task(&self, location: Location) -> Task {
        self.task(location.block).expect("expected block to have a task!")
    }

    /// Get the last locations of the children of this task, panicking if it doesn't exist.
    pub fn children_last_locations(&self, task: Task) -> impl Iterator<Item = Location> + '_ {
        self.children(task).flat_map(move |child| self.last_locations(child))
    }

    /// Get the children of this task, panicking if it doesn't exist.
    pub fn children(&self, task: Task) -> impl Iterator<Item = Task> + '_ {
        self.tasks[task].children.iter().copied()
    }

    /// Get the locations where this task may return control to the task its continuation belongs to, panicking if
    /// the task doesn't exist.
    pub fn last_locations(&self, task: Task) -> impl Iterator<Item = Location> + '_ {
        self.tasks[task].last_locations.iter().copied()
    }

    /// Modify this task tree by detaching from the current task, spawning a new task, and
    /// labeling the continuation block with the current task.
    fn detach_at(
        &mut self,
        current_task: Task,
        spawned_task: BasicBlock,
        continuation: BasicBlock,
    ) {
        self.label_block(continuation, current_task);
        let new_task = self.tasks.push(TaskData {
            parent: Some(current_task),
            children: vec![],
            last_locations: vec![],
        });
        self.tasks[current_task].children.push(new_task);
        self.label_block(spawned_task, new_task);
    }

    /// Modify this task tree by reattaching to the parent task of `current_task` at the given location.
    fn reattach_at(&mut self, location: Location, current_task: Task, continuation: BasicBlock) {
        let current_task_data = &mut self.tasks[current_task];

        // Reattach is the only way for the task to change to some other task in a way that
        // won't return control to the current task, so we want to add it as a "last location".
        current_task_data.last_locations.push(location);

        let parent =
            current_task_data.parent.expect("expected current task to have parent if reattaching!");
        // NOTE(jhilton): As long as reattach_at is called only in a preorder traversal, we should expect that
        // the block is labeled with the parent task already since the continuation should have
        // been visited before we looked at successors of the spawned task.
        self.label_block(continuation, parent);

        debug_assert!(
            self.tasks[parent].children.contains(&current_task),
            "the current task should be a child of the task being reattached to!"
        );
    }

    /// Modify this task tree by adding all blocks that the terminator can go to, to the current task.
    fn add_successors_to_current_task(
        &mut self,
        current_task: Task,
        terminator: &mir::Terminator<'_>,
    ) {
        terminator.successors().for_each(|target| {
            if !self.cleanup_blocks.contains(target) {
                self.label_block(target, current_task);
            }
        });
    }

    /// Create a TaskTree from a MIR body.
    pub fn from_body<'a, 'tcx>(body: &'a mir::Body<'tcx>) -> Self {
        // We use this instead of a visitor because we want to control the iteration order.
        // We need to know that all ancestors of a block are visited before the block itself.
        let mut task_tree = Self {
            tasks: IndexVec::new(),
            basic_blocks: FxHashMap::default(),
            unwind_subgraph: unwind_subgraph(body),
            cleanup_blocks: cleanup_blocks(body),
        };
        for (block, block_data) in mir::traversal::preorder(body) {
            if task_tree.unwind_subgraph.contains(block) {
                continue;
            }

            let current_task = *task_tree.basic_blocks.entry(block).or_insert_with(|| {
                assert!(
                    task_tree.tasks.is_empty(),
                    "expected the first task to be the only orphan task!"
                );
                task_tree.tasks.push(TaskData {
                    parent: None,
                    children: vec![],
                    last_locations: vec![],
                })
            });

            // As per Location's docs, we know that the length of statements is the index of the terminator.
            let location = Location { block, statement_index: block_data.statements.len() };
            let terminator = block_data.terminator();
            match terminator.kind {
                mir::TerminatorKind::Detach { spawned_task, continuation } => {
                    task_tree.detach_at(current_task, spawned_task, continuation);
                }
                mir::TerminatorKind::Reattach { continuation } => {
                    task_tree.reattach_at(location, current_task, continuation);
                }
                _ => {
                    // For all other terminators, we want to mark all targets as children of the current task.
                    // The correct behavior for panics and unwinding is to avoid marking blocks used during
                    // unwinding as part of any tasks. We should disallow using spawn and sync in unwinding
                    // contexts.
                    task_tree.add_successors_to_current_task(current_task, terminator);
                }
            }
        }
        task_tree.validate();
        task_tree
    }
}

// FIXME(jhilton): at some point we should do a dataflow analysis on which tasks can be potentially running at a time given that
// basic blocks have been assigned to tasks. The only complicated part is that a sync says that all tasks which could be synced
// are definitely not running, and then this means that we can have a MightRunLogicallyInParallel and a
// DefinitelyLogicallyRunsInParallel. I think that dataflow is a fairly good fit for this since we know that on either side of a branch,
// a spawned task is "confined" to that side. Then when we merge the branch in the successor to the conditional (however that happens),
// we merge properly depending on the operator we use for merging (intersection or union). Without this change, we too-optimistically
// mark variables as initialized if they're initialized in some conditionally-spawned work, which is an obvious soundness bug.

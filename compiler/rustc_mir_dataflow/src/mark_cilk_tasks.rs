use rustc_data_structures::fx::FxHashMap;
use rustc_index::IndexVec;
use rustc_middle::mir::{self, visit::Visitor, BasicBlock};

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
    pub last_locations: Vec<mir::Location>,
}

pub struct TaskTree {
    tasks: IndexVec<Task, TaskData>,
    basic_blocks: FxHashMap<BasicBlock, Task>,
}

impl TaskTree {
    /// Label the block as part of the given task, panicking if it's already mapped to a different task.
    ///
    /// This makes sense whenever the block might have been labeled with a task already, but you
    /// should always expect that task to be the same: no basic block should be part of two tasks.
    fn label_block(&mut self, block: BasicBlock, task: Task) {
        match self.basic_blocks.entry(block) {
            std::collections::hash_map::Entry::Occupied(other_task)
                if *other_task.get() != task =>
            {
                panic!("expected the task for this block to be the same as the task given!")
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

    /// Create a new TaskTree.
    pub fn new() -> Self {
        Self {
            tasks: IndexVec::new(),
            basic_blocks: rustc_data_structures::fx::FxHashMap::default(),
        }
    }

    fn task(&self, block: BasicBlock) -> Option<Task> {
        self.basic_blocks.get(&block).copied()
    }

    /// Get the task for the given location, panicking if it doesn't exist.
    pub fn expect_task(&self, location: mir::Location) -> Task {
        self.task(location.block).expect("expected block to have a task!")
    }

    /// Get the last locations of the children of this task.
    pub fn children_last_locations(&self, task: Task) -> impl Iterator<Item = mir::Location> + '_ {
        self.tasks[task]
            .children
            .iter()
            .flat_map(move |&child| self.tasks[child].last_locations.iter().copied())
    }

    /// Get an iterator over child tasks and their last locations.
    pub fn last_locations_by_child(
        &self,
        task: Task,
    ) -> impl Iterator<Item = (Task, &[mir::Location])> + '_ {
        self.tasks[task]
            .children
            .iter()
            .map(|&child| (child, self.tasks[child].last_locations.as_ref()))
    }
}

impl<'tcx> Visitor<'tcx> for TaskTree {
    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        // If we see a terminator, we want to mark the reachable blocks as being part of
        // the current task, unless this is a Detach, in which case the spawned task is part
        // of a new task. On a reattach, the task should be marked as the parent of whatever task
        // this basic block is part of.

        // This makes sense because we expect it to only happen once. When we finalize the analysis, we'll make sure
        // that there's exactly one task with no parent (an orphan task).
        let current_task = *self.basic_blocks.entry(location.block).or_insert_with(|| {
            self.tasks.push(TaskData { parent: None, children: vec![], last_locations: vec![] })
        });
        match terminator.kind {
            mir::TerminatorKind::Detach { spawned_task, continuation } => {
                self.label_block(continuation, current_task);
                let new_task = self.tasks.push(TaskData {
                    parent: Some(current_task),
                    children: vec![],
                    last_locations: vec![],
                });
                self.tasks[current_task].children.push(new_task);
                self.label_block(spawned_task, new_task);
            }
            mir::TerminatorKind::Reattach { continuation } => {
                let current_task_data = &mut self.tasks[current_task];

                // Reattach is the only way for the task to change to some other task in a way that
                // won't return control to the old task, so we want to add it as a "last location".
                current_task_data.last_locations.push(location);

                let parent = current_task_data
                    .parent
                    .expect("expected current task to have parent if reattaching!");
                self.label_block(continuation, parent);

                debug_assert!(
                    self.tasks[parent].children.contains(&current_task),
                    "the current task should be a child of the task being reattached to!"
                );
            }
            _ => {
                // For all other terminators, we want to mark all targets as children of the current task.
                // This might have the wrong semantics with panics and unwinding? Hopefully sync insertion
                // can make that a nonissue.
                match terminator.edges() {
                    mir::TerminatorEdges::None => {
                        // No targets, nothing to do
                    }
                    mir::TerminatorEdges::Single(target) => {
                        self.label_block(target, current_task);
                    }
                    mir::TerminatorEdges::Double(target1, target2) => {
                        self.label_block(target1, current_task);
                        self.label_block(target2, current_task);
                    }
                    mir::TerminatorEdges::AssignOnReturn { return_, cleanup, place: _ } => {
                        for target in return_.into_iter().chain(cleanup.into_iter()) {
                            self.label_block(target, current_task);
                        }
                    }
                    mir::TerminatorEdges::SwitchInt { targets, discr: _ } => {
                        for target in targets.all_targets() {
                            self.label_block(*target, current_task);
                        }
                    }
                }
            }
        }
    }
}

// FIXME(jhilton): at some point we should do a dataflow analysis on which tasks can be potentially running at a time given that
// basic blocks have been assigned to tasks. The only complicated part is that a sync says that all tasks which could be synced
// are definitely not running, and then this means that we can have a MightRunLogicallyInParallel and a
// DefinitelyLogicallyRunsInParallel. I think that dataflow is a fairly good fit for this since we know that on either side of a branch,
// a spawned task is "confined" to that side. Then when we merge the branch in the successor to the conditional (however that happens),
// we merge properly depending on the operator we use for merging (intersection or union). Without this change, we too-optimistically
// mark variables as initialized if they're initialized in some conditionally-spawned work, which is an obvious soundness bug.

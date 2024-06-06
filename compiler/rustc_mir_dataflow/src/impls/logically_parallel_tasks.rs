use rustc_index::bit_set::BitSet;
use rustc_middle::mir;

use crate::task_info::{Task, TaskInfo};
use crate::{AnalysisDomain, Forward, GenKill, GenKillAnalysis};

/// An analysis of which tasks are executing logically in parallel at any given program point.
/// The terminators of interest here are Detach, Reattach, and Sync, since no other statement
/// or terminator can create a new task.
///
/// This analysis is notably *not* usable for determining what dataflow state should be merged
/// at a given sync. This is due to a particular case where Task A spawns Task B, which
/// spawns Task C. If Task B then syncs Task C, the dataflow state from Task C should not be
/// merged at a sync in Task A. In general, this analysis includes *all* tasks that may logically
/// be in parallel rather than just those tasks whose dataflow state should be merged at a
/// sync.
///
/// This analysis is also a "Maybe" analysis in that if a task is conditionally spawned, the task
/// is considered to be logically in parallel at program points that are dominated by the condition.
struct LogicallyParallelTasks {
    task_info: TaskInfo,
}

impl<'tcx> AnalysisDomain<'tcx> for LogicallyParallelTasks {
    type Domain = BitSet<Task>;
    type Direction = Forward;

    const NAME: &'static str = "logically_parallel_tasks";

    fn bottom_value(&self, body: &rustc_middle::mir::Body<'tcx>) -> Self::Domain {
        BitSet::new_empty(self.task_info.num_tasks())
    }

    fn initialize_start_block(
        &self,
        body: &rustc_middle::mir::Body<'tcx>,
        state: &mut Self::Domain,
    ) {
        // Task 0 is initially executing at the beginning of the start block.
        state.insert(Task::from_usize(0));
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for LogicallyParallelTasks {
    type Idx = Task;

    fn domain_size(&self, body: &rustc_middle::mir::Body<'tcx>) -> usize {
        self.task_info.num_tasks()
    }

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        // Nothing here since no statement affects the currently-parallel task set,
        // only terminators can do that.
    }

    fn call_return_effect(
        &mut self,
        trans: &mut Self::Domain,
        block: mir::BasicBlock,
        return_places: mir::CallReturnPlaces<'_, 'tcx>,
    ) {
        // Nothing here since returning doesn't affect the currently-parallel task set.
    }

    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) -> rustc_middle::mir::TerminatorEdges<'mir, 'tcx> {
        // NOTE(jhilton): I think our handling of unwinds (or lack thereof) is fine
        // here since we won't be querying anything in the unwind subgraph.
        let kind = &terminator.kind;
        if let mir::TerminatorKind::Detach { spawned_task, continuation } = kind {
            // At a detach, both the spawned task and the current task are logically
            // in parallel.
            let spawned_task = self.task_info.expect_task(*spawned_task);
            let continuation_task = self.task_info.expect_task(*continuation);
            trans.insert(spawned_task);
            trans.insert(continuation_task);
        } else if let mir::TerminatorKind::Reattach { continuation: _ } = kind {
            // All descendants of the spawned task should be logically parallel here
            // since the continuation can be executing in parallel with any point in
            // the spawned task.
            let current_task = self.task_info.expect_task(location.block);
            for descendant in self.task_info.descendants(current_task) {
                trans.insert(descendant);
            }
        } else if let mir::TerminatorKind::Sync { target: _ } = kind {
            // Syncs wait for any descendant of the current task, so
            // none of those descendants can be logically in parallel
            // after the sync.
            let current_task = self.task_info.expect_task(location.block);
            for descendant in self.task_info.descendants(current_task) {
                trans.remove(descendant);
            }
        }

        terminator.edges()
    }
}

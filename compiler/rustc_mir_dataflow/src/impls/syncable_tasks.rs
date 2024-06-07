use rustc_index::bit_set::BitSet;
use rustc_middle::mir;

use crate::lattice::Dual;
use crate::task_info::{Task, TaskInfo};
use crate::{AnalysisDomain, Forward, GenKill, GenKillAnalysis};

struct DefinitelySyncableTasks {
    task_info: TaskInfo,
    saved_reattach_state: Option<(mir::BasicBlock, Dual<BitSet<Task>>)>,
}

impl DefinitelySyncableTasks {
    fn cache_reattach_state(&mut self, block: mir::BasicBlock, output_state: Dual<BitSet<Task>>) {
        assert!(
            self.saved_reattach_state.is_none(),
            "expected no saved reattach state when caching reattach state!"
        );
        self.saved_reattach_state = Some((block, output_state));
    }

    fn should_take_reattach_state(&self, current_block: mir::BasicBlock) -> bool {
        self.saved_reattach_state
            .as_ref()
            .filter(|(block, _state)| *block == current_block)
            .is_some()
    }

    fn expect_take_reattach_state(&mut self) -> Dual<BitSet<Task>> {
        self.saved_reattach_state
            .take()
            .map(|(_block, state)| state)
            .expect("expected reattach state to be defined!")
    }

    fn update_state_from_reattach_state(
        &mut self,
        current_block: mir::BasicBlock,
        trans: &mut impl GenKill<Task>,
    ) {
        // The only special case here is where our location is the beginning of the basic block referenced
        // in self. If that's the case, we want to union that dataflow state with the current dataflow state.
        // This is because in the handling of Reattach, we'll have cached the dataflow state so that it can
        // be merged into the continuation header that we're seeing now.
        if self.should_take_reattach_state(current_block) {
            let state = self.expect_take_reattach_state();
            // We have to use meet because the domain is a dual of a join (union-based) lattice
            // where join is instead intersection, so we use meet to get union.
            trans.gen_all(state.0.iter());
        }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for DefinitelySyncableTasks {
    type Domain = Dual<BitSet<Task>>;
    type Direction = Forward;

    const NAME: &'static str = "definitely_syncable_tasks";

    fn bottom_value(&self, _body: &mir::Body<'tcx>) -> Self::Domain {
        Dual(BitSet::new_empty(self.task_info.num_tasks()))
    }

    fn initialize_start_block(&self, _body: &mir::Body<'tcx>, state: &mut Self::Domain) {
        // Task 0 is initially executing at the beginning of the start block.
        state.gen(Task::from_usize(0));
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for DefinitelySyncableTasks {
    type Idx = Task;

    fn domain_size(&self, _body: &mir::Body<'tcx>) -> usize {
        self.task_info.num_tasks()
    }

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        _statement: &mir::Statement<'tcx>,
        location: mir::Location,
    ) {
        self.update_state_from_reattach_state(location.block, trans);
    }

    fn call_return_effect(
        &mut self,
        _trans: &mut Self::Domain,
        _block: mir::BasicBlock,
        _return_places: mir::CallReturnPlaces<'_, 'tcx>,
    ) {
        // Doing nothing here should be fine.
        // [terminator_effect] still runs regardless of whether
        // or not the call successfully returns, while this runs
        // only on successful return.
    }

    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: mir::Location,
    ) -> mir::TerminatorEdges<'mir, 'tcx> {
        self.update_state_from_reattach_state(location.block, trans);

        let kind = &terminator.kind;
        if let mir::TerminatorKind::Detach { spawned_task, continuation: _ } = kind {
            // We now add the spawned task to the syncable task set.
            let spawned_task = self.task_info.expect_task(*spawned_task);
            trans.gen(spawned_task);
        } else if let mir::TerminatorKind::Reattach { continuation } = kind {
            // We have to save the current state for bookkeeping when we reach the
            // continuation: we know that by the traversal order this is the last
            // reattach before the dataflow analysis reaches the continuation.
            self.cache_reattach_state(*continuation, trans.clone());
        } else if let mir::TerminatorKind::Sync { target: _ } = kind {
            // Remove all descendants from the dataflow state: they'll be synced by
            // this sync.
            let current_task = self.task_info.expect_task(location.block);
            for descendant in self.task_info.descendants(current_task) {
                trans.kill(descendant);
            }
        }

        terminator.edges()
    }
}

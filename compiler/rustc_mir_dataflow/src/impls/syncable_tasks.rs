//! This module defines analyses for which tasks will be waited for at a sync.
//!
//! It offers two levels of abstraction: the dataflow analysis itself, through structs like
//! [DefinitelySyncableTasks] and [MaybeSyncableTasks], and a mapping from syncs to the tasks
//! which are waited for at the sync, through the functions [definitely_synced_tasks]
//! and [maybe_synced_tasks], and their corresponding returned structs.
//!
//! Use the latter if you don't need to know anything other than which tasks are waited for
//! at a sync, and use the former for cases where you need additional information the analysis
//! can provide (such as dataflow state at locations other than syncs).

use rustc_data_structures::fx::FxHashMap;
use rustc_index::bit_set::BitSet;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use std::iter::Iterator;

use smallvec::SmallVec;

use crate::fmt::DebugWithContext;
use crate::lattice::Dual;
use crate::task_info::{Task, TaskInfo};
use crate::{Analysis, AnalysisDomain, Forward, GenKill, GenKillAnalysis, Results, ResultsCursor};

/// An analysis of which tasks can be definitely synced at any given program point.
/// The terminators of interest here are, similar to LogicallyParallelTasks,
/// Detach, Reattach, and Sync, since no other statement or terminator can spawn
/// or stop a task.
///
/// This analysis is usable for determining whether dataflow state should be merged
/// at a given sync.
///
/// This analyis is a "must" analysis: any given task which is stated as "definitely
/// syncable" must be logically in parallel with the current program point.
///
/// [saved_reattach_state] is part of a hacky solution to the problem of only having
/// one join operator. Since at, say, a SwitchInt terminator where all arms enter
/// the same basic block, we want to only consider tasks syncable if they're syncable
/// in all branches, we need intersection as the joining operator. However, this means
/// that for the continuation header after a detach, which has an edge from the detach
/// and from the reattach of the spawned task, the dataflow state will just be the state
/// from the detach. The state from the detach will be a subset of the state from the
/// reattach, so intersection always gives the state from the detach. Our solution for
/// this is to cache the reattach state before the continuation header is visited and
/// union with the cached state. This only works because a forward dataflow analysis needs
/// to visit the basic blocks in a pre-order traversal, which means that the reattach
/// with an edge to the continuation header will be visited immediately before the
/// continuation header by construction.
pub struct DefinitelySyncableTasks<'task_info> {
    task_info: &'task_info TaskInfo,
    saved_reattach_state: Option<(mir::BasicBlock, Dual<BitSet<Task>>)>,
}

impl<'task_info> DefinitelySyncableTasks<'task_info> {
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

impl<'tcx, 'task_info> AnalysisDomain<'tcx> for DefinitelySyncableTasks<'task_info> {
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

impl<'tcx, 'task_info> GenKillAnalysis<'tcx> for DefinitelySyncableTasks<'task_info> {
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
            trans.kill_all(self.task_info.descendants(current_task));
        }

        terminator.edges()
    }
}

/// An analysis of which tasks may be able to be synced at a given program point.
/// The terminators of interest here are the same as [DefinitelySyncableTasks].
///
/// This analysis is also useful for determining what dataflow state should be
/// merged at a sync.
///
/// This analysis is a "may" analysis: any given task which is stated as "maybe syncable"
/// might be logically in parallel with the current program point.
pub struct MaybeSyncableTasks<'task_info> {
    task_info: &'task_info TaskInfo,
}

impl<'tcx, 'task_info> AnalysisDomain<'tcx> for MaybeSyncableTasks<'task_info> {
    type Domain = BitSet<Task>;

    type Direction = Forward;

    const NAME: &'static str = "maybe_syncable_tasks";

    fn bottom_value(&self, _body: &mir::Body<'tcx>) -> Self::Domain {
        BitSet::new_empty(self.task_info.num_tasks())
    }

    fn initialize_start_block(&self, _body: &mir::Body<'tcx>, state: &mut Self::Domain) {
        state.gen(Task::from_usize(0))
    }
}

impl<'tcx, 'task_info> GenKillAnalysis<'tcx> for MaybeSyncableTasks<'task_info> {
    type Idx = Task;

    fn domain_size(&self, _body: &mir::Body<'tcx>) -> usize {
        self.task_info.num_tasks()
    }

    fn statement_effect(
        &mut self,
        _trans: &mut impl GenKill<Self::Idx>,
        _statement: &mir::Statement<'tcx>,
        _location: mir::Location,
    ) {
        // Nothing to see here: there are no statements that modify task state.
    }

    fn call_return_effect(
        &mut self,
        _trans: &mut Self::Domain,
        _block: mir::BasicBlock,
        _return_places: mir::CallReturnPlaces<'_, 'tcx>,
    ) {
        // See [DefinitelySyncableTasks::call_return_effect] for why this is empty.
    }

    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: mir::Location,
    ) -> mir::TerminatorEdges<'mir, 'tcx> {
        let kind = &terminator.kind;

        if let mir::TerminatorKind::Detach { spawned_task, continuation: _ } = kind {
            // Add the spawned task.
            let spawned_task = self.task_info.expect_task(*spawned_task);
            trans.gen(spawned_task);
        } else if let mir::TerminatorKind::Reattach { continuation: _ } = kind {
            // No-op: don't actually have to do anything for this case
            // since reattach doesn't change the tasks which might be running
            // after it.
        } else if let mir::TerminatorKind::Sync { target: _ } = kind {
            // Remove any tasks that are descendants of the current task.
            let current_task = self.task_info.expect_task(location.block);
            trans.kill_all(self.task_info.descendants(current_task));
        }

        terminator.edges()
    }
}

/// Run `analysis`, naming it `pass_name` if `pass_name` is not `None`, on `body` with `tcx`.
/// Returns the result of `analysis` converging to fixpoint.
fn run_analysis<'tcx, A>(
    analysis: A,
    pass_name: Option<&'static str>,
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
) -> Results<'tcx, A>
where
    A: Analysis<'tcx>,
    A::Domain: DebugWithContext<A>,
{
    let mut engine = analysis.into_engine(tcx, body);
    if let Some(pass_name) = pass_name {
        engine = engine.pass_name(pass_name);
    }

    engine.iterate_to_fixpoint()
}

/// An iterator over basic blocks along with the attached data.
trait EnumeratedBlockIter<'mir, 'tcx> =
    Iterator<Item = (mir::BasicBlock, &'mir mir::BasicBlockData<'tcx>)> + 'mir where 'tcx: 'mir;

/// An iterator over the syncs within the blocks being iterated over by `iter`.
struct SyncsIter<I> {
    /// An iterator over a [mir::Body]'s basic blocks, enumerated.
    iter: I,
}

impl<'mir, 'tcx, I> Iterator for SyncsIter<I>
where
    'tcx: 'mir,
    I: EnumeratedBlockIter<'mir, 'tcx>,
{
    type Item = mir::Location;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().and_then(|(block, block_data)| {
            let ends_in_sync =
                matches!(block_data.terminator().kind, mir::TerminatorKind::Sync { .. });
            ends_in_sync
                .then(|| mir::Location { block, statement_index: block_data.statements.len() })
        })
    }
}

/// An iterator over the syncs iterated over by `iter` and the corresponding tasks
/// which are waited for at those syncs.
struct SyncedTasksIter<'cursor, 'mir, 'tcx, A: Analysis<'tcx>, F, I> {
    syncs: SyncsIter<I>,
    cursor: &'cursor mut ResultsCursor<'mir, 'tcx, A>,
    merge: F,
}

impl<'cursor, 'mir, 'tcx, A, F, I> Iterator for SyncedTasksIter<'cursor, 'mir, 'tcx, A, F, I>
where
    A: Analysis<'tcx>,
    A::Domain: Clone,
    F: FnMut(A::Domain, &A::Domain) -> BitSet<Task> + 'static,
    I: EnumeratedBlockIter<'mir, 'tcx>,
{
    type Item = (mir::Location, BitSet<Task>);

    fn next(&mut self) -> Option<Self::Item> {
        self.syncs.next().map(|location| {
            self.cursor.seek_before_primary_effect(location);
            let before_state = self.cursor.get().clone();
            self.cursor.seek_after_primary_effect(location);
            let after_state = self.cursor.get();
            (location, (self.merge)(before_state, &after_state))
        })
    }
}

/// Find the syncs in `body` and the tasks waited for at those syncs, where
/// `cursor` visits some dataflow analysis results and `merge` indicates how to
/// compute the tasks waited for at a sync given the dataflow state before and
/// after the sync.
fn synced_tasks_for_body<'cursor, 'mir, 'tcx, A, F>(
    body: &'mir mir::Body<'tcx>,
    cursor: &'cursor mut ResultsCursor<'mir, 'tcx, A>,
    merge: F,
) -> SyncedTasksIter<'cursor, 'mir, 'tcx, A, F, impl EnumeratedBlockIter<'mir, 'tcx>>
where
    A: Analysis<'tcx>,
    A::Domain: Clone,
    F: FnMut(A::Domain, &A::Domain) -> BitSet<Task> + 'static,
{
    let syncs = SyncsIter { iter: body.basic_blocks.iter_enumerated() };
    SyncedTasksIter { syncs, cursor, merge }
}

/// A mapping from locations corresponding to syncs in a body to the tasks
/// which must be waited for at those syncs.
pub struct DefinitelySyncedTasks {
    pub synced_tasks: FxHashMap<mir::Location, SmallVec<[Task; 2]>>,
}

impl DefinitelySyncedTasks {
    fn new<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>, task_info: &TaskInfo) -> Self {
        let mut cursor = run_analysis(
            DefinitelySyncableTasks { task_info, saved_reattach_state: None },
            Some("definitely_synced_tasks"),
            tcx,
            body,
        )
        .into_results_cursor(body);

        let synced_tasks = synced_tasks_for_body(body, &mut cursor, |mut before, after| {
            before.0.subtract(&after.0);
            before.0
        })
        .map(|(location, tasks)| {
            let tasks: SmallVec<[Task; 2]> = tasks.iter().collect();
            (location, tasks)
        })
        .collect();

        Self { synced_tasks }
    }
}

/// Find the tasks which must be waited for at each sync in `body`
/// where `task_info` is a [TaskInfo] constructed from analyzing `body`.
#[allow(unused)]
pub fn definitely_synced_tasks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    task_info: &TaskInfo,
) -> DefinitelySyncedTasks {
    DefinitelySyncedTasks::new(tcx, body, task_info)
}

/// A mapping from locations corresponding to syncs in a body to the tasks
/// which may be waited for at those syncs.
pub struct MaybeSyncedTasks {
    pub synced_tasks: FxHashMap<mir::Location, SmallVec<[Task; 2]>>,
}

impl MaybeSyncedTasks {
    fn new<'tcx>(tcx: TyCtxt<'tcx>, body: &mir::Body<'tcx>, task_info: &TaskInfo) -> Self {
        let mut cursor =
            run_analysis(MaybeSyncableTasks { task_info }, Some("maybe_synced_tasks"), tcx, body)
                .into_results_cursor(body);

        let synced_tasks = synced_tasks_for_body(body, &mut cursor, |mut before, after| {
            before.subtract(after);
            before
        })
        .map(|(location, tasks)| {
            let tasks: SmallVec<[Task; 2]> = tasks.iter().collect();
            (location, tasks)
        })
        .collect();

        Self { synced_tasks }
    }
}

/// Find the tasks which may be waited for at each sync in `body`
/// where `task_info` is a [TaskInfo] constructed from analyzing `body`.
#[allow(unused)]
pub fn maybe_synced_tasks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    task_info: &TaskInfo,
) -> MaybeSyncedTasks {
    MaybeSyncedTasks::new(tcx, body, task_info)
}

use rustc_index::bit_set::{BitSet, ChunkedBitSet};
use rustc_index::Idx;
use rustc_middle::mir::{self, Body, CallReturnPlaces, Location, TerminatorEdges};
use rustc_middle::ty::{self, TyCtxt};

use crate::elaborate_drops::DropFlagState;
use crate::framework::SwitchIntEdgeEffects;
use crate::move_paths::{HasMoveData, InitIndex, InitKind, LookupResult, MoveData, MovePathIndex};
use crate::on_lookup_result_bits;
use crate::MoveDataParamEnv;
use crate::{drop_flag_effects, on_all_children_bits};
use crate::{drop_flag_effects_for_function_entry, mark_cilk_tasks};
use crate::{drop_flag_effects_for_location, JoinSemiLattice};
use crate::{lattice, AnalysisDomain, GenKill, GenKillAnalysis, MaybeReachable};

/// `MaybeInitializedPlaces` tracks all places that might be
/// initialized upon reaching a particular point in the control flow
/// for a function.
///
/// For example, in code like the following, we have corresponding
/// dataflow information shown in the right-hand comments.
///
/// ```rust
/// struct S;
/// fn foo(pred: bool) {                        // maybe-init:
///                                             // {}
///     let a = S; let mut b = S; let c; let d; // {a, b}
///
///     if pred {
///         drop(a);                            // {   b}
///         b = S;                              // {   b}
///
///     } else {
///         drop(b);                            // {a}
///         d = S;                              // {a,       d}
///
///     }                                       // {a, b,    d}
///
///     c = S;                                  // {a, b, c, d}
/// }
/// ```
///
/// To determine whether a place *must* be initialized at a
/// particular control-flow point, one can take the set-difference
/// between this data and the data from `MaybeUninitializedPlaces` at the
/// corresponding control-flow point.
///
/// Similarly, at a given `drop` statement, the set-intersection
/// between this data and `MaybeUninitializedPlaces` yields the set of
/// places that would require a dynamic drop-flag at that statement.
pub struct MaybeInitializedPlaces<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    mdpe: &'a MoveDataParamEnv<'tcx>,
    skip_unreachable_unwind: bool,
    /// Maps basic blocks to the task they are part of.
    task_tree: mark_cilk_tasks::TaskTree,
    /// Maps locations to the state of the dataflow analysis at that location. The locations in this
    /// map are the last locations of tasks.
    state_at_last_locations: rustc_data_structures::fx::FxHashMap<
        Location,
        MaybeReachable<ChunkedBitSet<MovePathIndex>>,
    >,
}

fn task_tree_of_body<'a, 'tcx>(body: &'a Body<'tcx>) -> mark_cilk_tasks::TaskTree {
    use rustc_middle::mir::visit::Visitor;
    let mut task_tree = mark_cilk_tasks::TaskTree::new();
    task_tree.visit_body(body);
    task_tree.validate();
    task_tree
}

impl<'a, 'tcx> MaybeInitializedPlaces<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, mdpe: &'a MoveDataParamEnv<'tcx>) -> Self {
        // FIXME(jhilton): I don't like that this constructor does non-trivial work. Make the task tree a parameter?
        MaybeInitializedPlaces {
            tcx,
            body,
            mdpe,
            skip_unreachable_unwind: false,
            task_tree: task_tree_of_body(body),
            state_at_last_locations: rustc_data_structures::fx::FxHashMap::default(),
        }
    }

    pub fn skipping_unreachable_unwind(mut self) -> Self {
        self.skip_unreachable_unwind = true;
        self
    }

    pub fn is_unwind_dead(
        &self,
        place: mir::Place<'tcx>,
        state: &MaybeReachable<ChunkedBitSet<MovePathIndex>>,
    ) -> bool {
        if let LookupResult::Exact(path) = self.move_data().rev_lookup.find(place.as_ref()) {
            let mut maybe_live = false;
            on_all_children_bits(self.move_data(), path, |child| {
                maybe_live |= state.contains(child);
            });
            !maybe_live
        } else {
            false
        }
    }
}

impl<'a, 'tcx> HasMoveData<'tcx> for MaybeInitializedPlaces<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.mdpe.move_data
    }
}

/// `MaybeUninitializedPlaces` tracks all places that might be
/// uninitialized upon reaching a particular point in the control flow
/// for a function.
///
/// For example, in code like the following, we have corresponding
/// dataflow information shown in the right-hand comments.
///
/// ```rust
/// struct S;
/// fn foo(pred: bool) {                        // maybe-uninit:
///                                             // {a, b, c, d}
///     let a = S; let mut b = S; let c; let d; // {      c, d}
///
///     if pred {
///         drop(a);                            // {a,    c, d}
///         b = S;                              // {a,    c, d}
///
///     } else {
///         drop(b);                            // {   b, c, d}
///         d = S;                              // {   b, c   }
///
///     }                                       // {a, b, c, d}
///
///     c = S;                                  // {a, b,    d}
/// }
/// ```
///
/// To determine whether a place *must* be uninitialized at a
/// particular control-flow point, one can take the set-difference
/// between this data and the data from `MaybeInitializedPlaces` at the
/// corresponding control-flow point.
///
/// Similarly, at a given `drop` statement, the set-intersection
/// between this data and `MaybeInitializedPlaces` yields the set of
/// places that would require a dynamic drop-flag at that statement.
pub struct MaybeUninitializedPlaces<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    mdpe: &'a MoveDataParamEnv<'tcx>,

    mark_inactive_variants_as_uninit: bool,
    skip_unreachable_unwind: BitSet<mir::BasicBlock>,

    /// See [MaybeInitializedPlaces::task_tree].
    task_tree: mark_cilk_tasks::TaskTree,
    /// See [MaybeInitializedPlaces::state_at_last_locations]
    state_at_last_locations:
        rustc_data_structures::fx::FxHashMap<Location, ChunkedBitSet<MovePathIndex>>,
}

impl<'a, 'tcx> MaybeUninitializedPlaces<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, mdpe: &'a MoveDataParamEnv<'tcx>) -> Self {
        // TODO(jhilton): non-trivial work in constructor :(
        MaybeUninitializedPlaces {
            tcx,
            body,
            mdpe,
            mark_inactive_variants_as_uninit: false,
            skip_unreachable_unwind: BitSet::new_empty(body.basic_blocks.len()),
            task_tree: task_tree_of_body(body),
            state_at_last_locations: rustc_data_structures::fx::FxHashMap::default(),
        }
    }

    /// Causes inactive enum variants to be marked as "maybe uninitialized" after a switch on an
    /// enum discriminant.
    ///
    /// This is correct in a vacuum but is not the default because it causes problems in the borrow
    /// checker, where this information gets propagated along `FakeEdge`s.
    pub fn mark_inactive_variants_as_uninit(mut self) -> Self {
        self.mark_inactive_variants_as_uninit = true;
        self
    }

    pub fn skipping_unreachable_unwind(
        mut self,
        unreachable_unwind: BitSet<mir::BasicBlock>,
    ) -> Self {
        self.skip_unreachable_unwind = unreachable_unwind;
        self
    }
}

impl<'a, 'tcx> HasMoveData<'tcx> for MaybeUninitializedPlaces<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.mdpe.move_data
    }
}

/// `DefinitelyInitializedPlaces` tracks all places that are definitely
/// initialized upon reaching a particular point in the control flow
/// for a function.
///
/// For example, in code like the following, we have corresponding
/// dataflow information shown in the right-hand comments.
///
/// ```rust
/// struct S;
/// fn foo(pred: bool) {                        // definite-init:
///                                             // {          }
///     let a = S; let mut b = S; let c; let d; // {a, b      }
///
///     if pred {
///         drop(a);                            // {   b,     }
///         b = S;                              // {   b,     }
///
///     } else {
///         drop(b);                            // {a,        }
///         d = S;                              // {a,       d}
///
///     }                                       // {          }
///
///     c = S;                                  // {       c  }
/// }
/// ```
///
/// To determine whether a place *may* be uninitialized at a
/// particular control-flow point, one can take the set-complement
/// of this data.
///
/// Similarly, at a given `drop` statement, the set-difference between
/// this data and `MaybeInitializedPlaces` yields the set of places
/// that would require a dynamic drop-flag at that statement.
pub struct DefinitelyInitializedPlaces<'a, 'tcx> {
    body: &'a Body<'tcx>,
    mdpe: &'a MoveDataParamEnv<'tcx>,
    task_tree: mark_cilk_tasks::TaskTree,
    state_at_last_locations:
        rustc_data_structures::fx::FxHashMap<Location, lattice::Dual<BitSet<MovePathIndex>>>,
}

impl<'a, 'tcx> DefinitelyInitializedPlaces<'a, 'tcx> {
    pub fn new(body: &'a Body<'tcx>, mdpe: &'a MoveDataParamEnv<'tcx>) -> Self {
        DefinitelyInitializedPlaces {
            body,
            mdpe,
            task_tree: task_tree_of_body(body),
            state_at_last_locations: rustc_data_structures::fx::FxHashMap::default(),
        }
    }
}

impl<'a, 'tcx> HasMoveData<'tcx> for DefinitelyInitializedPlaces<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.mdpe.move_data
    }
}

/// `EverInitializedPlaces` tracks all places that might have ever been
/// initialized upon reaching a particular point in the control flow
/// for a function, without an intervening `StorageDead`.
///
/// This dataflow is used to determine if an immutable local variable may
/// be assigned to.
///
/// For example, in code like the following, we have corresponding
/// dataflow information shown in the right-hand comments.
///
/// ```rust
/// struct S;
/// fn foo(pred: bool) {                        // ever-init:
///                                             // {          }
///     let a = S; let mut b = S; let c; let d; // {a, b      }
///
///     if pred {
///         drop(a);                            // {a, b,     }
///         b = S;                              // {a, b,     }
///
///     } else {
///         drop(b);                            // {a, b,      }
///         d = S;                              // {a, b,    d }
///
///     }                                       // {a, b,    d }
///
///     c = S;                                  // {a, b, c, d }
/// }
/// ```
pub struct EverInitializedPlaces<'a, 'tcx> {
    body: &'a Body<'tcx>,
    mdpe: &'a MoveDataParamEnv<'tcx>,
    task_tree: mark_cilk_tasks::TaskTree,
    state_at_last_locations:
        rustc_data_structures::fx::FxHashMap<Location, ChunkedBitSet<InitIndex>>,
}

impl<'a, 'tcx> EverInitializedPlaces<'a, 'tcx> {
    pub fn new(body: &'a Body<'tcx>, mdpe: &'a MoveDataParamEnv<'tcx>) -> Self {
        EverInitializedPlaces {
            body,
            mdpe,
            task_tree: task_tree_of_body(body),
            state_at_last_locations: rustc_data_structures::fx::FxHashMap::default(),
        }
    }
}

impl<'a, 'tcx> HasMoveData<'tcx> for EverInitializedPlaces<'a, 'tcx> {
    fn move_data(&self) -> &MoveData<'tcx> {
        &self.mdpe.move_data
    }
}

impl<'a, 'tcx> MaybeInitializedPlaces<'a, 'tcx> {
    fn update_bits(
        trans: &mut impl GenKill<MovePathIndex>,
        path: MovePathIndex,
        state: DropFlagState,
    ) {
        match state {
            DropFlagState::Absent => trans.kill(path),
            DropFlagState::Present => trans.gen(path),
        }
    }
}

impl<'a, 'tcx> MaybeUninitializedPlaces<'a, 'tcx> {
    fn update_bits(
        trans: &mut impl GenKill<MovePathIndex>,
        path: MovePathIndex,
        state: DropFlagState,
    ) {
        match state {
            DropFlagState::Absent => trans.gen(path),
            DropFlagState::Present => trans.kill(path),
        }
    }
}

impl<'a, 'tcx> DefinitelyInitializedPlaces<'a, 'tcx> {
    fn update_bits(
        trans: &mut impl GenKill<MovePathIndex>,
        path: MovePathIndex,
        state: DropFlagState,
    ) {
        match state {
            DropFlagState::Absent => trans.kill(path),
            DropFlagState::Present => trans.gen(path),
        }
    }
}

impl<'tcx> AnalysisDomain<'tcx> for MaybeInitializedPlaces<'_, 'tcx> {
    /// There can be many more `MovePathIndex` than there are locals in a MIR body.
    /// We use a chunked bitset to avoid paying too high a memory footprint.
    type Domain = MaybeReachable<ChunkedBitSet<MovePathIndex>>;

    const NAME: &'static str = "maybe_init";

    fn bottom_value(&self, _: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = uninitialized
        MaybeReachable::Unreachable
    }

    fn initialize_start_block(&self, _: &mir::Body<'tcx>, state: &mut Self::Domain) {
        *state =
            MaybeReachable::Reachable(ChunkedBitSet::new_empty(self.move_data().move_paths.len()));
        drop_flag_effects_for_function_entry(self.body, self.mdpe, |path, s| {
            assert!(s == DropFlagState::Present);
            state.gen(path);
        });
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for MaybeInitializedPlaces<'_, 'tcx> {
    type Idx = MovePathIndex;

    fn domain_size(&self, _: &Body<'tcx>) -> usize {
        self.move_data().move_paths.len()
    }

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        drop_flag_effects_for_location(self.body, self.mdpe, location, |path, s| {
            Self::update_bits(trans, path, s)
        });

        // Mark all places as "maybe init" if they are mutably borrowed. See #90752.
        if self.tcx.sess.opts.unstable_opts.precise_enum_drop_elaboration
            && let Some((_, rvalue)) = statement.kind.as_assign()
            && let mir::Rvalue::Ref(_, mir::BorrowKind::Mut { .. }, place)
                // FIXME: Does `&raw const foo` allow mutation? See #90413.
                | mir::Rvalue::AddressOf(_, place) = rvalue
            && let LookupResult::Exact(mpi) = self.move_data().rev_lookup.find(place.as_ref())
        {
            on_all_children_bits(self.move_data(), mpi, |child| {
                trans.gen(child);
            })
        }
    }

    fn terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let mut edges = terminator.edges();
        if self.skip_unreachable_unwind
            && let mir::TerminatorKind::Drop { target, unwind, place, replace: _ } = terminator.kind
            && matches!(unwind, mir::UnwindAction::Cleanup(_))
            && self.is_unwind_dead(place, state)
        {
            edges = TerminatorEdges::Single(target);
        }
        drop_flag_effects_for_location(self.body, self.mdpe, location, |path, s| {
            Self::update_bits(state, path, s)
        });

        // This lets us track the state before a reattach, which is necessary when we sync.
        if let mir::TerminatorKind::Reattach { continuation: _ } = terminator.kind {
            self.state_at_last_locations.insert(location, state.clone());
        } else if let mir::TerminatorKind::Sync { target: _ } = terminator.kind {
            // Grab the state at all last locations we could be syncing based on the current basic block.
            let task = self.task_tree.expect_task(location);
            // We skip the locations that don't exist because a task can have children which aren't synced at this point in the dataflow analysis, since
            // they can be successors of this sync. This is because tasks don't end on sync.
            self.task_tree
                .children_last_locations(task)
                .filter_map(|last_location| {
                    self.state_at_last_locations.get(&last_location).cloned()
                })
                .for_each(|state_at_last_location| {
                    // Bottom is uninitialized and top is initialized, and we want to become more initialized, so we go up.
                    // This makes sense because as we go 'up' in the lattice, we consider more of the state to be initialized.
                    // `join` provides least-upper-bound and we want the state to become "more initialized" upon a sync.
                    state.join(&state_at_last_location);
                });
        }

        edges
    }

    fn call_return_effect(
        &mut self,
        trans: &mut Self::Domain,
        _block: mir::BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        return_places.for_each(|place| {
            // when a call returns successfully, that means we need to set
            // the bits for that dest_place to 1 (initialized).
            on_lookup_result_bits(
                self.move_data(),
                self.move_data().rev_lookup.find(place.as_ref()),
                |mpi| {
                    trans.gen(mpi);
                },
            );
        });
    }

    fn switch_int_edge_effects<G: GenKill<Self::Idx>>(
        &mut self,
        block: mir::BasicBlock,
        discr: &mir::Operand<'tcx>,
        edge_effects: &mut impl SwitchIntEdgeEffects<G>,
    ) {
        if !self.tcx.sess.opts.unstable_opts.precise_enum_drop_elaboration {
            return;
        }

        let enum_ = discr.place().and_then(|discr| {
            switch_on_enum_discriminant(self.tcx, self.body, &self.body[block], discr)
        });

        let Some((enum_place, enum_def)) = enum_ else {
            return;
        };

        let mut discriminants = enum_def.discriminants(self.tcx);
        edge_effects.apply(|trans, edge| {
            let Some(value) = edge.value else {
                return;
            };

            // MIR building adds discriminants to the `values` array in the same order as they
            // are yielded by `AdtDef::discriminants`. We rely on this to match each
            // discriminant in `values` to its corresponding variant in linear time.
            let (variant, _) = discriminants
                .find(|&(_, discr)| discr.val == value)
                .expect("Order of `AdtDef::discriminants` differed from `SwitchInt::values`");

            // Kill all move paths that correspond to variants we know to be inactive along this
            // particular outgoing edge of a `SwitchInt`.
            drop_flag_effects::on_all_inactive_variants(
                self.move_data(),
                enum_place,
                variant,
                |mpi| trans.kill(mpi),
            );
        });
    }
}

impl<'tcx> AnalysisDomain<'tcx> for MaybeUninitializedPlaces<'_, 'tcx> {
    /// There can be many more `MovePathIndex` than there are locals in a MIR body.
    /// We use a chunked bitset to avoid paying too high a memory footprint.
    type Domain = ChunkedBitSet<MovePathIndex>;

    const NAME: &'static str = "maybe_uninit";

    fn bottom_value(&self, _: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = initialized (start_block_effect counters this at outset)
        ChunkedBitSet::new_empty(self.move_data().move_paths.len())
    }

    // sets on_entry bits for Arg places
    fn initialize_start_block(&self, _: &mir::Body<'tcx>, state: &mut Self::Domain) {
        // set all bits to 1 (uninit) before gathering counter-evidence
        state.insert_all();

        drop_flag_effects_for_function_entry(self.body, self.mdpe, |path, s| {
            assert!(s == DropFlagState::Present);
            state.remove(path);
        });
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for MaybeUninitializedPlaces<'_, 'tcx> {
    type Idx = MovePathIndex;

    fn domain_size(&self, _: &Body<'tcx>) -> usize {
        self.move_data().move_paths.len()
    }

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        _statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        drop_flag_effects_for_location(self.body, self.mdpe, location, |path, s| {
            Self::update_bits(trans, path, s)
        });

        // Unlike in `MaybeInitializedPlaces` above, we don't need to change the state when a
        // mutable borrow occurs. Places cannot become uninitialized through a mutable reference.
    }

    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        drop_flag_effects_for_location(self.body, self.mdpe, location, |path, s| {
            Self::update_bits(trans, path, s)
        });
        if let mir::TerminatorKind::Reattach { continuation: _ } = terminator.kind {
            self.state_at_last_locations.insert(location, trans.clone());
        } else if let mir::TerminatorKind::Sync { target: _ } = terminator.kind {
            let task = self.task_tree.expect_task(location);
            // See the comment in `MaybeInitializedPlaces::terminator_effect` for why we skip locations that have no state.
            self.task_tree
                .children_last_locations(task)
                .filter_map(|location| self.state_at_last_locations.get(&location))
                .for_each(|state| {
                    use crate::lattice::MeetSemiLattice;
                    // Bottom is all-initialized and top is all-uninitialized, so we want to use meet to go lower in the lattice.
                    trans.meet(state);
                });
        }

        if self.skip_unreachable_unwind.contains(location.block) {
            let mir::TerminatorKind::Drop { target, unwind, .. } = terminator.kind else { bug!() };
            assert!(matches!(unwind, mir::UnwindAction::Cleanup(_)));
            TerminatorEdges::Single(target)
        } else {
            terminator.edges()
        }
    }

    fn call_return_effect(
        &mut self,
        trans: &mut Self::Domain,
        _block: mir::BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        return_places.for_each(|place| {
            // when a call returns successfully, that means we need to set
            // the bits for that dest_place to 0 (initialized).
            on_lookup_result_bits(
                self.move_data(),
                self.move_data().rev_lookup.find(place.as_ref()),
                |mpi| {
                    trans.kill(mpi);
                },
            );
        });
    }

    fn switch_int_edge_effects<G: GenKill<Self::Idx>>(
        &mut self,
        block: mir::BasicBlock,
        discr: &mir::Operand<'tcx>,
        edge_effects: &mut impl SwitchIntEdgeEffects<G>,
    ) {
        if !self.tcx.sess.opts.unstable_opts.precise_enum_drop_elaboration {
            return;
        }

        if !self.mark_inactive_variants_as_uninit {
            return;
        }

        let enum_ = discr.place().and_then(|discr| {
            switch_on_enum_discriminant(self.tcx, self.body, &self.body[block], discr)
        });

        let Some((enum_place, enum_def)) = enum_ else {
            return;
        };

        let mut discriminants = enum_def.discriminants(self.tcx);
        edge_effects.apply(|trans, edge| {
            let Some(value) = edge.value else {
                return;
            };

            // MIR building adds discriminants to the `values` array in the same order as they
            // are yielded by `AdtDef::discriminants`. We rely on this to match each
            // discriminant in `values` to its corresponding variant in linear time.
            let (variant, _) = discriminants
                .find(|&(_, discr)| discr.val == value)
                .expect("Order of `AdtDef::discriminants` differed from `SwitchInt::values`");

            // Mark all move paths that correspond to variants other than this one as maybe
            // uninitialized (in reality, they are *definitely* uninitialized).
            drop_flag_effects::on_all_inactive_variants(
                self.move_data(),
                enum_place,
                variant,
                |mpi| trans.gen(mpi),
            );
        });
    }
}

impl<'a, 'tcx> AnalysisDomain<'tcx> for DefinitelyInitializedPlaces<'a, 'tcx> {
    /// Use set intersection as the join operator.
    type Domain = lattice::Dual<BitSet<MovePathIndex>>;

    const NAME: &'static str = "definite_init";

    fn bottom_value(&self, _: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = initialized (start_block_effect counters this at outset)
        lattice::Dual(BitSet::new_filled(self.move_data().move_paths.len()))
    }

    // sets on_entry bits for Arg places
    fn initialize_start_block(&self, _: &mir::Body<'tcx>, state: &mut Self::Domain) {
        state.0.clear();

        drop_flag_effects_for_function_entry(self.body, self.mdpe, |path, s| {
            assert!(s == DropFlagState::Present);
            state.0.insert(path);
        });
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for DefinitelyInitializedPlaces<'_, 'tcx> {
    type Idx = MovePathIndex;

    fn domain_size(&self, _: &Body<'tcx>) -> usize {
        self.move_data().move_paths.len()
    }

    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        _statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        drop_flag_effects_for_location(self.body, self.mdpe, location, |path, s| {
            Self::update_bits(trans, path, s)
        })
    }

    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        drop_flag_effects_for_location(self.body, self.mdpe, location, |path, s| {
            Self::update_bits(trans, path, s)
        });
        if let mir::TerminatorKind::Reattach { continuation: _ } = terminator.kind {
            self.state_at_last_locations.insert(location, trans.clone());
        } else if let mir::TerminatorKind::Sync { target: _ } = terminator.kind {
            let task = self.task_tree.expect_task(location);
            self.task_tree
                .children_last_locations(task)
                .filter_map(|location| self.state_at_last_locations.get(&location))
                .for_each(|state| {
                    // We want to say that a state is definitely initialized if it is definitely initialized in some synced child.
                    // FIXME(jhilton): this is currently inaccurate because we sync locations that we may not have actually reached
                    // in the case of conditional spawns. We should only sync locations here that we know have actually detached.
                    // We could figure out which locations have actually detached through a separate gen-kill analysis that we only
                    // need for this case. This is a SOUNDNESS problem that we should definitely fix.

                    // Since this lattice has a join operator of intersection and a set bit implies an initialized value, we want
                    // to use union here. We want to get 'lower' in the lattice so we use meet (which will also be union).
                    use crate::framework::lattice::MeetSemiLattice;
                    trans.meet(state);
                });
        }
        terminator.edges()
    }

    fn call_return_effect(
        &mut self,
        trans: &mut Self::Domain,
        _block: mir::BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        return_places.for_each(|place| {
            // when a call returns successfully, that means we need to set
            // the bits for that dest_place to 1 (initialized).
            on_lookup_result_bits(
                self.move_data(),
                self.move_data().rev_lookup.find(place.as_ref()),
                |mpi| {
                    trans.gen(mpi);
                },
            );
        });
    }
}

impl<'tcx> AnalysisDomain<'tcx> for EverInitializedPlaces<'_, 'tcx> {
    /// There can be many more `InitIndex` than there are locals in a MIR body.
    /// We use a chunked bitset to avoid paying too high a memory footprint.
    type Domain = ChunkedBitSet<InitIndex>;

    const NAME: &'static str = "ever_init";

    fn bottom_value(&self, _: &mir::Body<'tcx>) -> Self::Domain {
        // bottom = no initialized variables by default
        ChunkedBitSet::new_empty(self.move_data().inits.len())
    }

    fn initialize_start_block(&self, body: &mir::Body<'tcx>, state: &mut Self::Domain) {
        for arg_init in 0..body.arg_count {
            state.insert(InitIndex::new(arg_init));
        }
    }
}

impl<'tcx> GenKillAnalysis<'tcx> for EverInitializedPlaces<'_, 'tcx> {
    type Idx = InitIndex;

    fn domain_size(&self, _: &Body<'tcx>) -> usize {
        self.move_data().inits.len()
    }

    #[instrument(skip(self, trans), level = "debug")]
    fn statement_effect(
        &mut self,
        trans: &mut impl GenKill<Self::Idx>,
        stmt: &mir::Statement<'tcx>,
        location: Location,
    ) {
        let move_data = self.move_data();
        let init_path_map = &move_data.init_path_map;
        let init_loc_map = &move_data.init_loc_map;
        let rev_lookup = &move_data.rev_lookup;

        debug!("initializes move_indexes {:?}", &init_loc_map[location]);
        trans.gen_all(init_loc_map[location].iter().copied());

        if let mir::StatementKind::StorageDead(local) = stmt.kind {
            // End inits for StorageDead, so that an immutable variable can
            // be reinitialized on the next iteration of the loop.
            if let Some(move_path_index) = rev_lookup.find_local(local) {
                debug!(
                    "clears the ever initialized status of {:?}",
                    init_path_map[move_path_index]
                );
                trans.kill_all(init_path_map[move_path_index].iter().copied());
            }
        }
    }

    #[instrument(skip(self, trans, terminator), level = "debug")]
    fn terminator_effect<'mir>(
        &mut self,
        trans: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let (body, move_data) = (self.body, self.move_data());
        let term = body[location.block].terminator();
        let init_loc_map = &move_data.init_loc_map;
        debug!(?term);
        debug!("initializes move_indexes {:?}", init_loc_map[location]);
        trans.gen_all(
            init_loc_map[location]
                .iter()
                .filter(|init_index| {
                    move_data.inits[**init_index].kind != InitKind::NonPanicPathOnly
                })
                .copied(),
        );
        if let mir::TerminatorKind::Reattach { continuation: _ } = terminator.kind {
            self.state_at_last_locations.insert(location, trans.clone());
        } else if let mir::TerminatorKind::Sync { target: _ } = terminator.kind {
            let task = self.task_tree.expect_task(location);
            self.task_tree
                .children_last_locations(task)
                .filter_map(|location| self.state_at_last_locations.get(&location))
                .for_each(|state| {
                    // This lattice has all-uninitialized as the bottom and the join operator adds
                    // initialized places, so we use join here.
                    trans.join(state);
                });
        }
        terminator.edges()
    }

    fn call_return_effect(
        &mut self,
        trans: &mut Self::Domain,
        block: mir::BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        let move_data = self.move_data();
        let init_loc_map = &move_data.init_loc_map;

        let call_loc = self.body.terminator_loc(block);
        for init_index in &init_loc_map[call_loc] {
            trans.gen(*init_index);
        }
    }
}

/// Inspect a `SwitchInt`-terminated basic block to see if the condition of that `SwitchInt` is
/// an enum discriminant.
///
/// We expect such blocks to have a call to `discriminant` as their last statement like so:
///
/// ```text
/// ...
/// _42 = discriminant(_1)
/// SwitchInt(_42, ..)
/// ```
///
/// If the basic block matches this pattern, this function returns the place corresponding to the
/// enum (`_1` in the example above) as well as the `AdtDef` of that enum.
fn switch_on_enum_discriminant<'mir, 'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &'mir mir::Body<'tcx>,
    block: &'mir mir::BasicBlockData<'tcx>,
    switch_on: mir::Place<'tcx>,
) -> Option<(mir::Place<'tcx>, ty::AdtDef<'tcx>)> {
    for statement in block.statements.iter().rev() {
        match &statement.kind {
            mir::StatementKind::Assign(box (lhs, mir::Rvalue::Discriminant(discriminated)))
                if *lhs == switch_on =>
            {
                match discriminated.ty(body, tcx).ty.kind() {
                    ty::Adt(def, _) => return Some((*discriminated, *def)),

                    // `Rvalue::Discriminant` is also used to get the active yield point for a
                    // coroutine, but we do not need edge-specific effects in that case. This may
                    // change in the future.
                    ty::Coroutine(..) => return None,

                    t => bug!("`discriminant` called on unexpected type {:?}", t),
                }
            }
            mir::StatementKind::Coverage(_) => continue,
            _ => return None,
        }
    }
    None
}

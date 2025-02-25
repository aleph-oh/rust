//! Propagates constants for early reporting of statically known
//! assertion failures

use std::fmt::Debug;

use rustc_const_eval::interpret::{
    format_interp_error, ImmTy, InterpCx, InterpResult, Projectable, Scalar,
};
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_hir::HirId;
use rustc_index::bit_set::BitSet;
use rustc_index::{Idx, IndexVec};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::*;
use rustc_middle::ty::layout::{LayoutError, LayoutOf, LayoutOfHelpers, TyAndLayout};
use rustc_middle::ty::{self, ConstInt, ParamEnv, ScalarInt, Ty, TyCtxt, TypeVisitableExt};
use rustc_span::Span;
use rustc_target::abi::{Abi, FieldIdx, HasDataLayout, Size, TargetDataLayout, VariantIdx};

use crate::const_prop::CanConstProp;
use crate::const_prop::ConstPropMode;
use crate::dataflow_const_prop::DummyMachine;
use crate::errors::{AssertLint, AssertLintKind};
use crate::MirLint;

pub struct ConstPropLint;

impl<'tcx> MirLint<'tcx> for ConstPropLint {
    fn run_lint(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
        if body.tainted_by_errors.is_some() {
            return;
        }

        // will be evaluated by miri and produce its errors there
        if body.source.promoted.is_some() {
            return;
        }

        let def_id = body.source.def_id().expect_local();
        let def_kind = tcx.def_kind(def_id);
        let is_fn_like = def_kind.is_fn_like();
        let is_assoc_const = def_kind == DefKind::AssocConst;

        // Only run const prop on functions, methods, closures and associated constants
        if !is_fn_like && !is_assoc_const {
            // skip anon_const/statics/consts because they'll be evaluated by miri anyway
            trace!("ConstPropLint skipped for {:?}", def_id);
            return;
        }

        // FIXME(welseywiser) const prop doesn't work on coroutines because of query cycles
        // computing their layout.
        if tcx.is_coroutine(def_id.to_def_id()) {
            trace!("ConstPropLint skipped for coroutine {:?}", def_id);
            return;
        }

        trace!("ConstPropLint starting for {:?}", def_id);

        // FIXME(oli-obk, eddyb) Optimize locals (or even local paths) to hold
        // constants, instead of just checking for const-folding succeeding.
        // That would require a uniform one-def no-mutation analysis
        // and RPO (or recursing when needing the value of a local).
        let mut linter = ConstPropagator::new(body, tcx);
        linter.visit_body(body);

        trace!("ConstPropLint done for {:?}", def_id);
    }
}

/// Finds optimization opportunities on the MIR.
struct ConstPropagator<'mir, 'tcx> {
    ecx: InterpCx<'mir, 'tcx, DummyMachine>,
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    worklist: Vec<BasicBlock>,
    visited_blocks: BitSet<BasicBlock>,
    locals: IndexVec<Local, Value<'tcx>>,
    body: &'mir Body<'tcx>,
    written_only_inside_own_block_locals: FxHashSet<Local>,
    can_const_prop: IndexVec<Local, ConstPropMode>,
}

#[derive(Debug, Clone)]
enum Value<'tcx> {
    Immediate(ImmTy<'tcx>),
    Aggregate { variant: VariantIdx, fields: IndexVec<FieldIdx, Value<'tcx>> },
    Uninit,
}

impl<'tcx> From<ImmTy<'tcx>> for Value<'tcx> {
    fn from(v: ImmTy<'tcx>) -> Self {
        Self::Immediate(v)
    }
}

impl<'tcx> Value<'tcx> {
    fn project(
        &self,
        proj: &[PlaceElem<'tcx>],
        prop: &ConstPropagator<'_, 'tcx>,
    ) -> Option<&Value<'tcx>> {
        let mut this = self;
        for proj in proj {
            this = match (*proj, this) {
                (PlaceElem::Field(idx, _), Value::Aggregate { fields, .. }) => {
                    fields.get(idx).unwrap_or(&Value::Uninit)
                }
                (PlaceElem::Index(idx), Value::Aggregate { fields, .. }) => {
                    let idx = prop.get_const(idx.into())?.immediate()?;
                    let idx = prop.ecx.read_target_usize(idx).ok()?;
                    fields.get(FieldIdx::from_u32(idx.try_into().ok()?)).unwrap_or(&Value::Uninit)
                }
                (
                    PlaceElem::ConstantIndex { offset, min_length: _, from_end: false },
                    Value::Aggregate { fields, .. },
                ) => fields
                    .get(FieldIdx::from_u32(offset.try_into().ok()?))
                    .unwrap_or(&Value::Uninit),
                _ => return None,
            };
        }
        Some(this)
    }

    fn project_mut(&mut self, proj: &[PlaceElem<'_>]) -> Option<&mut Value<'tcx>> {
        let mut this = self;
        for proj in proj {
            this = match (proj, this) {
                (PlaceElem::Field(idx, _), Value::Aggregate { fields, .. }) => {
                    fields.ensure_contains_elem(*idx, || Value::Uninit)
                }
                (PlaceElem::Field(..), val @ Value::Uninit) => {
                    *val = Value::Aggregate {
                        variant: VariantIdx::new(0),
                        fields: Default::default(),
                    };
                    val.project_mut(&[*proj])?
                }
                _ => return None,
            };
        }
        Some(this)
    }

    fn immediate(&self) -> Option<&ImmTy<'tcx>> {
        match self {
            Value::Immediate(op) => Some(op),
            _ => None,
        }
    }
}

impl<'tcx> LayoutOfHelpers<'tcx> for ConstPropagator<'_, 'tcx> {
    type LayoutOfResult = Result<TyAndLayout<'tcx>, LayoutError<'tcx>>;

    #[inline]
    fn handle_layout_err(&self, err: LayoutError<'tcx>, _: Span, _: Ty<'tcx>) -> LayoutError<'tcx> {
        err
    }
}

impl HasDataLayout for ConstPropagator<'_, '_> {
    #[inline]
    fn data_layout(&self) -> &TargetDataLayout {
        &self.tcx.data_layout
    }
}

impl<'tcx> ty::layout::HasTyCtxt<'tcx> for ConstPropagator<'_, 'tcx> {
    #[inline]
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
}

impl<'tcx> ty::layout::HasParamEnv<'tcx> for ConstPropagator<'_, 'tcx> {
    #[inline]
    fn param_env(&self) -> ty::ParamEnv<'tcx> {
        self.param_env
    }
}

impl<'mir, 'tcx> ConstPropagator<'mir, 'tcx> {
    fn new(body: &'mir Body<'tcx>, tcx: TyCtxt<'tcx>) -> ConstPropagator<'mir, 'tcx> {
        let def_id = body.source.def_id();
        let param_env = tcx.param_env_reveal_all_normalized(def_id);

        let can_const_prop = CanConstProp::check(tcx, param_env, body);
        let ecx = InterpCx::new(tcx, tcx.def_span(def_id), param_env, DummyMachine);

        ConstPropagator {
            ecx,
            tcx,
            param_env,
            worklist: vec![START_BLOCK],
            visited_blocks: BitSet::new_empty(body.basic_blocks.len()),
            locals: IndexVec::from_elem_n(Value::Uninit, body.local_decls.len()),
            body,
            can_const_prop,
            written_only_inside_own_block_locals: Default::default(),
        }
    }

    fn local_decls(&self) -> &'mir LocalDecls<'tcx> {
        &self.body.local_decls
    }

    fn get_const(&self, place: Place<'tcx>) -> Option<&Value<'tcx>> {
        self.locals[place.local].project(&place.projection, self)
    }

    /// Remove `local` from the pool of `Locals`. Allows writing to them,
    /// but not reading from them anymore.
    fn remove_const(&mut self, local: Local) {
        self.locals[local] = Value::Uninit;
        self.written_only_inside_own_block_locals.remove(&local);
    }

    fn access_mut(&mut self, place: &Place<'_>) -> Option<&mut Value<'tcx>> {
        match self.can_const_prop[place.local] {
            ConstPropMode::NoPropagation => return None,
            ConstPropMode::OnlyInsideOwnBlock => {
                self.written_only_inside_own_block_locals.insert(place.local);
            }
            ConstPropMode::FullConstProp => {}
        }
        self.locals[place.local].project_mut(place.projection)
    }

    fn lint_root(&self, source_info: SourceInfo) -> Option<HirId> {
        source_info.scope.lint_root(&self.body.source_scopes)
    }

    fn use_ecx<F, T>(&mut self, f: F) -> Option<T>
    where
        F: FnOnce(&mut Self) -> InterpResult<'tcx, T>,
    {
        match f(self) {
            Ok(val) => Some(val),
            Err(error) => {
                trace!("InterpCx operation failed: {:?}", error);
                // Some errors shouldn't come up because creating them causes
                // an allocation, which we should avoid. When that happens,
                // dedicated error variants should be introduced instead.
                assert!(
                    !error.kind().formatted_string(),
                    "const-prop encountered formatting error: {}",
                    format_interp_error(self.ecx.tcx.dcx(), error),
                );
                None
            }
        }
    }

    /// Returns the value, if any, of evaluating `c`.
    fn eval_constant(&mut self, c: &ConstOperand<'tcx>) -> Option<ImmTy<'tcx>> {
        // FIXME we need to revisit this for #67176
        if c.has_param() {
            return None;
        }

        // Normalization needed b/c const prop lint runs in
        // `mir_drops_elaborated_and_const_checked`, which happens before
        // optimized MIR. Only after optimizing the MIR can we guarantee
        // that the `RevealAll` pass has happened and that the body's consts
        // are normalized, so any call to resolve before that needs to be
        // manually normalized.
        let val = self.tcx.try_normalize_erasing_regions(self.param_env, c.const_).ok()?;

        self.use_ecx(|this| this.ecx.eval_mir_constant(&val, Some(c.span), None))?
            .as_mplace_or_imm()
            .right()
    }

    /// Returns the value, if any, of evaluating `place`.
    #[instrument(level = "trace", skip(self), ret)]
    fn eval_place(&mut self, place: Place<'tcx>) -> Option<ImmTy<'tcx>> {
        match self.get_const(place)? {
            Value::Immediate(imm) => Some(imm.clone()),
            Value::Aggregate { .. } => None,
            Value::Uninit => None,
        }
    }

    /// Returns the value, if any, of evaluating `op`. Calls upon `eval_constant`
    /// or `eval_place`, depending on the variant of `Operand` used.
    fn eval_operand(&mut self, op: &Operand<'tcx>) -> Option<ImmTy<'tcx>> {
        match *op {
            Operand::Constant(ref c) => self.eval_constant(c),
            Operand::Move(place) | Operand::Copy(place) => self.eval_place(place),
        }
    }

    fn report_assert_as_lint(
        &self,
        location: Location,
        lint_kind: AssertLintKind,
        assert_kind: AssertKind<impl Debug>,
    ) {
        let source_info = self.body.source_info(location);
        if let Some(lint_root) = self.lint_root(*source_info) {
            let span = source_info.span;
            self.tcx.emit_node_span_lint(
                lint_kind.lint(),
                lint_root,
                span,
                AssertLint { span, assert_kind, lint_kind },
            );
        }
    }

    fn check_unary_op(&mut self, op: UnOp, arg: &Operand<'tcx>, location: Location) -> Option<()> {
        let arg = self.eval_operand(arg)?;
        if let (val, true) = self.use_ecx(|this| {
            let val = this.ecx.read_immediate(&arg)?;
            let (_res, overflow) = this.ecx.overflowing_unary_op(op, &val)?;
            Ok((val, overflow))
        })? {
            // `AssertKind` only has an `OverflowNeg` variant, so make sure that is
            // appropriate to use.
            assert_eq!(op, UnOp::Neg, "Neg is the only UnOp that can overflow");
            self.report_assert_as_lint(
                location,
                AssertLintKind::ArithmeticOverflow,
                AssertKind::OverflowNeg(val.to_const_int()),
            );
            return None;
        }

        Some(())
    }

    fn check_binary_op(
        &mut self,
        op: BinOp,
        left: &Operand<'tcx>,
        right: &Operand<'tcx>,
        location: Location,
    ) -> Option<()> {
        let r =
            self.eval_operand(right).and_then(|r| self.use_ecx(|this| this.ecx.read_immediate(&r)));
        let l =
            self.eval_operand(left).and_then(|l| self.use_ecx(|this| this.ecx.read_immediate(&l)));
        // Check for exceeding shifts *even if* we cannot evaluate the LHS.
        if matches!(op, BinOp::Shr | BinOp::Shl) {
            let r = r.clone()?;
            // We need the type of the LHS. We cannot use `place_layout` as that is the type
            // of the result, which for checked binops is not the same!
            let left_ty = left.ty(self.local_decls(), self.tcx);
            let left_size = self.ecx.layout_of(left_ty).ok()?.size;
            let right_size = r.layout.size;
            let r_bits = r.to_scalar().to_bits(right_size).ok();
            if r_bits.is_some_and(|b| b >= left_size.bits() as u128) {
                debug!("check_binary_op: reporting assert for {:?}", location);
                let panic = AssertKind::Overflow(
                    op,
                    match l {
                        Some(l) => l.to_const_int(),
                        // Invent a dummy value, the diagnostic ignores it anyway
                        None => ConstInt::new(
                            ScalarInt::try_from_uint(1_u8, left_size).unwrap(),
                            left_ty.is_signed(),
                            left_ty.is_ptr_sized_integral(),
                        ),
                    },
                    r.to_const_int(),
                );
                self.report_assert_as_lint(location, AssertLintKind::ArithmeticOverflow, panic);
                return None;
            }
        }

        if let (Some(l), Some(r)) = (l, r) {
            // The remaining operators are handled through `overflowing_binary_op`.
            if self.use_ecx(|this| {
                let (_res, overflow) = this.ecx.overflowing_binary_op(op, &l, &r)?;
                Ok(overflow)
            })? {
                self.report_assert_as_lint(
                    location,
                    AssertLintKind::ArithmeticOverflow,
                    AssertKind::Overflow(op, l.to_const_int(), r.to_const_int()),
                );
                return None;
            }
        }
        Some(())
    }

    fn check_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) -> Option<()> {
        // Perform any special handling for specific Rvalue types.
        // Generally, checks here fall into one of two categories:
        //   1. Additional checking to provide useful lints to the user
        //        - In this case, we will do some validation and then fall through to the
        //          end of the function which evals the assignment.
        //   2. Working around bugs in other parts of the compiler
        //        - In this case, we'll return `None` from this function to stop evaluation.
        match rvalue {
            // Additional checking: give lints to the user if an overflow would occur.
            // We do this here and not in the `Assert` terminator as that terminator is
            // only sometimes emitted (overflow checks can be disabled), but we want to always
            // lint.
            Rvalue::UnaryOp(op, arg) => {
                trace!("checking UnaryOp(op = {:?}, arg = {:?})", op, arg);
                self.check_unary_op(*op, arg, location)?;
            }
            Rvalue::BinaryOp(op, box (left, right)) => {
                trace!("checking BinaryOp(op = {:?}, left = {:?}, right = {:?})", op, left, right);
                self.check_binary_op(*op, left, right, location)?;
            }
            Rvalue::CheckedBinaryOp(op, box (left, right)) => {
                trace!(
                    "checking CheckedBinaryOp(op = {:?}, left = {:?}, right = {:?})",
                    op,
                    left,
                    right
                );
                self.check_binary_op(*op, left, right, location)?;
            }

            // Do not try creating references (#67862)
            Rvalue::AddressOf(_, place) | Rvalue::Ref(_, _, place) => {
                trace!("skipping AddressOf | Ref for {:?}", place);

                // This may be creating mutable references or immutable references to cells.
                // If that happens, the pointed to value could be mutated via that reference.
                // Since we aren't tracking references, the const propagator loses track of what
                // value the local has right now.
                // Thus, all locals that have their reference taken
                // must not take part in propagation.
                self.remove_const(place.local);

                return None;
            }
            Rvalue::ThreadLocalRef(def_id) => {
                trace!("skipping ThreadLocalRef({:?})", def_id);

                return None;
            }

            // There's no other checking to do at this time.
            Rvalue::Aggregate(..)
            | Rvalue::Use(..)
            | Rvalue::CopyForDeref(..)
            | Rvalue::Repeat(..)
            | Rvalue::Len(..)
            | Rvalue::Cast(..)
            | Rvalue::ShallowInitBox(..)
            | Rvalue::Discriminant(..)
            | Rvalue::NullaryOp(..) => {}
        }

        // FIXME we need to revisit this for #67176
        if rvalue.has_param() {
            return None;
        }
        if !rvalue.ty(self.local_decls(), self.tcx).is_sized(self.tcx, self.param_env) {
            // the interpreter doesn't support unsized locals (only unsized arguments),
            // but rustc does (in a kinda broken way), so we have to skip them here
            return None;
        }

        Some(())
    }

    fn check_assertion(
        &mut self,
        expected: bool,
        msg: &AssertKind<Operand<'tcx>>,
        cond: &Operand<'tcx>,
        location: Location,
    ) -> Option<!> {
        let value = &self.eval_operand(cond)?;
        trace!("assertion on {:?} should be {:?}", value, expected);

        let expected = Scalar::from_bool(expected);
        let value_const = self.use_ecx(|this| this.ecx.read_scalar(value))?;

        if expected != value_const {
            // Poison all places this operand references so that further code
            // doesn't use the invalid value
            if let Some(place) = cond.place() {
                self.remove_const(place.local);
            }

            enum DbgVal<T> {
                Val(T),
                Underscore,
            }
            impl<T: std::fmt::Debug> std::fmt::Debug for DbgVal<T> {
                fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    match self {
                        Self::Val(val) => val.fmt(fmt),
                        Self::Underscore => fmt.write_str("_"),
                    }
                }
            }
            let mut eval_to_int = |op| {
                // This can be `None` if the lhs wasn't const propagated and we just
                // triggered the assert on the value of the rhs.
                self.eval_operand(op)
                    .and_then(|op| self.ecx.read_immediate(&op).ok())
                    .map_or(DbgVal::Underscore, |op| DbgVal::Val(op.to_const_int()))
            };
            let msg = match msg {
                AssertKind::DivisionByZero(op) => AssertKind::DivisionByZero(eval_to_int(op)),
                AssertKind::RemainderByZero(op) => AssertKind::RemainderByZero(eval_to_int(op)),
                AssertKind::Overflow(bin_op @ (BinOp::Div | BinOp::Rem), op1, op2) => {
                    // Division overflow is *UB* in the MIR, and different than the
                    // other overflow checks.
                    AssertKind::Overflow(*bin_op, eval_to_int(op1), eval_to_int(op2))
                }
                AssertKind::BoundsCheck { ref len, ref index } => {
                    let len = eval_to_int(len);
                    let index = eval_to_int(index);
                    AssertKind::BoundsCheck { len, index }
                }
                // Remaining overflow errors are already covered by checks on the binary operators.
                AssertKind::Overflow(..) | AssertKind::OverflowNeg(_) => return None,
                // Need proper const propagator for these.
                _ => return None,
            };
            self.report_assert_as_lint(location, AssertLintKind::UnconditionalPanic, msg);
        }

        None
    }

    fn ensure_not_propagated(&self, local: Local) {
        if cfg!(debug_assertions) {
            let val = self.get_const(local.into());
            assert!(
                matches!(val, Some(Value::Uninit))
                    || self
                        .layout_of(self.local_decls()[local].ty)
                        .map_or(true, |layout| layout.is_zst()),
                "failed to remove values for `{local:?}`, value={val:?}",
            )
        }
    }

    #[instrument(level = "trace", skip(self), ret)]
    fn eval_rvalue(&mut self, rvalue: &Rvalue<'tcx>, dest: &Place<'tcx>) -> Option<()> {
        if !dest.projection.is_empty() {
            return None;
        }
        use rustc_middle::mir::Rvalue::*;
        let layout = self.ecx.layout_of(dest.ty(self.body, self.tcx).ty).ok()?;
        trace!(?layout);

        let val: Value<'_> = match *rvalue {
            ThreadLocalRef(_) => return None,

            Use(ref operand) => self.eval_operand(operand)?.into(),

            CopyForDeref(place) => self.eval_place(place)?.into(),

            BinaryOp(bin_op, box (ref left, ref right)) => {
                let left = self.eval_operand(left)?;
                let left = self.use_ecx(|this| this.ecx.read_immediate(&left))?;

                let right = self.eval_operand(right)?;
                let right = self.use_ecx(|this| this.ecx.read_immediate(&right))?;

                let val =
                    self.use_ecx(|this| this.ecx.wrapping_binary_op(bin_op, &left, &right))?;
                val.into()
            }

            CheckedBinaryOp(bin_op, box (ref left, ref right)) => {
                let left = self.eval_operand(left)?;
                let left = self.use_ecx(|this| this.ecx.read_immediate(&left))?;

                let right = self.eval_operand(right)?;
                let right = self.use_ecx(|this| this.ecx.read_immediate(&right))?;

                let (val, overflowed) =
                    self.use_ecx(|this| this.ecx.overflowing_binary_op(bin_op, &left, &right))?;
                let overflowed = ImmTy::from_bool(overflowed, self.tcx);
                Value::Aggregate {
                    variant: VariantIdx::new(0),
                    fields: [Value::from(val), overflowed.into()].into_iter().collect(),
                }
            }

            UnaryOp(un_op, ref operand) => {
                let operand = self.eval_operand(operand)?;
                let val = self.use_ecx(|this| this.ecx.read_immediate(&operand))?;

                let val = self.use_ecx(|this| this.ecx.wrapping_unary_op(un_op, &val))?;
                val.into()
            }

            Aggregate(ref kind, ref fields) => Value::Aggregate {
                fields: fields
                    .iter()
                    .map(|field| self.eval_operand(field).map_or(Value::Uninit, Value::Immediate))
                    .collect(),
                variant: match **kind {
                    AggregateKind::Adt(_, variant, _, _, _) => variant,
                    AggregateKind::Array(_)
                    | AggregateKind::Tuple
                    | AggregateKind::Closure(_, _)
                    | AggregateKind::Coroutine(_, _)
                    | AggregateKind::CoroutineClosure(_, _) => VariantIdx::new(0),
                },
            },

            Repeat(ref op, n) => {
                trace!(?op, ?n);
                return None;
            }

            Len(place) => {
                let len = match self.get_const(place)? {
                    Value::Immediate(src) => src.len(&self.ecx).ok()?,
                    Value::Aggregate { fields, .. } => fields.len() as u64,
                    Value::Uninit => match place.ty(self.local_decls(), self.tcx).ty.kind() {
                        ty::Array(_, n) => n.try_eval_target_usize(self.tcx, self.param_env)?,
                        _ => return None,
                    },
                };
                ImmTy::from_scalar(Scalar::from_target_usize(len, self), layout).into()
            }

            Ref(..) | AddressOf(..) => return None,

            NullaryOp(ref null_op, ty) => {
                let op_layout = self.use_ecx(|this| this.ecx.layout_of(ty))?;
                let val = match null_op {
                    NullOp::SizeOf => op_layout.size.bytes(),
                    NullOp::AlignOf => op_layout.align.abi.bytes(),
                    NullOp::OffsetOf(fields) => {
                        op_layout.offset_of_subfield(self, fields.iter()).bytes()
                    }
                    NullOp::DebugAssertions => return None,
                };
                ImmTy::from_scalar(Scalar::from_target_usize(val, self), layout).into()
            }

            ShallowInitBox(..) => return None,

            Cast(ref kind, ref value, to) => match kind {
                CastKind::IntToInt | CastKind::IntToFloat => {
                    let value = self.eval_operand(value)?;
                    let value = self.ecx.read_immediate(&value).ok()?;
                    let to = self.ecx.layout_of(to).ok()?;
                    let res = self.ecx.int_to_int_or_float(&value, to).ok()?;
                    res.into()
                }
                CastKind::FloatToFloat | CastKind::FloatToInt => {
                    let value = self.eval_operand(value)?;
                    let value = self.ecx.read_immediate(&value).ok()?;
                    let to = self.ecx.layout_of(to).ok()?;
                    let res = self.ecx.float_to_float_or_int(&value, to).ok()?;
                    res.into()
                }
                CastKind::Transmute => {
                    let value = self.eval_operand(value)?;
                    let to = self.ecx.layout_of(to).ok()?;
                    // `offset` for immediates only supports scalar/scalar-pair ABIs,
                    // so bail out if the target is not one.
                    match (value.layout.abi, to.abi) {
                        (Abi::Scalar(..), Abi::Scalar(..)) => {}
                        (Abi::ScalarPair(..), Abi::ScalarPair(..)) => {}
                        _ => return None,
                    }

                    value.offset(Size::ZERO, to, &self.ecx).ok()?.into()
                }
                _ => return None,
            },

            Discriminant(place) => {
                let variant = match self.get_const(place)? {
                    Value::Immediate(op) => {
                        let op = op.clone();
                        self.use_ecx(|this| this.ecx.read_discriminant(&op))?
                    }
                    Value::Aggregate { variant, .. } => *variant,
                    Value::Uninit => return None,
                };
                let imm = self.use_ecx(|this| {
                    this.ecx.discriminant_for_variant(
                        place.ty(this.local_decls(), this.tcx).ty,
                        variant,
                    )
                })?;
                imm.into()
            }
        };
        trace!(?val);

        *self.access_mut(dest)? = val;

        Some(())
    }
}

impl<'tcx> Visitor<'tcx> for ConstPropagator<'_, 'tcx> {
    fn visit_body(&mut self, body: &Body<'tcx>) {
        while let Some(bb) = self.worklist.pop() {
            if !self.visited_blocks.insert(bb) {
                continue;
            }

            let data = &body.basic_blocks[bb];
            self.visit_basic_block_data(bb, data);
        }
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        self.super_operand(operand, location);
    }

    fn visit_constant(&mut self, constant: &ConstOperand<'tcx>, location: Location) {
        trace!("visit_constant: {:?}", constant);
        self.super_constant(constant, location);
        self.eval_constant(constant);
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        self.super_assign(place, rvalue, location);

        let Some(()) = self.check_rvalue(rvalue, location) else { return };

        match self.can_const_prop[place.local] {
            // Do nothing if the place is indirect.
            _ if place.is_indirect() => {}
            ConstPropMode::NoPropagation => self.ensure_not_propagated(place.local),
            ConstPropMode::OnlyInsideOwnBlock | ConstPropMode::FullConstProp => {
                if self.eval_rvalue(rvalue, place).is_none() {
                    // Const prop failed, so erase the destination, ensuring that whatever happens
                    // from here on, does not know about the previous value.
                    // This is important in case we have
                    // ```rust
                    // let mut x = 42;
                    // x = SOME_MUTABLE_STATIC;
                    // // x must now be uninit
                    // ```
                    // FIXME: we overzealously erase the entire local, because that's easier to
                    // implement.
                    trace!(
                        "propagation into {:?} failed.
                        Nuking the entire site from orbit, it's the only way to be sure",
                        place,
                    );
                    self.remove_const(place.local);
                }
            }
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'tcx>, location: Location) {
        trace!("visit_statement: {:?}", statement);

        // We want to evaluate operands before any change to the assigned-to value,
        // so we recurse first.
        self.super_statement(statement, location);

        match statement.kind {
            StatementKind::SetDiscriminant { ref place, variant_index } => {
                match self.can_const_prop[place.local] {
                    // Do nothing if the place is indirect.
                    _ if place.is_indirect() => {}
                    ConstPropMode::NoPropagation => self.ensure_not_propagated(place.local),
                    ConstPropMode::FullConstProp | ConstPropMode::OnlyInsideOwnBlock => {
                        match self.access_mut(place) {
                            Some(Value::Aggregate { variant, .. }) => *variant = variant_index,
                            _ => self.remove_const(place.local),
                        }
                    }
                }
            }
            StatementKind::StorageLive(local) => {
                self.remove_const(local);
            }
            StatementKind::StorageDead(local) => {
                self.remove_const(local);
            }
            _ => {}
        }
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        self.super_terminator(terminator, location);
        match &terminator.kind {
            TerminatorKind::Assert { expected, ref msg, ref cond, .. } => {
                self.check_assertion(*expected, msg, cond, location);
            }
            TerminatorKind::SwitchInt { ref discr, ref targets } => {
                if let Some(ref value) = self.eval_operand(discr)
                    && let Some(value_const) = self.use_ecx(|this| this.ecx.read_scalar(value))
                    && let Ok(constant) = value_const.try_to_int()
                    && let Ok(constant) = constant.to_bits(constant.size())
                {
                    // We managed to evaluate the discriminant, so we know we only need to visit
                    // one target.
                    let target = targets.target_for_value(constant);
                    self.worklist.push(target);
                    return;
                }
                // We failed to evaluate the discriminant, fallback to visiting all successors.
            }
            // None of these have Operands to const-propagate.
            TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Drop { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::Call { .. }
            | TerminatorKind::InlineAsm { .. }
            // NOTE(jhilton): It might be possible to const-eval a Reattach if you can evalute the entire basic block?
            | TerminatorKind::Reattach { .. }
            | TerminatorKind::Detach { .. }
            | TerminatorKind::Sync { .. } => {}
        }

        self.worklist.extend(terminator.successors());
    }

    fn visit_basic_block_data(&mut self, block: BasicBlock, data: &BasicBlockData<'tcx>) {
        self.super_basic_block_data(block, data);

        // We remove all Locals which are restricted in propagation to their containing blocks and
        // which were modified in the current block.
        // Take it out of the ecx so we can get a mutable reference to the ecx for `remove_const`.
        let mut written_only_inside_own_block_locals =
            std::mem::take(&mut self.written_only_inside_own_block_locals);

        // This loop can get very hot for some bodies: it check each local in each bb.
        // To avoid this quadratic behaviour, we only clear the locals that were modified inside
        // the current block.
        // The order in which we remove consts does not matter.
        #[allow(rustc::potential_query_instability)]
        for local in written_only_inside_own_block_locals.drain() {
            debug_assert_eq!(self.can_const_prop[local], ConstPropMode::OnlyInsideOwnBlock);
            self.remove_const(local);
        }
        self.written_only_inside_own_block_locals = written_only_inside_own_block_locals;

        if cfg!(debug_assertions) {
            for (local, &mode) in self.can_const_prop.iter_enumerated() {
                match mode {
                    ConstPropMode::FullConstProp => {}
                    ConstPropMode::NoPropagation | ConstPropMode::OnlyInsideOwnBlock => {
                        self.ensure_not_propagated(local);
                    }
                }
            }
        }
    }
}

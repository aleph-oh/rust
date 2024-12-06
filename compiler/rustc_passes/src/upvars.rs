//! Upvar (closure capture) collection from cross-body HIR uses of `Res::Local`s.

use rustc_data_structures::fx::{FxHashSet, FxIndexMap};
use rustc_hir as hir;
use rustc_hir::def::Res;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self, HirId};
use rustc_middle::query::Providers;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

pub fn provide(providers: &mut Providers) {
    providers.upvars_mentioned = |tcx, def_id| {
        println!("upvars_mentioned provider");
        if !tcx.is_closure_like(def_id) {
            return None;
        }
        println!("OHON");
        let local_def_id = def_id.expect_local();
        println!("sad");
        let body = tcx.hir().body(tcx.hir().maybe_body_owned_by(local_def_id)?);
        println!("sad2");
        let mut local_collector = LocalCollector::default();
        println!("sad3");
        local_collector.visit_body(body);
        println!("what the heck");
        let mut capture_collector = CaptureCollector {
            tcx,
            locals: &local_collector.locals,
            upvars: FxIndexMap::default(),
        };
        capture_collector.visit_body(body);
        // println!("what the heck2");

        if !capture_collector.upvars.is_empty() {
            // println!("what the heck3");
            Some(tcx.arena.alloc(capture_collector.upvars))
        } else {
            println!("providers.upvars_mentioned capture_collector.upvars.is_empty");
            None
        }
    };
}

#[derive(Default)]
struct LocalCollector {
    // FIXME(eddyb) perhaps use `ItemLocalId` instead?
    locals: FxHashSet<HirId>,
}

impl<'tcx> Visitor<'tcx> for LocalCollector {
    fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
        println!("LocalCollector visit_pat");
        if let hir::PatKind::Binding(_, hir_id, ..) = pat.kind {
            println!("LocalCollector visit_pat self.locals.insert()");
            self.locals.insert(hir_id);
        }
        intravisit::walk_pat(self, pat);
    }
}

struct CaptureCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    locals: &'a FxHashSet<HirId>,
    upvars: FxIndexMap<HirId, hir::Upvar>,
}

impl CaptureCollector<'_, '_> {
    fn visit_local_use(&mut self, var_id: HirId, span: Span) {
        println!("CaptureCollector visit_local_use");
        if !self.locals.contains(&var_id) {
            println!("CaptureCollector contains(&var_id)");
            self.upvars.entry(var_id).or_insert(hir::Upvar { span });
        }
    }
}

impl<'tcx> Visitor<'tcx> for CaptureCollector<'_, 'tcx> {
    fn visit_path(&mut self, path: &hir::Path<'tcx>, _: hir::HirId) {
        println!("CaptureCollector visit_path");
        if let Res::Local(var_id) = path.res {
            println!("CaptureCollector inside");
            self.visit_local_use(var_id, path.span);
        }

        intravisit::walk_path(self, path);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        println!("CaptureCollector visit_expr");
        if let hir::ExprKind::Closure(closure) = expr.kind {
            println!("CaptureCollector visit_expr2");
            if let Some(upvars) = self.tcx.upvars_mentioned(closure.def_id) {
                println!("CaptureCollector visit_expr3");
                // Every capture of a closure expression is a local in scope,
                // that is moved/copied/borrowed into the closure value, and
                // for this analysis they are like any other access to a local.
                //
                // E.g. in `|b| |c| (a, b, c)`, the upvars of the inner closure
                // are `a` and `b`, and while `a` is not directly used in the
                // outer closure, it needs to be an upvar there too, so that
                // the inner closure can take it (from the outer closure's env).
                for (&var_id, upvar) in upvars {
                    self.visit_local_use(var_id, upvar.span);
                }
            }
        }

        intravisit::walk_expr(self, expr);
    }
}

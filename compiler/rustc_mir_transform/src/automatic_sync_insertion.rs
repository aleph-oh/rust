/// This pass inserts a sync before every return terminator in a function that contains a detach.
/// We need this to have the correct behavior: we need to make sure that functions with detaches
/// always end with only a single task.
use rustc_middle::mir::{self, MirPass};
use rustc_middle::ty::TyCtxt;

/// Returns true if the given body contains a detach, which implies that there should be a sync before the return.
/// We care about checking this rather than inserting a sync before all returns regardless of the presence of detach
/// because we don't want to break tests that depend on MIR or LLVM IR looking a certain way.
pub fn body_contains_detach<'a, 'tcx>(body: &'a mir::Body<'tcx>) -> bool {
    body.basic_blocks.iter().any(|bb| {
        matches!(bb.terminator(), mir::Terminator { kind: mir::TerminatorKind::Detach { .. }, .. })
    })
}

pub struct InsertSyncs;

impl<'tcx> MirPass<'tcx> for InsertSyncs {
    fn run_pass(&self, _tcx: TyCtxt<'_>, body: &mut mir::Body<'tcx>) {
        trace!("Running InsertSyncs on {:?}", body.source);
        if !body_contains_detach(body) {
            return;
        }

        trace!("Found detach in {:?}, inserting syncs", body.source);
        let mut new_blocks = body.basic_blocks.clone();
        // Now that we know this is the case, we want to make a basic block before every return terminator.
        body.basic_blocks.iter_enumerated().for_each(|(bb, bb_data)| {
            if let mir::TerminatorKind::Return = bb_data.terminator().kind {
                // First, we have to create a new block to return instead. Then, we need this block to end in a sync
                // that leads to the returning block.
                let return_block = mir::BasicBlockData {
                    statements: vec![],
                    terminator: Some(mir::Terminator {
                        source_info: bb_data.terminator().source_info,
                        kind: mir::TerminatorKind::Return,
                    }),
                    is_cleanup: false,
                    is_parallel_loop_header: false,
                };
                let target = new_blocks.as_mut().push(return_block);
                let new_bb_data =
                    new_blocks.as_mut().get_mut(bb).expect("block should exist in cloned blocks!");
                new_bb_data.terminator_mut().kind = mir::TerminatorKind::Sync { target };
            }
        });

        // Now we finalize our changes by replacing the basic blocks with the new ones that sync before returning.
        body.basic_blocks = new_blocks;
    }
}

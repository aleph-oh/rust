#![feature(cilk)]
// This test checks that cilk_scope emits tapir_runtime_start and tapir_runtime_end
// intrinsic calls while lowering cilk_scope.

// compile-flags: -C panic=abort
// no-prefer-dynamic

// EMIT_MIR scope_emits_intrinsics.fn0.built.after.mir
pub fn fn0() -> bool {
    // CHECK: tapir_runtime_start
    // CHECK: tapir_runtime_end
    let x = cilk_scope { true };
    x
}

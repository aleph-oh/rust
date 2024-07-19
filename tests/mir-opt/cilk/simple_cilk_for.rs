#![feature(cilk)]
// This tests that a simple cilk_for doesn't break from within the spawned task.

// compile-flags: -C panic=abort
// no-prefer-dynamic

use std::sync::atomic::AtomicU64;

// EMIT_MIR simple_cilk_for.fn0.built.after.mir
pub fn fn0() {
    let sum: AtomicU64 = AtomicU64::new(0);
    cilk_for i in 1..10 {
        sum.fetch_add(i, std::sync::atomic::Ordering::Relaxed);
    }
}

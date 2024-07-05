#![feature(cilk)]
// This tests that a simple cilk_for doesn't break from within the spawned task.

// compile-flags: -C panic=abort -C no-prepopulate-passes
// no-prefer-dynamic

use std::sync::atomic::AtomicU64;

pub fn main() {
    let sum: AtomicU64 = AtomicU64::new(0);
    cilk_for i in 1..10 {
        sum.fetch_add(i, std::sync::atomic::Ordering::Relaxed);
    }
    assert_eq!(45, sum.into_inner());
}

// CHECK: !tapir.loop.spawn.strategy

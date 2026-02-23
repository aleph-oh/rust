
#![feature(cilk)]
// This tests that a simple cilk_for performs loop spawning.

// compile-flags: -C panic=abort -O
// no-prefer-dynamic

use std::sync::atomic::AtomicU64;

pub fn main() {
    let sum: AtomicU64 = AtomicU64::new(0);
    cilk_for i in 1..10 {
        sum.fetch_add(i, std::sync::atomic::Ordering::Relaxed);
    }
    assert_eq!(45, sum.into_inner());
}

// We expect to see this substring somewhere because it indicates that we have found a basic block
// which resulted from loop spawning.
// CHECK: .ls1

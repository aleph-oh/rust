#![feature(cilk)]
// Tests that a cilk_for loop with a return in it fails to compile.

// known-bug: unknown
// compile-flags: -C panic=abort
// no-prefer-dynamic

use std::sync::atomic::AtomicU64;

fn main() {
    let sum: AtomicU64 = AtomicU64::new(0);
    cilk_for i in 1..10 {
        if i == 11 {
            return;
        }
        sum.fetch_add(i, std::sync::atomic::Ordering::Relaxed);
    }
    assert_eq!(sum.into_inner(), 45);
}

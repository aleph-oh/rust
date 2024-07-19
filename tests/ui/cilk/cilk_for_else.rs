#![feature(cilk)]
// Tests a simple cilk_for loop with an else arm to show that it errors.

// compile-flags: -C panic=abort
// no-prefer-dynamic

use std::sync::atomic::AtomicU64;

fn main() {
    let sum: AtomicU64 = AtomicU64::new(0);
    cilk_for i in 1..10 {
        sum.fetch_add(i, std::sync::atomic::Ordering::Relaxed);
    } else { //~ ERROR: `for...else` loops are not supported
        panic!("shouldn't get here!");
    }
    assert_eq!(sum.into_inner(), 45);
}

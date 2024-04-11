#![feature(cilk)]
// Tests that values used in a spawned block must be Sync since they can be accessed in parallel.
// build-pass
// known-bug: unknown
// compile-flags: -C panic=abort

use std::cell::RefCell;
use std::rc::Rc;

fn main() {
    let x = Rc::new(RefCell::new(1_usize));
    // Rc<T> is not Sync so we can't use it here.
    cilk_spawn { let x = Rc::clone(&x); x.replace_with(|n| *n + 1) };
}

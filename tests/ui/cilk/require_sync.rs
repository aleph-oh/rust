#![feature(cilk)]
// Tests that values used in a spawned block must be Sync since they can be accessed in parallel.
// Currently fails because we don't check that variables have the right traits for how they're
// used in spawned blocks.

// known-bug: unknown
// compile-flags: -C panic=abort
// no-prefer-dynamic

use std::cell::RefCell;
use std::rc::Rc;

fn main() {
    let x = Rc::new(RefCell::new(1_usize));
    // Rc<T> is not Sync so we can't use it here.
    cilk_spawn { let x = Rc::clone(&x); x.replace_with(|n| *n + 1) };
}

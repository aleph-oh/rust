#![feature(cilk)]
// Check what happens when using cilk_spawn in a const context.

// run-pass
// compile-flags: -C panic=abort
// no-prefer-dynamic

const fn f() -> usize {
    cilk_spawn { let x = 3; x }
}

fn main() {
    assert_eq!(f(), 3);
}

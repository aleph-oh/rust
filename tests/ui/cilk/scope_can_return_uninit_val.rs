#![feature(cilk)]
// Tests that scope can return an uninitialized variable.

// build-pass
// compile-flags: -C panic=abort
// no-prefer-dynamic

fn main() {
    let x = cilk_scope {
        cilk_spawn { 5 }
    };
    assert_eq!(x, 5);
}

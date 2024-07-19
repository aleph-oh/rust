#![feature(cilk)]
// Tests that breaking from a cilk_spawn is not allowed.

// known-bug: unknown
// compile-flags: -C panic=abort
// no-prefer-dynamic

fn main() {
    for _ in 0..5 {
        cilk_spawn { break; };
    }
}

#![feature(cilk)]
// Tests that returning from a cilk_spawn is not allowed.

// known-bug: unknown
// compile-flags: -C panic=abort
// no-prefer-dynamic

fn main() {
    cilk_spawn { return 5; };
}

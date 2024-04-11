#![feature(cilk)]
// Check what happens when using cilk_spawn in a const context.
// build-pass
// compile-flags: -C panic=abort

const fn f() {
    cilk_spawn { let x = 3; x };
}

fn main() {}

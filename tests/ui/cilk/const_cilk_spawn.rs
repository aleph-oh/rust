#![feature(cilk)]
// Check what happens when using cilk_spawn in a const context.
// build-pass

const fn f() {
    cilk_spawn { let x = 3; x };
}

fn main() {}

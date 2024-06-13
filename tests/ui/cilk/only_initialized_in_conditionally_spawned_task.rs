#![feature(cilk)]
// Tests that when we sync conditionally spawned tasks, the liveness analysis correctly considers
// the variables uninitialized.

// compile-flags: -C panic=abort
// no-prefer-dynamic

fn f() -> usize {
    let y;
    if true {
        cilk_spawn { y = 1; };
    }
    cilk_sync;
    y + 1
    //~^ ERROR used binding `y` is possibly-uninitialized [E0381]
}

fn main() {
}

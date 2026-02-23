#![feature(cilk)]
// Tests that when we sync conditionally spawned tasks, the liveness analysis correctly considers
// the variables re-written to. In conjunction with the other tests for conditionally spawned tasks,
// this should restrict implementations only to those which accurately track which tasks are synced
// at a sync.

// compile-flags: -C panic=abort
// no-prefer-dynamic

fn f() -> usize {
    let y = 5;
    if true {
        cilk_spawn { y = 1; };
    //~^ ERROR cannot assign twice to immutable variable `y` [E0384]
    }
    cilk_sync;
    y + 1
}

fn main() {
}

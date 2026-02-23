#![feature(cilk)]
// Tests that when all conditional spawns initialize a place, that place is considered initialized.
// This currently fails because although the sync will sync *some* task that initializes y, no
// particular task is known to be synced. Solutions will involve changing the liveness analysis
// in more involved ways.

// known-bug: unknown
// compile-flags: -C panic=abort
// no-prefer-dynamic

fn f() -> usize {
    let y;
    if true {
        cilk_spawn { y = 1; };
    } else {
        cilk_spawn { y = 2; };
    }
    cilk_sync;
    y + 1
}

fn main() {
}

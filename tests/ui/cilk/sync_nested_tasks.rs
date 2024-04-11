#![feature(cilk)]
// Tests that when we sync nested tasks, the liveness analysis correctly considers the variables
// defined in the nested task as live.
// build-pass
// compile-flags: -C panic=abort

fn f() -> usize {
    let y;
    let x = cilk_spawn { cilk_spawn { y = 1 }; 2 };
    cilk_sync;
    x + y
}

fn main() {}

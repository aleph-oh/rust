#![feature(cilk)]
// Tests that compilation fails when a value is returned from a spawned block before
// a sync runs.

fn main() {
    let x = { 
        let y = cilk_spawn { 1 };
        y
//~^ ERROR: used binding `y` is possibly-uninitialized [E0381]
    };
}
#![feature(cilk)]
// Tests that matching on a spawned expression gives an error.

fn main() {
    let x: Option<usize> = cilk_spawn { None };
    match x {
//~^ ERROR used binding `x` is possibly-uninitialized [E0381]
        Some(x) => {}
        None => {}
    }
}

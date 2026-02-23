#![feature(cilk)]
// Tests that when a variable is declared in a spawned block, it's not usable outside
// that spawned block.
fn main() {
    let _ = cilk_spawn { let y = 5; y };
    println!("y={}", y);
//~^ ERROR cannot find value `y` in this scope [E0425]
}

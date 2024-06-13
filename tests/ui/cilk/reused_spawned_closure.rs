#![feature(cilk)]
// Checks that spawning a closure twice is accepted.

// build-pass
// compile-flags: -C panic=abort
// no-prefer-dynamic

fn main() {
    foo();
}

fn foo(){
    let x = 5;
    let my_closure = |y| {
        println!("Hello, world! x = {x}, y = {y}");
        y + x
    };
    let z = cilk_spawn{my_closure(3)};
    let w = cilk_spawn{my_closure(10)};
    cilk_sync;
    println!("x + y1 = z = {z}");
    println!("x + y2 = w = {w}");
}

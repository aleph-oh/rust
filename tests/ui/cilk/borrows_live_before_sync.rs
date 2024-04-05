#![feature(cilk)]
// Tests that borrows are still live before a cilk_sync.
// build-pass
// known-bug: unknown

// This should be rejected since s is still referenced by the spawned block
// and there's no sync to indicate that the borrow can be dropped.

fn main() {
    let mut s = String::from("hello");
    cilk_spawn {
        println!("{}", &s);
    };
    s.push_str(" world");
    println!("{}", s);
}

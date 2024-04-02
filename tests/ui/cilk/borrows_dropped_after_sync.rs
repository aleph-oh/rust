// Tests that borrows are not live after the cilk_sync point.
// build-pass

// Note that this test can pass if the borrow is dropped at the end of the block being spawned
// rather than at the sync. There's another test that borrows are live before a sync.
fn main() {
    let mut s = String::from("hello");
    cilk_spawn {
        println!("{}", &s);
    };
    cilk_sync;
    s.push_str(" world");
    println!("{}", s);
}

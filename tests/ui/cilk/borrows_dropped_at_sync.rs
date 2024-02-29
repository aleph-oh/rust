// Tests that borrows are dropped at the cilk_sync point.
// build-pass

fn main() {
    let mut s = String::from("hello");
    cilk_spawn { 
        println!("{}", &s);
    };
    cilk_sync;
    s.push_str(" world");
    println!("{}", s);
}

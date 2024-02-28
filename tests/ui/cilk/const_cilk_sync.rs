// build-pass
// Check what happens when using cilk_sync in a const context.
const fn f() {
    cilk_sync;
}

fn main() {}

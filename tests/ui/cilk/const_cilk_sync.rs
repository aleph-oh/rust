// Check what happens when using cilk_sync in a const context.
// build-pass

const fn f() {
    cilk_sync;
}

fn main() {}

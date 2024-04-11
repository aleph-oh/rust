#![feature(cilk)]
// Check what happens when using cilk_sync in a const context.
//@ build-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

const fn f() {
    cilk_sync;
}

fn main() {}

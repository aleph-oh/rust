#![feature(cilk)]
// Checks that a simple Cilk program compiles, with type ascription.

//@ build-pass
//@ compile-flags: -C panic=abort
//@ no-prefer-dynamic

fn fib(n: usize) -> usize {
    if n <= 1 {
        return n;
    }
    let x: usize = cilk_spawn { fib(n - 1) };
    let y: usize = fib(n - 2);
    cilk_sync;
    x + y
}

fn main() {}

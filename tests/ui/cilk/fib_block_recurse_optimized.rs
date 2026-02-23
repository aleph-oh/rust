#![feature(cilk)]
// Checks that a simple Cilk program compiles.

// run-pass
// compile-flags: -C panic=abort -O
// no-prefer-dynamic

fn fib(n: usize) -> usize {
    if n <= 1 {
        return n;
    }
    let x = cilk_spawn { fib(n - 1) };
    let y = fib(n - 2);
    cilk_sync;
    x + y
}

fn main() {
    let n = 10;
    let result = fib(n);
    assert_eq!(result, 55);
}

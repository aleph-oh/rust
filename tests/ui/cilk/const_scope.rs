#![feature(cilk)]
// Tests that cilk_scope can be used in a const context.

// run-pass
// compile-flags: -C panic=abort
// no-prefer-dynamic

const fn fib(n: u8) -> usize {
    if n <= 1 {
        return n as usize;
    }

    cilk_scope {
        let x = cilk_spawn { fib(n - 1) };
        let y = fib(n - 2);
        cilk_sync;
        x + y
    }
}

fn main() {
    assert_eq!(fib(10), 55);
}

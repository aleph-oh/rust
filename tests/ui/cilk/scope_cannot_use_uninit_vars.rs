#![feature(cilk)]
// Tests that scope can't return a value resulting from uninitialized variables.

// compile-flags: -C panic=abort
// no-prefer-dynamic

fn fib(n: u8) -> usize {
    if n <= 1 {
        return n as usize;
    }

    cilk_scope {
        let x = cilk_spawn { fib(n - 1) };
        let y = fib(n - 2);
        x + y
    //~^ ERROR used binding `x` is possibly-uninitialized [E0381]
    }
}

fn main() {
    assert_eq!(fib(10), 55);
}

// Check what happens when using Cilk keywords in a const context.
// known-bug: unknown

const fn fib(n: usize) -> usize {
    if n <= 1 {
        return n;
    }

    let x = cilk_spawn { fib(n - 1) };
    let y = fib(n - 2);
    cilk_sync;
    x + y
}

fn main() {}

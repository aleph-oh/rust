// Checks that a simple Cilk program compiles.
// known-bug: unknown

fn fib(n: usize) -> usize {
    if n <= 1 {
        return n;
    }
    let x = cilk_spawn { fib(n - 1) };
    let y = fib(n - 2);
    cilk_sync;
    x + y
}

fn main() {}

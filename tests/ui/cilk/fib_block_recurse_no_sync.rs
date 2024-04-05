#![feature(cilk)]
// Checks that a cilk program without a sync reports an uninitialized variable error.

fn fib(n: usize) -> usize {
    if n <= 1 {
        return n;
    }
    let x = cilk_spawn { fib(n - 1) };
    let y = fib(n - 2);
    x + y
//~^ ERROR used binding `x` is possibly-uninitialized [E0381]
}

fn main() {

}

fn fib(n: usize) -> usize {
    if n <= 1 {
        return n;
    }
    let x = cilk_spawn { fib(n - 1) };
//~^ ERROR used binding `x` is possibly-uninitialized [E0381]
    let y = fib(n - 2);
    x + y
}

fn main() {

}

#![feature(cilk)]

// compile-flags: -O -Cpanic=abort -Cno-prepopulate-passes
// no-prefer-dynamic
pub fn fib(n: u8) -> usize {
    if n <= 1 {
        return n as usize;
    }

    cilk_scope {
        // CHECK: llvm.tapir.runtime.start
        // CHECK: detach
        let x = cilk_spawn { fib(n - 1) };
        // CHECK: reattach
        let y = fib(n - 2);
        // CHECK: sync
        cilk_sync;
        x + y
    }
    // CHECK: llvm.tapir.runtime.stop
}

fn main() {
    assert_eq!(fib(10), 55);
}

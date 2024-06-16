#![feature(cilk)]
// Reproduces internal compiler error with consume_iter from Rayon code.
// At some point we would expect this to fail since it has concurrent
// mutable access to the iterator, so this is marked as known-bug.

// known-bug: unknown
// compile-flags: -C panic=abort
// no-prefer-dynamic

struct Ptr<T>(*mut T);

struct Foo<T> {
    start: Ptr<T>,
    total_len: usize,
    initialized_len: usize,
}

impl<T> Foo<T> {
    fn consume_iter<I>(mut self, iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut i = iter.into_iter();
        for j in 0..self.total_len {
            cilk_spawn {
                if let Some(item) = i.next() {
                    unsafe {
                        self.start.0.add(j).write(item);
                        self.initialized_len += 1;
                    }
                }
            }
        }
        cilk_sync;
        self
    }
}

fn main() {}

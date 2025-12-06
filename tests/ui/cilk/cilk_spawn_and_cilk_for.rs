#![feature(cilk)]

// This is expected to compile and run, currently it does not compile

fn main() {
    cilk_spawn_and_cilk_for();
}
fn cilk_spawn_and_cilk_for() {
    let a: usize = 0;
    let b: usize = 10;
    let c = 100;

    let v_size = (b + 1) * c;
    let mut v = vec![0; v_size]; 

    cilk_spawn{
        for x in 0..c{
            v[b * c + x] = b * c + x
        }
    };
    cilk_sync;
    cilk_for i in a..b {
        for x in 0..c{
            v[i * c + x] = i * c + x
        }
    }
    cilk_sync;

    for i in 0..((b+1) * c){
        assert!(v[i] == i, "{} != {}", v[i], i);
    }
}

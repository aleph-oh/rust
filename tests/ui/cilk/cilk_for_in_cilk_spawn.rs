#![feature(cilk)]

// This is expected to compile and run, currently it does not compile

fn main() {
    cilk_for_in_cilk_spawn();
}
fn cilk_for_in_cilk_spawn() {
    let a: usize = 0;
    let b: usize = 10;
    let c = 100;

    let v_size = b * c;
    let mut v = vec![0; v_size]; 

    cilk_spawn{
        cilk_for i in a..b {
        for x in 0..c{
            v[i * c + x] = i * c + x
        }
        }
        cilk_sync;
    };
    cilk_sync;

    for i in 0..(b * c){
        assert!(v[i] == i, "{} != {}", v[i], i);
    }
}
#![feature(cilk)]
use std::time::Instant;
fn main(){
    cilk_for_for();
}

fn cilk_for_for(){
    let a: usize = 0;
    let b: usize = 1000;
    let c = 1000;

    let v_size = (b-a) * c;
    let mut v = vec![0; v_size]; 
    let start = Instant::now();

    cilk_for i in a..b {
        for x in 0..c{
            // assuming a == 0
            v[i * c + x] = i * c + x
        }
    }
    let duration = start.elapsed();
    println!("Time elapsed: {:?}", duration);

    for i in 0..((b-a) * c){
        assert!(v[i] == i, "{} != {}", v[i], i);
    }
}

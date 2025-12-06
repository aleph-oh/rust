#![feature(cilk)]
fn main(){
    nested_cilk_for();
}

// -O3 does not compile
fn nested_cilk_for(){
    let b: usize = 10;
    let c: usize = 100;
    let v_size = b * c;
    let mut v = vec![0; v_size]; 
    cilk_for i in a..b {
        cilk_for x in a..c{
            v[i * c + x] = i * c + x
        }
    }
    for i in 0..((b) * c){
        assert!(v[i] == i, "{} != {}", v[i], i);
    }
}

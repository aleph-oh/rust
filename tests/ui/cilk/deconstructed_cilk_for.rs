#![feature(cilk)]

fn main(){
    deconstructed_cilk_for();
}

fn deconstructed_cilk_for(){ 
    let a = 0;
    let b = 10;
    let c = 100;

    let v_size = (b-a) * c;
    let mut v = vec![0; v_size]; 

    for i in a..b {
        (#[inline(always)] #[orphaning]|| {
            let my_i = i;
            cilk_spawn {
                for x in 0..c{
                    // assuming a == 0
                    v[my_i * c + x] = my_i * c + x
                }
            }
        })();
    }
    cilk_sync;

    for i in 0..((b-a) * c){
        assert!(v[i] == i, "{} != {}", v[i], i);
    }
}

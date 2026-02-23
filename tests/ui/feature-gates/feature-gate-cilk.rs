fn main() {
    cilk_spawn { 5 }; //~ ERROR cilk keywords are experimental [E0658]
    cilk_sync; //~ ERROR cilk keywords are experimental [E0658]
    cilk_scope { 5 }; //~ ERROR cilk keywords are experimental [E0658]
    cilk_for i in 0..10 {} //~ ERROR cilk keywords are experimental [E0658]
}

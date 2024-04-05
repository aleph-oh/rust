fn main() {
    cilk_spawn { 5 }; //~ ERROR cilk keywords are experimental [E0658]
    cilk_sync; //~ ERROR cilk keywords are experimental [E0658]
}
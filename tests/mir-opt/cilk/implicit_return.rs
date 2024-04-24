#![feature(cilk)]
// unit-test: InsertSyncs

// compile-flags: -C panic=abort
// no-prefer-dynamic

// skip-filecheck

// EMIT_MIR implicit_return.fn0.InsertSyncs.diff
pub fn fn0() -> bool {
    let _ = cilk_spawn { 0 };
    true
}

pub fn main() {
    println!("{}", fn0());
}

#![feature(cilk)]
// unit-test: InsertSyncs

// compile-flags: -C panic=abort
// no-prefer-dynamic

// skip-filecheck

// EMIT_MIR inserts_syncs_for_trailing_if.fn0.InsertSyncs.diff
pub fn fn0(x: bool) -> usize {
    let _ = cilk_spawn { 0 };
    if x {
        1
    } else {
        2
    }
}

pub fn main() {
    println!("{}", fn0(true));
}

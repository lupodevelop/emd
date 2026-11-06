// emd: an esoteric language written only in Unicode dashes.
// Kani harnesses: `cargo kani -p emd-parser`.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use super::*;

fn any_sym() -> Sym {
    let i: u8 = kani::any();
    kani::assume(i < 8);
    Sym::new(i).unwrap()
}

/// All 64 pairs: decoding never panics, and what decodes encodes back.
#[kani::proof]
#[kani::unwind(4)]
fn decode_never_panics_and_preserves_symbols() {
    let syms = [any_sym(), any_sym()];
    if let Ok(program) = decode(&syms) {
        let (f, o) = program[0].encode();
        assert!([f, o] == syms);
    }
}

// emd: an esoteric language written only in Unicode dashes.
// Kani harnesses on the encoding.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::*;

fn any_sym() -> Sym {
    let i: u8 = kani::any();
    kani::assume(i < 8);
    Sym(i)
}

/// On every assigned pair, `encode` inverts `decode` and vice versa.
#[kani::proof]
fn decode_encode_are_inverse() {
    let (f, o) = (any_sym(), any_sym());
    if let Some(i) = Instr::decode(f, o) {
        assert_eq!(i.encode(), (f, o));
        let (f2, o2) = i.encode();
        assert_eq!(Instr::decode(f2, o2), Some(i));
    }
}

#[kani::proof]
fn from_char_inverts_to_char() {
    let s = any_sym();
    assert_eq!(Sym::from_char(s.to_char()), Some(s));
}

#[kani::proof]
fn from_char_never_panics() {
    let c: char = kani::any();
    if let Some(s) = Sym::from_char(c) {
        assert_eq!(s.to_char(), c);
    }
}

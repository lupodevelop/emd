// emd: an esoteric language written only in Unicode dashes.
// Encoding and layout.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::*;

#[test]
fn alphabet_is_sorted_by_code_point() {
    assert!(ALPHABET.windows(2).all(|w| w[0] < w[1]));
}

#[test]
fn wrap_source_ends_every_line_it_starts() {
    assert_eq!(wrap_source(""), "");
    assert_eq!(wrap_source("-"), "-\n");
    assert_eq!(wrap_source(&"-".repeat(LINE_MAX)), format!("{}\n", "-".repeat(LINE_MAX)));
    assert_eq!(wrap_source(&"-".repeat(LINE_MAX + 1)), format!("{}\n-\n", "-".repeat(LINE_MAX)));
}

#[test]
fn decode_inverts_encode() {
    for i in Instr::all() {
        let (f, o) = i.encode();
        assert_eq!(Instr::decode(f, o), Some(i));
    }
}

#[test]
fn encode_inverts_decode_and_32_pairs_are_assigned() {
    let mut assigned = 0;
    for f in Sym::ALL {
        for o in Sym::ALL {
            if let Some(i) = Instr::decode(f, o) {
                assert_eq!(i.encode(), (f, o));
                assigned += 1;
            }
        }
    }
    // 8 constants + 4 stack + 5 arithmetic + 2 memory + 4 control + 2 I/O + 4 logic.
    assert_eq!(assigned, 32);
    assert_eq!(Instr::all().count(), 32);
}

#[test]
fn spec_examples() {
    let push1 = Instr::Push(Sym(1));
    assert_eq!(push1.source(), "-\u{2010}");
    assert_eq!(Instr::Halt.source(), "\u{2013}\u{2012}");
    assert_eq!(Instr::Write.source(), "\u{2014}\u{2010}");
    assert_eq!(Instr::Add.source(), "\u{2011}-");
}

#[test]
fn explanations_state_operand_order() {
    for (instr, text) in [
        (Instr::Sub, "a - b"),
        (Instr::Div, "a / b"),
        (Instr::Mod, "a % b"),
        (Instr::Lt, "a < b"),
        (Instr::Gt, "a > b"),
        (Instr::Jz, "if c = 0"),
        (Instr::Jnz, "if c != 0"),
    ] {
        assert!(instr.describe().contains(text), "{instr}: {}", instr.describe());
    }
}

#[test]
fn mnemonic_round_trip() {
    for i in Instr::all() {
        assert_eq!(Instr::from_mnemonic(&i.to_string()), Some(i));
    }
    assert_eq!(Instr::from_mnemonic("push 7"), Some(Instr::Push(Sym(7))));
    assert_eq!(Instr::from_mnemonic("PUSH 8"), None);
    assert_eq!(Instr::from_mnemonic("ADD 1"), None);
    assert_eq!(Instr::from_mnemonic("NOP"), None);
}

#[test]
fn a_mnemonic_takes_at_most_one_operand() {
    assert_eq!(Instr::from_mnemonic("PUSH 1 2"), None);
}

#[test]
fn a_mnemonic_needs_a_name_and_a_constant_from_0_to_7() {
    for text in ["", "PUSH x", "PUSH 8", "PUSH -1"] {
        assert_eq!(Instr::from_mnemonic(text), None, "{text:?}");
    }
}

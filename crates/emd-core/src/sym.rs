// emd: an esoteric language written only in Unicode dashes.
// The alphabet: eight dashes, and the letters that type them.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use std::fmt;

/// The eight dashes of the alphabet, in code point order.
pub const ALPHABET: [char; 8] = [
    '\u{002D}', // HYPHEN-MINUS
    '\u{2010}', // HYPHEN
    '\u{2011}', // NON-BREAKING HYPHEN
    '\u{2012}', // FIGURE DASH
    '\u{2013}', // EN DASH
    '\u{2014}', // EM DASH
    '\u{2015}', // HORIZONTAL BAR
    '\u{2212}', // MINUS SIGN
];

/// A letter per symbol, in alphabet order, for typing. Not part of the language.
pub const KEYS: [char; 8] = ['a', 's', 'd', 'f', 'g', 'h', 'j', 'k'];

/// A symbol of the alphabet, identified by its index in [`ALPHABET`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sym(pub(crate) u8);

impl Sym {
    /// All symbols, in order.
    pub const ALL: [Sym; 8] = [Sym(0), Sym(1), Sym(2), Sym(3), Sym(4), Sym(5), Sym(6), Sym(7)];

    /// The symbol at `index`, if `index < 8`.
    pub fn new(index: u8) -> Option<Sym> {
        (index < 8).then_some(Sym(index))
    }

    /// The symbol for a character, if it belongs to the alphabet.
    pub fn from_char(c: char) -> Option<Sym> {
        ALPHABET.iter().position(|&a| a == c).map(|i| Sym(i as u8))
    }

    /// The symbol typed with a letter of [`KEYS`].
    pub fn from_key(c: char) -> Option<Sym> {
        KEYS.iter().position(|&k| k == c).map(|i| Sym(i as u8))
    }

    pub fn index(self) -> u8 {
        self.0
    }

    pub fn to_char(self) -> char {
        ALPHABET[usize::from(self.0)]
    }
}

impl fmt::Display for Sym {
    /// The code point, as `U+2014`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "U+{:04X}", self.to_char() as u32)
    }
}

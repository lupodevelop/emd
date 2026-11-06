// emd: an esoteric language written only in Unicode dashes.
// Alphabet, instructions and encoding.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

mod instr;
mod source;
mod sym;

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;

pub use instr::Instr;
pub use source::{LINE_MAX, encode_program, format_program, wrap_source};
pub use sym::{ALPHABET, KEYS, Sym};

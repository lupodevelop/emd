// emd: an esoteric language written only in Unicode dashes.
// Code points to instructions. Newlines go first, wherever they fall. Nothing is corrected.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

mod doctor;

pub use doctor::{Report, doctor};

use emd_core::{Instr, LINE_MAX, Sym};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseError {
    /// Bytes that are not valid UTF-8; `offset` is the first invalid byte.
    InvalidUtf8 { offset: usize },
    /// A code point outside the alphabet; `index` counts code points from 0.
    Foreign { index: usize, ch: char },
    /// A line past [`LINE_MAX`] code points; `line` counts from 1.
    LineTooLong { line: usize },
    /// An odd number of code points, newlines not counted.
    OddLength { code_points: usize },
    /// An unassigned pair; `index` is the instruction index.
    Unassigned { index: usize, family: Sym, op: Sym },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::InvalidUtf8 { offset } => write!(f, "invalid UTF-8 at byte {offset}"),
            ParseError::Foreign { index, ch } => {
                write!(f, "code point {index} is U+{:04X}, not one of the eight dashes", *ch as u32)
            }
            ParseError::LineTooLong { line } => {
                write!(f, "line {line} is longer than {LINE_MAX} code points")
            }
            ParseError::OddLength { code_points } => {
                write!(f, "odd number of code points ({code_points}): every instruction is a pair")
            }
            ParseError::Unassigned { index, family, op } => {
                write!(f, "instruction {index} ({family} {op}) is unassigned")
            }
        }
    }
}

impl std::error::Error for ParseError {}

/// Turns the source into symbols, dropping the newlines. Stops at the first problem.
pub fn lex(src: &str) -> Result<Vec<Sym>, ParseError> {
    let mut syms = Vec::with_capacity(src.len() / 2);
    let (mut line, mut column) = (1, 0);
    for (index, ch) in src.chars().enumerate() {
        if ch == '\n' {
            line += 1;
            column = 0;
            continue;
        }
        syms.push(Sym::from_char(ch).ok_or(ParseError::Foreign { index, ch })?);
        column += 1;
        if column > LINE_MAX {
            return Err(ParseError::LineTooLong { line });
        }
    }
    Ok(syms)
}

/// Groups symbols into pairs and decodes them.
pub fn decode(syms: &[Sym]) -> Result<Vec<Instr>, ParseError> {
    if !syms.len().is_multiple_of(2) {
        return Err(ParseError::OddLength { code_points: syms.len() });
    }
    syms.as_chunks::<2>()
        .0
        .iter()
        .enumerate()
        .map(|(index, &[family, op])| {
            Instr::decode(family, op).ok_or(ParseError::Unassigned { index, family, op })
        })
        .collect()
}

/// Code points to a program.
pub fn parse(src: &str) -> Result<Vec<Instr>, ParseError> {
    decode(&lex(src)?)
}

/// Like [`lex`], from bytes not yet validated.
pub fn lex_bytes(bytes: &[u8]) -> Result<Vec<Sym>, ParseError> {
    let src = std::str::from_utf8(bytes).map_err(|e| ParseError::InvalidUtf8 { offset: e.valid_up_to() })?;
    lex(src)
}

/// Like [`parse`], from bytes not yet validated.
pub fn parse_bytes(bytes: &[u8]) -> Result<Vec<Instr>, ParseError> {
    decode(&lex_bytes(bytes)?)
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;

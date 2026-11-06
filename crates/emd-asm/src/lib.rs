// emd: an esoteric language written only in Unicode dashes.
// Assembly text to instructions, through `lexer`, `parser` and `codegen`. No I/O.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

mod codegen;
mod error;
mod lexer;
#[cfg(test)]
mod oracle;
mod parser;
#[cfg(kani)]
mod verification;

pub use codegen::push_int;
pub use error::{AsmError, Span};

use emd_core::Instr;

/// A value and where it came from.
pub(crate) struct Located<T> {
    pub span: Span,
    pub value: T,
}

/// Compiles assembly text to a program.
pub fn assemble(text: &str) -> Result<Vec<Instr>, AsmError> {
    let tokens = lexer::lex(text)?;
    let statements = parser::parse(&tokens)?;
    codegen::generate(&statements)
}

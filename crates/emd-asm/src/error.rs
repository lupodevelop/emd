// emd: an esoteric language written only in Unicode dashes.
// Compile errors, and how they look on a terminal.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use std::fmt;

/// Where something is in the source, in characters, counting from 1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub line: usize,
    pub column: usize,
    pub length: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AsmError {
    pub span: Span,
    pub message: String,
}

impl AsmError {
    /// The error with its source line. Control characters are replaced.
    pub fn render(&self, file: &str, source: &str) -> String {
        let Span { line, column, length } = self.span;
        let text: String = source
            .lines()
            .nth(line - 1)
            .unwrap_or("")
            .chars()
            .map(|c| if c.is_control() && c != '\t' { '\u{FFFD}' } else { c })
            .collect();
        // Tabs stay tabs, so carets line up.
        let indent: String = text.chars().take(column - 1).map(|c| if c == '\t' { c } else { ' ' }).collect();
        let carets = "^".repeat(length);
        let gutter = " ".repeat(line.to_string().len());
        format!(
            "error: {}\n{gutter}--> {file}:{line}:{column}\n{gutter} |\n{line} | {text}\n{gutter} | {indent}{carets}\n",
            self.message
        )
    }
}

impl fmt::Display for AsmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}, column {}: {}", self.span.line, self.span.column, self.message)
    }
}

impl std::error::Error for AsmError {}

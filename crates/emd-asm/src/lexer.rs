// emd: an esoteric language written only in Unicode dashes.
// Text to located tokens.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::{AsmError, Located, Span};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Token<'a> {
    Word(&'a str),
    /// A name followed by a colon.
    Label(&'a str),
    Int(i128),
    Str(Vec<u8>),
}

pub fn lex(text: &str) -> Result<Vec<Located<Token<'_>>>, AsmError> {
    let mut out = Vec::new();
    for (index, source) in text.lines().enumerate() {
        let mut cursor = Cursor { source, number: index + 1, byte: 0, column: 0 };
        while let Some(c) = cursor.peek() {
            if c == ';' {
                break;
            }
            if c.is_whitespace() {
                cursor.bump();
                continue;
            }
            let column = cursor.column;
            let value = cursor.token(c)?;
            out.push(Located { span: cursor.span(column), value });
        }
    }
    Ok(out)
}

/// A position in one line.
struct Cursor<'a> {
    source: &'a str,
    number: usize,
    byte: usize,
    column: usize,
}

impl<'a> Cursor<'a> {
    fn peek(&self) -> Option<char> {
        self.source[self.byte..].chars().next()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.byte += c.len_utf8();
        self.column += 1;
        Some(c)
    }

    fn bump_while(&mut self, keep: impl Fn(char) -> bool) {
        while self.peek().is_some_and(&keep) {
            self.bump();
        }
    }

    /// From a column to here, at least one character wide.
    fn span(&self, column: usize) -> Span {
        Span { line: self.number, column: column + 1, length: (self.column - column).max(1) }
    }

    fn error(&self, column: usize, message: String) -> AsmError {
        AsmError { span: self.span(column), message }
    }

    /// The token that starts with `c`, the character at the cursor.
    fn token(&mut self, c: char) -> Result<Token<'a>, AsmError> {
        let (byte, column) = (self.byte, self.column);
        self.bump();
        match c {
            '"' => self.string(column),
            '\'' => self.character(column),
            '-' | '0'..='9' => self.integer(byte, column),
            'a'..='z' | 'A'..='Z' | '_' => Ok(self.word(byte)),
            _ => Err(self.error(column, format!("unexpected character `{}`", c.escape_debug()))),
        }
    }

    fn string(&mut self, column: usize) -> Result<Token<'a>, AsmError> {
        let mut bytes = Vec::new();
        loop {
            let c = self.bump().ok_or_else(|| self.error(column, "unterminated string".into()))?;
            if c == '"' {
                return Ok(Token::Str(bytes));
            }
            let c = if c == '\\' { self.escape(column)? } else { c };
            bytes.extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes());
        }
    }

    fn character(&mut self, column: usize) -> Result<Token<'a>, AsmError> {
        let c = self.bump().ok_or_else(|| self.error(column, "unterminated character".into()))?;
        let c = if c == '\\' { self.escape(column)? } else { c };
        if self.bump() != Some('\'') {
            return Err(self.error(column, "a character literal holds one character".into()));
        }
        Ok(Token::Int(i128::from(u32::from(c))))
    }

    fn escape(&mut self, column: usize) -> Result<char, AsmError> {
        let c = self.bump().ok_or_else(|| self.error(column, "unterminated escape".into()))?;
        Ok(match c {
            'n' => '\n',
            't' => '\t',
            'r' => '\r',
            '0' => '\0',
            '\\' => '\\',
            '"' => '"',
            '\'' => '\'',
            _ => return Err(self.error(column, format!("unknown escape `\\{}`", c.escape_debug()))),
        })
    }

    fn integer(&mut self, byte: usize, column: usize) -> Result<Token<'a>, AsmError> {
        self.bump_while(|c| c.is_ascii_digit());
        let digits = &self.source[byte..self.byte];
        digits.parse().map(Token::Int).map_err(|_| self.error(column, format!("invalid integer `{digits}`")))
    }

    fn word(&mut self, byte: usize) -> Token<'a> {
        self.bump_while(|c| c.is_ascii_alphanumeric() || c == '_');
        let word = &self.source[byte..self.byte];
        if self.peek() == Some(':') {
            self.bump();
            Token::Label(word)
        } else {
            Token::Word(word)
        }
    }
}

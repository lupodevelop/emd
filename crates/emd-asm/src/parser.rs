// emd: an esoteric language written only in Unicode dashes.
// Tokens to statements. Resolves mnemonics and constants, not labels.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::lexer::Token;
use crate::{AsmError, Located, Span};
use emd_core::Instr;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement<'a> {
    Label(&'a str),
    Instr(Instr),
    /// Pushes any 64-bit integer.
    Push(i64),
    /// Pushes the offset to a label, then executes a jump instruction.
    Jump(Instr, &'a str),
}

pub fn parse<'a>(tokens: &[Located<Token<'a>>]) -> Result<Vec<Located<Statement<'a>>>, AsmError> {
    let mut parser =
        Parser { tokens, pos: 0, constants: HashMap::new(), out: Vec::with_capacity(tokens.len()) };
    while parser.pos < tokens.len() {
        parser.statement()?;
    }
    Ok(parser.out)
}

struct Parser<'t, 'a> {
    tokens: &'t [Located<Token<'a>>],
    pos: usize,
    constants: HashMap<&'a str, i64>,
    out: Vec<Located<Statement<'a>>>,
}

impl<'t, 'a> Parser<'t, 'a> {
    fn statement(&mut self) -> Result<(), AsmError> {
        let Located { span, value } = &self.tokens[self.pos];
        let span = *span;
        self.pos += 1;
        match value {
            Token::Label(name) => {
                reject_reserved(name, span)?;
                self.emit(span, Statement::Label(name));
                Ok(())
            }
            Token::Word(word) => self.instruction(word, span),
            other => Err(at(span, format!("expected an instruction, found {}", show(other)))),
        }
    }

    fn instruction(&mut self, word: &str, span: Span) -> Result<(), AsmError> {
        if word.eq_ignore_ascii_case("CONST") {
            return self.constant(span);
        }
        if word.eq_ignore_ascii_case("PUSH") {
            let value = self.value(span)?;
            self.emit(span, Statement::Push(value));
            return Ok(());
        }
        if word.eq_ignore_ascii_case("PRINT") {
            return self.print(span);
        }
        match Instr::from_mnemonic(word) {
            Some(instr @ (Instr::Load | Instr::Store)) => {
                if self.operand_follows() {
                    let value = self.value(span)?;
                    self.emit(span, Statement::Push(value));
                }
                self.emit(span, Statement::Instr(instr));
            }
            Some(instr @ (Instr::Jmp | Instr::Jz | Instr::Jnz | Instr::Call)) => {
                if self.operand_follows() {
                    let (target, target_span) = self.label_name()?;
                    self.emit(target_span, Statement::Jump(instr, target));
                } else {
                    self.emit(span, Statement::Instr(instr));
                }
            }
            Some(instr) => self.emit(span, Statement::Instr(instr)),
            None => return Err(at(span, format!("unknown instruction `{}`", word.to_ascii_uppercase()))),
        }
        Ok(())
    }

    fn constant(&mut self, span: Span) -> Result<(), AsmError> {
        let (name, name_span) = match self.next(span, "a constant name")? {
            Located { value: Token::Word(name), span } => (*name, *span),
            Located { value, span } => {
                return Err(at(*span, format!("expected a constant name, found {}", show(value))));
            }
        };
        reject_reserved(name, name_span)?;
        let value = self.value(span)?;
        if self.constants.insert(name, value).is_some() {
            return Err(at(name_span, format!("constant `{name}` defined twice")));
        }
        Ok(())
    }

    fn print(&mut self, span: Span) -> Result<(), AsmError> {
        match self.next(span, "a string")? {
            Located { value: Token::Str(bytes), .. } => {
                for &byte in bytes {
                    self.emit(span, Statement::Push(i64::from(byte)));
                    self.emit(span, Statement::Instr(Instr::Write));
                }
                Ok(())
            }
            Located { value, span } => Err(at(*span, format!("expected a string, found {}", show(value)))),
        }
    }

    fn emit(&mut self, span: Span, statement: Statement<'a>) {
        self.out.push(Located { span, value: statement });
    }

    /// The next token, which must be on the line of its instruction.
    fn next(&mut self, instruction: Span, wanted: &str) -> Result<&'t Located<Token<'a>>, AsmError> {
        match self.tokens.get(self.pos) {
            Some(located) if located.span.line == instruction.line => {
                self.pos += 1;
                Ok(located)
            }
            _ => Err(at(instruction, format!("expected {wanted}"))),
        }
    }

    /// A word on the same line is an operand unless it is a mnemonic.
    fn operand_follows(&self) -> bool {
        let Some(next) = self.tokens.get(self.pos) else { return false };
        let same_line = next.span.line == self.tokens[self.pos - 1].span.line;
        match &next.value {
            Token::Int(_) => same_line,
            Token::Word(word) => same_line && !is_mnemonic(word),
            _ => false,
        }
    }

    fn value(&mut self, instruction: Span) -> Result<i64, AsmError> {
        let Located { span, value } = self.next(instruction, "a value")?;
        match value {
            Token::Int(n) => {
                // i64::MIN is excluded: its absolute value cannot be built on the stack.
                if n.unsigned_abs() > i64::MAX as u128 {
                    return Err(at(*span, format!("{n} does not fit in 63 bits plus sign")));
                }
                Ok(*n as i64)
            }
            Token::Word(name) => self
                .constants
                .get(name)
                .copied()
                .ok_or_else(|| at(*span, format!("undefined constant `{name}`"))),
            other => Err(at(*span, format!("expected a value, found {}", show(other)))),
        }
    }

    /// The operand of a jump. Called once `operand_follows` has seen it.
    fn label_name(&mut self) -> Result<(&'a str, Span), AsmError> {
        let Located { value, span } = &self.tokens[self.pos];
        self.pos += 1;
        match value {
            Token::Word(name) => Ok((name, *span)),
            _ => Err(at(*span, format!("expected a label, found {}", show(value)))),
        }
    }
}

fn at(span: Span, message: String) -> AsmError {
    AsmError { span, message }
}

/// `JNZ halt` must have one reading.
fn reject_reserved(name: &str, span: Span) -> Result<(), AsmError> {
    if is_mnemonic(name) {
        return Err(at(span, format!("`{name}` is an instruction, not a usable name")));
    }
    Ok(())
}

fn is_mnemonic(word: &str) -> bool {
    ["PUSH", "PRINT", "CONST"].iter().any(|m| word.eq_ignore_ascii_case(m))
        || Instr::from_mnemonic(word).is_some()
}

fn show(token: &Token<'_>) -> String {
    match token {
        Token::Word(w) => format!("`{w}`"),
        Token::Label(l) => format!("label `{l}`"),
        Token::Int(n) => n.to_string(),
        Token::Str(_) => "a string".into(),
    }
}

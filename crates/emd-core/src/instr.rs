// emd: an esoteric language written only in Unicode dashes.
// Instructions: a pair of symbols is a family and an operation.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::sym::Sym;
use std::fmt;

/// A decoded instruction. `b` is the top of the stack, `a` the value below.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Instr {
    /// Pushes the constant 0 to 7 given by the symbol's index.
    Push(Sym),
    Dup,
    Drop,
    Swap,
    Over,
    /// `a b c` to `b c a`: the third value comes to the top.
    Rot,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Load,
    Store,
    Jmp,
    Jz,
    Jnz,
    Halt,
    /// Pops an offset, pushes `pc + 1` and jumps: a return address is an ordinary value.
    Call,
    /// Pops an absolute address and jumps to it.
    Ret,
    Read,
    Write,
    Eq,
    Lt,
    Gt,
    Not,
}

impl Instr {
    /// Decodes the pair (family, operation). `None` if unassigned.
    pub fn decode(family: Sym, op: Sym) -> Option<Instr> {
        use Instr::*;
        Some(match (family.0, op.0) {
            (0, _) => Push(op),
            (1, 0) => Dup,
            (1, 1) => Drop,
            (1, 2) => Swap,
            (1, 3) => Over,
            (1, 4) => Rot,
            (2, 0) => Add,
            (2, 1) => Sub,
            (2, 2) => Mul,
            (2, 3) => Div,
            (2, 4) => Mod,
            (3, 0) => Load,
            (3, 1) => Store,
            (4, 0) => Jmp,
            (4, 1) => Jz,
            (4, 2) => Jnz,
            (4, 3) => Halt,
            (4, 4) => Call,
            (4, 5) => Ret,
            (5, 0) => Read,
            (5, 1) => Write,
            (6, 0) => Eq,
            (6, 1) => Lt,
            (6, 2) => Gt,
            (6, 3) => Not,
            _ => return None,
        })
    }

    /// The pair (family, operation) of the instruction.
    pub fn encode(self) -> (Sym, Sym) {
        use Instr::*;
        let (f, o) = match self {
            Push(n) => return (Sym(0), n),
            Dup => (1, 0),
            Drop => (1, 1),
            Swap => (1, 2),
            Over => (1, 3),
            Rot => (1, 4),
            Add => (2, 0),
            Sub => (2, 1),
            Mul => (2, 2),
            Div => (2, 3),
            Mod => (2, 4),
            Load => (3, 0),
            Store => (3, 1),
            Jmp => (4, 0),
            Jz => (4, 1),
            Jnz => (4, 2),
            Halt => (4, 3),
            Call => (4, 4),
            Ret => (4, 5),
            Read => (5, 0),
            Write => (5, 1),
            Eq => (6, 0),
            Lt => (6, 1),
            Gt => (6, 2),
            Not => (6, 3),
        };
        (Sym(f), Sym(o))
    }

    /// Every assigned instruction, in code order.
    pub fn all() -> impl Iterator<Item = Instr> {
        Sym::ALL.into_iter().flat_map(|f| Sym::ALL.into_iter().filter_map(move |o| Instr::decode(f, o)))
    }

    /// The source of the instruction: two dashes.
    pub fn source(self) -> String {
        let (f, o) = self.encode();
        [f.to_char(), o.to_char()].into_iter().collect()
    }

    /// Reads a mnemonic such as `ADD` or `PUSH 3`, ignoring case.
    pub fn from_mnemonic(s: &str) -> Option<Instr> {
        use Instr::*;
        let mut parts = s.split_whitespace();
        let name = parts.next()?.to_ascii_uppercase();
        let arg = parts.next();
        if parts.next().is_some() {
            return None;
        }
        Some(match (name.as_str(), arg) {
            ("PUSH", Some(n)) => Push(Sym::new(n.parse().ok()?)?),
            (_, Some(_)) => return None,
            ("DUP", None) => Dup,
            ("DROP", None) => Drop,
            ("SWAP", None) => Swap,
            ("OVER", None) => Over,
            ("ROT", None) => Rot,
            ("ADD", None) => Add,
            ("SUB", None) => Sub,
            ("MUL", None) => Mul,
            ("DIV", None) => Div,
            ("MOD", None) => Mod,
            ("LOAD", None) => Load,
            ("STORE", None) => Store,
            ("JMP", None) => Jmp,
            ("JZ", None) => Jz,
            ("JNZ", None) => Jnz,
            ("HALT", None) => Halt,
            ("CALL", None) => Call,
            ("RET", None) => Ret,
            ("READ", None) => Read,
            ("WRITE", None) => Write,
            ("EQ", None) => Eq,
            ("LT", None) => Lt,
            ("GT", None) => Gt,
            ("NOT", None) => Not,
            _ => return None,
        })
    }
}

impl Instr {
    /// What the instruction does, in words.
    pub fn describe(self) -> String {
        use Instr::*;
        match self {
            Push(n) => return format!("push {}", n.index()),
            Dup => "duplicate the top value",
            Drop => "discard the top value",
            Swap => "swap the two top values",
            Over => "copy the second value onto the top",
            Rot => "bring the third value to the top",
            Add => "pop b, pop a, push a + b",
            Sub => "pop b, pop a, push a - b",
            Mul => "pop b, pop a, push a * b",
            Div => "pop b, pop a, push a / b truncated toward zero; fault if b = 0",
            Mod => "pop b, pop a, push a % b with the sign of a; fault if b = 0",
            Load => "pop address a, push memory[a]; fault if a < 0",
            Store => "pop address a, pop value v, memory[a] = v; fault if a < 0",
            Jmp => "pop offset, pc += offset",
            Jz => "pop offset, pop c, pc += offset if c = 0 else pc += 1",
            Jnz => "pop offset, pop c, pc += offset if c != 0 else pc += 1",
            Halt => "stop",
            Call => "pop offset, push pc + 1, pc += offset",
            Ret => "pop address, pc = address",
            Read => "read one byte from input and push it; push -1 at end of input",
            Write => "pop v, write byte v; fault if v is not in 0..=255",
            Eq => "pop b, pop a, push 1 if a = b else 0",
            Lt => "pop b, pop a, push 1 if a < b else 0",
            Gt => "pop b, pop a, push 1 if a > b else 0",
            Not => "pop a, push 1 if a = 0 else 0",
        }
        .to_string()
    }
}

impl fmt::Display for Instr {
    /// The mnemonic, such as `ADD` or `PUSH 3`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Instr::*;
        let name = match self {
            Push(n) => return write!(f, "PUSH {}", n.index()),
            Dup => "DUP",
            Drop => "DROP",
            Swap => "SWAP",
            Over => "OVER",
            Rot => "ROT",
            Add => "ADD",
            Sub => "SUB",
            Mul => "MUL",
            Div => "DIV",
            Mod => "MOD",
            Load => "LOAD",
            Store => "STORE",
            Jmp => "JMP",
            Jz => "JZ",
            Jnz => "JNZ",
            Halt => "HALT",
            Call => "CALL",
            Ret => "RET",
            Read => "READ",
            Write => "WRITE",
            Eq => "EQ",
            Lt => "LT",
            Gt => "GT",
            Not => "NOT",
        };
        f.write_str(name)
    }
}

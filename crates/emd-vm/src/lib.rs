// emd: an esoteric language written only in Unicode dashes.
// The virtual machine: the semantics of the model, with 64-bit overflow and [`Limits`] as faults.
// The last element of the stack is the top.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::Instr;
use std::collections::BTreeMap;
use std::fmt;
use std::io::{Read, Write};

/// Resource limits of the implementation. Exceeding one is a [`Fault`].
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_steps: u64,
    pub max_stack: usize,
    pub max_cells: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits { max_steps: u64::MAX, max_stack: 1 << 24, max_cells: 1 << 24 }
    }
}

/// An explicit error state. The machine stops and does not resume.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fault {
    StackUnderflow,
    DivisionByZero,
    NegativeAddress(i64),
    /// A jump or advance would take `pc` outside `0..len`.
    PcOutOfRange(i64),
    /// `WRITE` with a value outside `0..=255`.
    InvalidByte(i64),
    Overflow,
    StepLimit,
    StackLimit,
    MemoryLimit,
    Io(String),
}

impl fmt::Display for Fault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Fault::StackUnderflow => write!(f, "stack underflow"),
            Fault::DivisionByZero => write!(f, "division by zero"),
            Fault::NegativeAddress(a) => write!(f, "negative address {a}"),
            Fault::PcOutOfRange(t) => write!(f, "pc {t} is outside the program"),
            Fault::InvalidByte(v) => write!(f, "{v} is not a byte"),
            Fault::Overflow => write!(f, "64-bit overflow (implementation limit)"),
            Fault::StepLimit => write!(f, "step limit reached"),
            Fault::StackLimit => write!(f, "stack limit reached"),
            Fault::MemoryLimit => write!(f, "memory cell limit reached"),
            Fault::Io(e) => write!(f, "i/o error: {e}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Status {
    Running,
    Halted,
    Faulted(Fault),
}

/// A program in execution. A step either completes or faults and leaves the state as it was.
pub struct Vm<'p> {
    program: &'p [Instr],
    pub pc: usize,
    pub stack: Vec<i64>,
    /// Cells never written are 0.
    pub memory: BTreeMap<i64, i64>,
    pub steps: u64,
    pub limits: Limits,
    pub status: Status,
}

impl<'p> Vm<'p> {
    pub fn new(program: &'p [Instr], limits: Limits) -> Self {
        Vm {
            program,
            pc: 0,
            stack: Vec::new(),
            memory: BTreeMap::new(),
            steps: 0,
            limits,
            status: Status::Running,
        }
    }

    /// Runs until `Halted` or `Faulted`.
    pub fn run(&mut self, input: &mut dyn Read, output: &mut dyn Write) -> &Status {
        while self.status == Status::Running {
            self.step(input, output);
        }
        &self.status
    }

    /// Runs one instruction. No effect unless the machine is `Running`.
    pub fn step(&mut self, input: &mut dyn Read, output: &mut dyn Write) -> &Status {
        if self.status != Status::Running {
            return &self.status;
        }
        let result = if self.steps >= self.limits.max_steps {
            Err(Fault::StepLimit)
        } else {
            match self.program.get(self.pc) {
                None => Err(Fault::PcOutOfRange(self.pc as i64)),
                Some(&instr) => {
                    self.steps += 1;
                    self.exec(instr, input, output)
                }
            }
        };
        if let Err(fault) = result {
            self.status = Status::Faulted(fault);
        }
        &self.status
    }

    /// Checks operands, limits and destination, then changes state: a fault leaves it as it was.
    fn exec(&mut self, instr: Instr, input: &mut dyn Read, output: &mut dyn Write) -> Result<(), Fault> {
        use Instr::*;
        let next = match instr {
            Push(n) => {
                let next = self.target(1)?;
                self.push(i64::from(n.index()))?;
                next
            }
            Dup => {
                let a = self.peek(1)?;
                let next = self.target(1)?;
                self.push(a)?;
                next
            }
            Drop => {
                self.peek(1)?;
                let next = self.target(1)?;
                self.pop(1);
                next
            }
            Swap => {
                let [a, b] = self.top()?;
                let next = self.target(1)?;
                self.pop(2);
                self.stack.extend([b, a]);
                next
            }
            Over => {
                let a = self.peek(2)?;
                let next = self.target(1)?;
                self.push(a)?;
                next
            }
            Rot => {
                let [a, b, c] = self.top()?;
                let next = self.target(1)?;
                self.pop(3);
                self.stack.extend([b, c, a]);
                next
            }
            Add => self.binary(|a, b| a.checked_add(b).ok_or(Fault::Overflow))?,
            Sub => self.binary(|a, b| a.checked_sub(b).ok_or(Fault::Overflow))?,
            Mul => self.binary(|a, b| a.checked_mul(b).ok_or(Fault::Overflow))?,
            Div => self.binary(|a, b| match b {
                0 => Err(Fault::DivisionByZero),
                _ => a.checked_div(b).ok_or(Fault::Overflow),
            })?,
            Mod => self.binary(|a, b| match b {
                0 => Err(Fault::DivisionByZero),
                // `i64::MIN % -1` is 0, as in the model: nothing here can overflow.
                _ => Ok(a.wrapping_rem(b)),
            })?,
            Load => {
                let addr = self.address()?;
                let next = self.target(1)?;
                let v = self.memory.get(&addr).copied().unwrap_or(0);
                self.pop(1);
                self.stack.push(v);
                next
            }
            Store => {
                // Both operands first: underflow outranks a bad address, as in the model.
                let v = self.peek(2)?;
                let addr = self.address()?;
                if !self.memory.contains_key(&addr) && self.memory.len() >= self.limits.max_cells {
                    return Err(Fault::MemoryLimit);
                }
                let next = self.target(1)?;
                self.pop(2);
                self.memory.insert(addr, v);
                next
            }
            Jmp => {
                let off = self.peek(1)?;
                let next = self.target(off)?;
                self.pop(1);
                next
            }
            Jz | Jnz => {
                let [c, off] = self.top()?;
                let taken = if instr == Jz { c == 0 } else { c != 0 };
                let next = self.target(if taken { off } else { 1 })?;
                self.pop(2);
                next
            }
            Halt => {
                self.status = Status::Halted;
                return Ok(());
            }
            Call => {
                let off = self.peek(1)?;
                let next = self.target(off)?;
                self.pop(1);
                self.stack.push(self.pc as i64 + 1);
                next
            }
            Ret => {
                let address = self.peek(1)?;
                let next = usize::try_from(address)
                    .ok()
                    .filter(|&a| a < self.program.len())
                    .ok_or(Fault::PcOutOfRange(address))?;
                self.pop(1);
                next
            }
            Read => {
                self.room()?;
                let next = self.target(1)?;
                let mut byte = [0u8; 1];
                let v = match input.read(&mut byte) {
                    Ok(0) => -1,
                    Ok(_) => i64::from(byte[0]),
                    Err(e) => return Err(Fault::Io(e.to_string())),
                };
                self.stack.push(v);
                next
            }
            Write => {
                let v = self.peek(1)?;
                let byte = u8::try_from(v).map_err(|_| Fault::InvalidByte(v))?;
                let next = self.target(1)?;
                output.write_all(&[byte]).map_err(|e| Fault::Io(e.to_string()))?;
                self.pop(1);
                next
            }
            Eq => self.binary(|a, b| Ok(i64::from(a == b)))?,
            Lt => self.binary(|a, b| Ok(i64::from(a < b)))?,
            Gt => self.binary(|a, b| Ok(i64::from(a > b)))?,
            Not => {
                let a = self.peek(1)?;
                let next = self.target(1)?;
                self.pop(1);
                self.stack.push(i64::from(a == 0));
                next
            }
        };
        self.pc = next;
        Ok(())
    }

    /// The value at `depth` (1 = top), without removing it.
    fn peek(&self, depth: usize) -> Result<i64, Fault> {
        self.stack.len().checked_sub(depth).map(|i| self.stack[i]).ok_or(Fault::StackUnderflow)
    }

    /// The top `N` values, the top last, without removing them.
    fn top<const N: usize>(&self) -> Result<[i64; N], Fault> {
        self.stack.last_chunk().copied().ok_or(Fault::StackUnderflow)
    }

    /// Removes `n` values. Call only after `peek(n)`.
    fn pop(&mut self, n: usize) {
        self.stack.truncate(self.stack.len() - n);
    }

    fn room(&self) -> Result<(), Fault> {
        if self.stack.len() >= self.limits.max_stack {
            return Err(Fault::StackLimit);
        }
        Ok(())
    }

    fn push(&mut self, v: i64) -> Result<(), Fault> {
        self.room()?;
        self.stack.push(v);
        Ok(())
    }

    /// Binary operation: `a b` to `f(a, b)`. Returns the next pc.
    fn binary(&mut self, f: impl Fn(i64, i64) -> Result<i64, Fault>) -> Result<usize, Fault> {
        let [a, b] = self.top()?;
        let r = f(a, b)?;
        let next = self.target(1)?;
        self.pop(2);
        self.stack.push(r);
        Ok(next)
    }

    /// The address on top of the stack, if not negative.
    fn address(&self) -> Result<i64, Fault> {
        let addr = self.peek(1)?;
        if addr < 0 {
            return Err(Fault::NegativeAddress(addr));
        }
        Ok(addr)
    }

    /// The pc reached by `offset`, if inside the program. A program ends only with HALT.
    fn target(&self, offset: i64) -> Result<usize, Fault> {
        // Saturating: an offset this large is out of range, as in the model.
        let t = (self.pc as i64).saturating_add(offset);
        if t < 0 || t >= self.program.len() as i64 {
            return Err(Fault::PcOutOfRange(t));
        }
        Ok(t as usize)
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;

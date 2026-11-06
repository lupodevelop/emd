// emd: an esoteric language written only in Unicode dashes.
// Kani harnesses: one step of the machine against a specification, on i128.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use super::*;
use emd_core::Sym;
use std::io;

struct OneByte(Option<u8>);

impl Read for OneByte {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self.0.take() {
            Some(b) => {
                buf[0] = b;
                Ok(1)
            }
            None => Ok(0),
        }
    }
}

#[derive(Default)]
struct Written(Option<u8>, usize);

impl Write for Written {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.write_all(buf).map(|()| buf.len())
    }
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.1 += buf.len();
        self.0 = buf.first().copied();
        Ok(())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// A symbolic state before one step.
#[derive(Clone, Copy)]
struct Before {
    len: usize,
    pc: usize,
    steps: u64,
    depth: usize,
    stack: [i64; 3],
    cell: Option<(i64, i64)>,
    max_stack: usize,
    max_cells: usize,
    input: Option<u8>,
}

const MAX_STEPS: u64 = 4;
const CELL: i64 = 7;

fn any_before(depth: usize, with_cell: bool) -> Before {
    let (len, pc, steps): (usize, usize, u64) = (kani::any(), kani::any(), kani::any());
    kani::assume((len == 1 || len == 2) && pc < len);
    kani::assume(steps <= MAX_STEPS);
    let (max_stack, max_cells): (usize, usize) = (kani::any(), kani::any());
    kani::assume(max_stack <= 3 && depth <= max_stack);
    kani::assume(max_cells <= 2);
    // A concrete address, for `load_cell` only: STORE over a cell runs out of memory.
    let cell = if with_cell { Some((CELL, kani::any())) } else { None };
    let input = if kani::any() { Some(kani::any()) } else { None };
    Before { len, pc, steps, depth, stack: kani::any(), cell, max_stack, max_cells, input }
}

fn start<'p>(program: &'p [Instr], s: &Before) -> Vm<'p> {
    let limits = Limits { max_steps: MAX_STEPS, max_stack: s.max_stack, max_cells: s.max_cells };
    let mut vm = Vm::new(&program[..s.len], limits);
    vm.pc = s.pc;
    vm.steps = s.steps;
    vm.stack = Vec::with_capacity(4);
    for i in 0..s.depth {
        vm.stack.push(s.stack[i]);
    }
    if let Some((a, v)) = s.cell {
        vm.memory.insert(a, v);
    }
    vm
}

/// What one step does to the stack, pc, memory and streams.
struct Effect {
    pops: usize,
    pushes: [Option<i64>; 3],
    offset: i64,
    store: Option<(i64, i64)>,
    reads: bool,
    writes: Option<u8>,
}

/// The expected step, on `i128` so nothing wraps. `Ok(None)` is HALT.
/// `i64` inside enums, because Kani 0.68 crashes on `Option<i128>`.
fn spec(instr: Instr, s: &Before) -> Result<Option<Effect>, Fault> {
    use Instr::*;
    let at = |depth: usize| -> Result<i64, Fault> {
        if s.depth < depth { Err(Fault::StackUnderflow) } else { Ok(s.stack[s.depth - depth]) }
    };
    let target = |offset: i64| -> Result<(), Fault> {
        let t = s.pc as i128 + offset as i128;
        if t < 0 || t >= s.len as i128 {
            let saturated = if t > i64::MAX as i128 { i64::MAX } else { t as i64 };
            return Err(Fault::PcOutOfRange(saturated));
        }
        Ok(())
    };
    let room = || if s.depth >= s.max_stack { Err(Fault::StackLimit) } else { Ok(()) };
    let fits = |r: i128| -> Result<i64, Fault> {
        if r < i64::MIN as i128 || r > i64::MAX as i128 { Err(Fault::Overflow) } else { Ok(r as i64) }
    };
    let effect = |pops, first: Option<i64>, second: Option<i64>| Effect {
        pops,
        pushes: [first, second, None],
        offset: 1,
        store: None,
        reads: false,
        writes: None,
    };
    let binary = |r: i64| -> Result<Option<Effect>, Fault> {
        target(1)?;
        Ok(Some(effect(2, Some(r), None)))
    };
    let (second, top) = (at(2), at(1));
    Ok(Some(match instr {
        Push(n) => {
            target(1)?;
            room()?;
            // The alphabet of the model, by code point: not `Sym::index`.
            let value = match n.to_char() as u32 {
                0x2D => 0,
                0x2010 => 1,
                0x2011 => 2,
                0x2012 => 3,
                0x2013 => 4,
                0x2014 => 5,
                0x2015 => 6,
                _ => 7,
            };
            effect(0, Some(value), None)
        }
        Dup => {
            let a = top?;
            target(1)?;
            room()?;
            effect(0, Some(a), None)
        }
        Drop => {
            top?;
            target(1)?;
            effect(1, None, None)
        }
        Swap => {
            let (a, b) = (second?, top?);
            target(1)?;
            effect(2, Some(b), Some(a))
        }
        Over => {
            let a = second?;
            target(1)?;
            room()?;
            effect(0, Some(a), None)
        }
        Rot => {
            let (a, b, c) = (at(3)?, second?, top?);
            target(1)?;
            Effect { pushes: [Some(b), Some(c), Some(a)], ..effect(3, None, None) }
        }
        Add => return binary(fits(second? as i128 + top? as i128)?),
        Sub => return binary(fits(second? as i128 - top? as i128)?),
        Mul => return binary(fits(second? as i128 * top? as i128)?),
        Div | Mod => {
            let (a, b) = (second? as i128, top? as i128);
            if b == 0 {
                return Err(Fault::DivisionByZero);
            }
            // Rust's `/` and `%` on i128 truncate, like `Int.tdiv` and `Int.tmod`.
            return binary(fits(if instr == Div { a / b } else { a % b })?);
        }
        Load => {
            let a = top?;
            if a < 0 {
                return Err(Fault::NegativeAddress(a));
            }
            target(1)?;
            let v = match s.cell {
                Some((k, v)) if k == a => v,
                _ => 0,
            };
            effect(1, Some(v), None)
        }
        Store => {
            let (v, a) = (second?, top?);
            if a < 0 {
                return Err(Fault::NegativeAddress(a));
            }
            let used = if s.cell.is_some() { 1 } else { 0 };
            let is_new = !matches!(s.cell, Some((k, _)) if k == a);
            if is_new && used >= s.max_cells {
                return Err(Fault::MemoryLimit);
            }
            target(1)?;
            Effect { store: Some((a, v)), ..effect(2, None, None) }
        }
        Jmp => {
            let off = top?;
            target(off)?;
            Effect { offset: off, ..effect(1, None, None) }
        }
        Jz | Jnz => {
            let (c, off) = (second?, top?);
            let taken = if instr == Jz { c == 0 } else { c != 0 };
            let offset = if taken { off } else { 1 };
            target(offset)?;
            Effect { offset, ..effect(2, None, None) }
        }
        Halt => return Ok(None),
        Call => {
            let off = top?;
            target(off)?;
            Effect { offset: off, ..effect(1, Some(s.pc as i64 + 1), None) }
        }
        Ret => {
            let a = top?;
            if a < 0 || a >= s.len as i64 {
                return Err(Fault::PcOutOfRange(a));
            }
            Effect { offset: a - s.pc as i64, ..effect(1, None, None) }
        }
        Read => {
            room()?;
            target(1)?;
            let v = match s.input {
                Some(b) => b as i64,
                None => -1,
            };
            Effect { reads: true, ..effect(0, Some(v), None) }
        }
        Write => {
            let v = top?;
            if v < 0 || v > 255 {
                return Err(Fault::InvalidByte(v));
            }
            target(1)?;
            Effect { writes: Some(v as u8), ..effect(1, None, None) }
        }
        Eq => return binary((second? == top?) as i64),
        Lt => return binary((second? < top?) as i64),
        Gt => return binary((second? > top?) as i64),
        Not => {
            let a = top?;
            target(1)?;
            effect(1, Some((a == 0) as i64), None)
        }
    }))
}

/// Stack, pc, steps, memory and streams after a step that left them as they were.
fn assert_unchanged(vm: &Vm<'_>, s: &Before, input: &OneByte, out: &Written) {
    assert!(vm.pc == s.pc);
    assert!(vm.stack.len() == s.depth);
    for i in 0..s.depth {
        assert!(vm.stack[i] == s.stack[i]);
    }
    assert_cell(vm, s);
    assert!(input.0 == s.input);
    assert!(out.1 == 0);
}

fn assert_cell(vm: &Vm<'_>, s: &Before) {
    match s.cell {
        Some((k, v)) => {
            assert!(vm.memory.len() == 1 && vm.memory.get(&k) == Some(&v));
        }
        None => {
            assert!(vm.memory.is_empty());
        }
    }
}

/// One step from any state is exactly what `spec` says, for each field.
fn check(instr: Instr, depth: usize, with_cell: bool) {
    let program = [instr, instr];
    let s = any_before(depth, with_cell);
    // `i16` operands plus extreme dividends: wider does not finish in 25 minutes.
    if matches!(instr, Instr::Div | Instr::Mod) && depth >= 2 {
        let (a, b) = (s.stack[depth - 2], s.stack[depth - 1]);
        let small = |v: i64| v >= i16::MIN as i64 && v <= i16::MAX as i64;
        let extreme = a == i64::MIN || a == i64::MAX;
        kani::assume((small(a) && small(b)) || (extreme && b >= -2 && b <= 3));
    }
    let mut vm = start(&program, &s);
    let (mut input, mut out) = (OneByte(s.input), Written::default());
    vm.step(&mut input, &mut out);

    if s.steps >= MAX_STEPS {
        assert!(vm.status == Status::Faulted(Fault::StepLimit));
        assert!(vm.steps == s.steps);
        assert_unchanged(&vm, &s, &input, &out);
        std::mem::forget(vm);
        return;
    }
    assert!(vm.steps == s.steps + 1);
    match spec(instr, &s) {
        Err(fault) => {
            assert!(vm.status == Status::Faulted(fault));
            assert_unchanged(&vm, &s, &input, &out);
        }
        Ok(None) => {
            assert!(vm.status == Status::Halted);
            assert_unchanged(&vm, &s, &input, &out);
        }
        Ok(Some(e)) => {
            assert!(vm.status == Status::Running);
            assert!(vm.pc as i128 == s.pc as i128 + e.offset as i128);
            let kept = s.depth - e.pops;
            let mut depth = kept;
            for value in e.pushes.into_iter().flatten() {
                assert!(vm.stack[depth] == value);
                depth += 1;
            }
            assert!(vm.stack.len() == depth);
            for i in 0..kept {
                assert!(vm.stack[i] == s.stack[i]);
            }
            match e.store {
                Some((a, v)) => {
                    assert!(vm.memory.get(&a) == Some(&v));
                    match s.cell {
                        Some((k, old)) if k != a => {
                            assert!(vm.memory.len() == 2 && vm.memory.get(&k) == Some(&old));
                        }
                        _ => {
                            assert!(vm.memory.len() == 1);
                        }
                    }
                }
                None => assert_cell(&vm, &s),
            }
            assert!(input.0 == if e.reads { None } else { s.input });
            match e.writes {
                Some(byte) => {
                    assert!(out.1 == 1 && out.0 == Some(byte));
                }
                None => {
                    assert!(out.1 == 0);
                }
            }
        }
    }
    // Dropping the BTreeMap costs more than the step under proof.
    std::mem::forget(vm);
}

/// Two machines in the same state stay equal after a step.
/// `i8` operands for MUL, DIV and MOD and empty memory: wider does not finish in an hour.
fn deterministic(instr: Instr, depth: usize) {
    let program = [instr, instr];
    let s = any_before(depth, false);
    if matches!(instr, Instr::Mul | Instr::Div | Instr::Mod) {
        for v in s.stack {
            kani::assume(v >= i8::MIN as i64 && v <= i8::MAX as i64);
        }
    }
    let (mut one, mut two) = (start(&program, &s), start(&program, &s));
    let (mut in1, mut in2) = (OneByte(s.input), OneByte(s.input));
    let (mut out1, mut out2) = (Written::default(), Written::default());
    one.step(&mut in1, &mut out1);
    two.step(&mut in2, &mut out2);
    assert!(one.status == two.status && one.pc == two.pc && one.steps == two.steps);
    assert!(one.stack.len() == two.stack.len());
    for i in 0..one.stack.len() {
        assert!(one.stack[i] == two.stack[i]);
    }
    assert!(one.memory.len() == two.memory.len());
    if depth >= 1 {
        let address = s.stack[depth - 1];
        assert!(one.memory.get(&address) == two.memory.get(&address));
    }
    assert!(in1.0 == in2.0 && out1.0 == out2.0 && out1.1 == out2.1);
    std::mem::forget(one);
    std::mem::forget(two);
}

fn any_sym() -> Sym {
    let i: usize = kani::any();
    kani::assume(i < 8);
    Sym::ALL[i]
}

// One harness per depth: a symbolic depth grows the stack `Vec` past 4 GiB.
macro_rules! harnesses {
    ($($name:ident: $instr:expr, $cell:expr,)*) => {
        $(mod $name {
            use super::*;
            #[kani::proof]
            #[kani::unwind(5)]
            fn depth0() {
                check($instr, 0, $cell);
            }
            #[kani::proof]
            #[kani::unwind(5)]
            fn depth1() {
                check($instr, 1, $cell);
            }
            #[kani::proof]
            #[kani::unwind(5)]
            fn depth2() {
                check($instr, 2, $cell);
            }
            #[kani::proof]
            #[kani::unwind(5)]
            fn depth3() {
                check($instr, 3, $cell);
            }
            #[kani::proof]
            #[kani::unwind(5)]
            fn deterministic_depth2() {
                deterministic($instr, 2);
            }
        })*
    };
}

harnesses! {
    push: Instr::Push(any_sym()), false,
    dup: Instr::Dup, false,
    drop_top: Instr::Drop, false,
    swap: Instr::Swap, false,
    over: Instr::Over, false,
    rot: Instr::Rot, false,
    add: Instr::Add, false,
    sub: Instr::Sub, false,
    mul: Instr::Mul, false,
    div: Instr::Div, false,
    rem: Instr::Mod, false,
    load: Instr::Load, false,
    store: Instr::Store, false,
    jmp: Instr::Jmp, false,
    jz: Instr::Jz, false,
    jnz: Instr::Jnz, false,
    halt: Instr::Halt, false,
    call: Instr::Call, false,
    ret: Instr::Ret, false,
    read: Instr::Read, false,
    write: Instr::Write, false,
    eq: Instr::Eq, false,
    lt: Instr::Lt, false,
    gt: Instr::Gt, false,
    not: Instr::Not, false,
}

/// LOAD over an existing cell, at depth 0 and 1: CBMC runs out of memory at depth 2.
mod load_cell {
    use super::*;
    #[kani::proof]
    #[kani::unwind(5)]
    fn depth0() {
        check(Instr::Load, 0, true);
    }
    #[kani::proof]
    #[kani::unwind(5)]
    fn depth1() {
        check(Instr::Load, 1, true);
    }
}

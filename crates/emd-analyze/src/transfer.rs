// emd: an esoteric language written only in Unicode dashes.
// What one instruction does to an abstract state.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::analysis::Kind;
use crate::state::{Cell, Frame, Rel};
use crate::value::{Cmp, Val};
use emd_core::Instr;
use std::collections::BTreeSet;

/// An operation on larger sets gives unknown rather than taking its time.
const MAX_PAIRS: usize = 8192;
/// More addresses than this count as an interval of addresses.
const MAX_ADDRESSES: usize = 16;

/// `f` on every pair of values, and whether any failed. `None` if the sets are too large.
fn lift2(a: &Val, b: &Val, f: impl Fn(i64, i64) -> Option<i64>) -> Option<(Option<Val>, bool)> {
    let (Val::Known(xs), Val::Known(ys)) = (a, b) else {
        return None;
    };
    if xs.len().saturating_mul(ys.len()) > MAX_PAIRS {
        return None;
    }
    let mut out = BTreeSet::new();
    let mut failed = false;
    for &x in xs.iter() {
        for &y in ys.iter() {
            match f(x, y) {
                Some(v) => {
                    out.insert(v);
                }
                None => failed = true,
            }
        }
    }
    Some((if out.is_empty() { None } else { Some(Val::of(out)) }, failed))
}

/// A sum of bounds: no bound stays no bound, and a sum past the integers has none.
fn bound_add(x: i64, y: i64, none: i64) -> i64 {
    if x == none || y == none { none } else { x.checked_add(y).unwrap_or(none) }
}

/// `instr` on bounds, for values too large to enumerate. Overflow is not reported from here.
pub(crate) fn on_bounds(instr: Instr, a: &Val, b: &Val) -> Val {
    use Instr::*;
    let ((al, ah), (bl, bh)) = (a.bounds(), b.bounds());
    let either = || Val::of(BTreeSet::from([0, 1]));
    let verdict = |yes: bool| Val::one(i64::from(yes));
    match instr {
        Add => Val::range(bound_add(al, bl, i64::MIN), bound_add(ah, bh, i64::MAX)),
        Sub => match (bl.checked_neg(), bh.checked_neg()) {
            (Some(nl), Some(nh)) => Val::range(bound_add(al, nh, i64::MIN), bound_add(ah, nl, i64::MAX)),
            _ => Val::Unknown,
        },
        Eq if ah < bl || bh < al => verdict(false),
        Eq => either(),
        Lt if ah < bl => verdict(true),
        Lt if al >= bh => verdict(false),
        Lt => either(),
        Gt if al > bh => verdict(true),
        Gt if ah <= bl => verdict(false),
        Gt => either(),
        Mod if bl != i64::MIN && bh != i64::MAX => {
            let top = bl.unsigned_abs().max(bh.unsigned_abs()).saturating_sub(1).min(i64::MAX as u64) as i64;
            if al >= 0 { Val::range(0, top) } else { Val::range(-top, top) }
        }
        _ => Val::Unknown,
    }
}

/// A large set of addresses counts as the interval around it.
fn bounded_addresses(value: &Val) -> Val {
    match value {
        Val::Known(set) if set.len() > MAX_ADDRESSES => {
            let (lo, hi) = value.bounds();
            Val::range(lo, hi)
        }
        _ => value.clone(),
    }
}

/// What `ADD` and `SUB` by a constant, and a comparison with one, keep of a relation.
fn relate(instr: Instr, a: &Cell, b: &Cell) -> Option<Rel> {
    use Instr::*;
    let offset = |c: &Cell| match c.rel {
        Some(Rel::Offset { sym, off }) => Some((sym, off)),
        _ => None,
    };
    let test = |sym, off, cmp, k| Some(Rel::Test { sym, off, cmp, k });
    match (instr, a.val.single(), b.val.single()) {
        (Add, _, Some(k)) => {
            offset(a).and_then(|(sym, off)| Some(Rel::Offset { sym, off: off.checked_add(k)? }))
        }
        (Add, Some(k), _) => {
            offset(b).and_then(|(sym, off)| Some(Rel::Offset { sym, off: off.checked_add(k)? }))
        }
        (Sub, _, Some(k)) => {
            offset(a).and_then(|(sym, off)| Some(Rel::Offset { sym, off: off.checked_sub(k)? }))
        }
        (Eq, _, Some(k)) => offset(a).and_then(|(sym, off)| test(sym, off, Cmp::Eq, k)),
        (Eq, Some(k), _) => offset(b).and_then(|(sym, off)| test(sym, off, Cmp::Eq, k)),
        (Lt, _, Some(k)) => offset(a).and_then(|(sym, off)| test(sym, off, Cmp::Lt, k)),
        (Lt, Some(k), _) => offset(b).and_then(|(sym, off)| test(sym, off, Cmp::Gt, k)),
        (Gt, _, Some(k)) => offset(a).and_then(|(sym, off)| test(sym, off, Cmp::Gt, k)),
        (Gt, Some(k), _) => offset(b).and_then(|(sym, off)| test(sym, off, Cmp::Lt, k)),
        _ => None,
    }
}

/// What one instruction can do from one state.
#[derive(Default)]
pub(crate) struct Step {
    pub(crate) next: Vec<(usize, Option<Frame>)>,
    pub(crate) issues: Vec<(Kind, bool)>,
    pub(crate) wild: bool,
    pub(crate) halts: bool,
}

impl Step {
    /// Reports disallowed values. False if none is allowed, so execution stops here.
    fn check(&mut self, kind: Kind, value: &Val, allowed: impl Fn(i64) -> bool) -> bool {
        match value {
            Val::Known(set) => {
                let good = set.iter().filter(|&&v| allowed(v)).count();
                if good < set.len() {
                    self.issues.push((kind, good == 0));
                }
                good > 0
            }
            _ => {
                let (lo, hi) = value.bounds();
                let fine =
                    if kind == Kind::DivisionByZero { lo > 0 || hi < 0 } else { allowed(lo) && allowed(hi) };
                if !fine {
                    self.issues.push((kind, false));
                }
                true
            }
        }
    }
}

/// An instruction being followed. `rest` is its frame without the operands, `None` when nothing is known.
struct Flow<'p> {
    program: &'p [Instr],
    pc: usize,
    rest: Option<Frame>,
    step: Step,
}

impl Flow<'_> {
    fn with(&self, top: &[Cell]) -> Option<Frame> {
        self.rest.clone().map(|mut r| {
            r.stack.extend_from_slice(top);
            r
        })
    }

    fn land(&mut self, target: Option<i64>, after: Option<Frame>) {
        match target.filter(|t| (0..self.program.len() as i64).contains(t)) {
            Some(t) => self.step.next.push((t as usize, after)),
            None => self.step.issues.push((Kind::PcOutOfRange, false)),
        }
    }

    fn go(&mut self, offset: i64, after: Option<Frame>) {
        self.land((self.pc as i64).checked_add(offset), after);
    }

    /// On to the next instruction, with these cells on top of the rest.
    fn fall(&mut self, top: &[Cell]) {
        let after = self.with(top);
        self.go(1, after);
    }

    fn lose_track(&mut self) {
        self.step.issues.push((Kind::UnknownJump, false));
        self.step.wild = true;
    }

    fn jump(&mut self, offset: &Val, after: Option<Frame>) {
        match offset {
            Val::Known(set) => {
                for &off in set.iter() {
                    self.go(off, after.clone());
                }
            }
            _ => self.lose_track(),
        }
    }

    /// Addresses, not offsets: each return address known here is followed.
    fn ret(&mut self, address: &Val) {
        match address {
            Val::Known(set) => {
                for &a in set.iter() {
                    let after = self.with(&[]);
                    self.land(Some(a), after);
                }
            }
            _ => self.lose_track(),
        }
    }

    /// A symbol on the copy, so a test on one tells about the other.
    fn copy(&mut self, ops: &[Cell]) {
        let mut after = self.rest.clone();
        let mut shared = ops[0].clone();
        let mut between = ops.get(1).cloned();
        if shared.rel.is_none() {
            if let Some(f) = after.as_mut() {
                f.forget(self.pc);
            }
            // An operand left this frame, but it is coming back: it forgets too.
            if let Some(cell) = between.as_mut().filter(|c| c.rel.is_some_and(|r| r.sym() == self.pc)) {
                cell.rel = None;
            }
            shared.rel = Some(Rel::Offset { sym: self.pc, off: 0 });
        }
        let top: Vec<Cell> = match between {
            Some(cell) => vec![shared.clone(), cell, shared],
            None => vec![shared.clone(), shared],
        };
        if let Some(f) = after.as_mut() {
            f.stack.extend(top);
        }
        self.go(1, after);
    }

    fn result(&mut self, value: Option<Val>, failed: bool, rel: Option<Rel>) {
        if failed {
            self.step.issues.push((Kind::Overflow, value.is_none()));
        }
        if let Some(val) = value {
            self.fall(&[Cell { val, rel }]);
        }
    }

    fn compute(&mut self, instr: Instr, ops: &[Cell]) {
        let (value, failed) = lift2(&ops[0].val, &ops[1].val, |a, b| match instr {
            Instr::Add => a.checked_add(b),
            Instr::Sub => a.checked_sub(b),
            Instr::Mul => a.checked_mul(b),
            Instr::Eq => Some(i64::from(a == b)),
            Instr::Lt => Some(i64::from(a < b)),
            _ => Some(i64::from(a > b)),
        })
        .unwrap_or_else(|| (Some(on_bounds(instr, &ops[0].val, &ops[1].val)), false));
        self.result(value, failed, relate(instr, &ops[0], &ops[1]));
    }

    fn divide(&mut self, instr: Instr, ops: &[Cell]) {
        if !self.step.check(Kind::DivisionByZero, &ops[1].val, |b| b != 0) {
            return;
        }
        // Only the divisors that get this far count for what comes next.
        let divisor = match &ops[1].val {
            Val::Known(set) => Val::of(set.iter().copied().filter(|&b| b != 0).collect()),
            other => other.clone(),
        };
        let (value, failed) = lift2(&ops[0].val, &divisor, |a, b| {
            if instr == Instr::Div { a.checked_div(b) } else { Some(a.wrapping_rem(b)) }
        })
        .unwrap_or_else(|| (Some(on_bounds(instr, &ops[0].val, &divisor)), false));
        self.result(value, failed, None);
    }

    fn load(&mut self, address: &Val) {
        if !self.step.check(Kind::NegativeAddress, address, |a| a >= 0) {
            return;
        }
        let mut after = self.rest.clone();
        if let Some(f) = after.as_mut() {
            let cell = load_from(f, self.pc, address);
            f.stack.push(cell);
        }
        self.go(1, after);
    }

    fn store(&mut self, value: &Cell, address: &Val) {
        if !self.step.check(Kind::NegativeAddress, address, |a| a >= 0) {
            return;
        }
        let mut after = self.rest.clone();
        if let Some(f) = after.as_mut() {
            store_to(f, value, address);
        }
        self.go(1, after);
    }

    fn branch(&mut self, instr: Instr, ops: &[Cell]) {
        let on_zero = instr == Instr::Jz;
        let (can_zero, can_other) = match &ops[0].val {
            Val::Known(set) => (set.contains(&0), set.iter().any(|&c| c != 0)),
            other => (other.contains(0), true),
        };
        let (taken, falls) = if on_zero { (can_zero, can_other) } else { (can_other, can_zero) };
        // The condition is known, on each way out: so is what it was computed from.
        let way_out = |flow: &Flow<'_>, taken_way: bool| -> Option<Option<Frame>> {
            let zero = taken_way == on_zero;
            match flow.with(&[]) {
                Some(f) => f.after_branch(&ops[0], zero).map(Some),
                None => Some(None),
            }
        };
        if taken && let Some(after) = way_out(self, true) {
            self.jump(&ops[1].val, after);
        }
        if falls && let Some(after) = way_out(self, false) {
            self.go(1, after);
        }
    }

    fn read(&mut self) {
        let mut after = self.rest.clone();
        if let Some(f) = after.as_mut() {
            f.forget(self.pc);
            f.stack.push(Cell {
                val: Val::of((-1..=255).collect()),
                rel: Some(Rel::Offset { sym: self.pc, off: 0 }),
            });
        }
        self.go(1, after);
    }

    fn not(&mut self, operand: &Cell) {
        let val = match &operand.val {
            Val::Known(set) => Val::of(set.iter().map(|&a| i64::from(a == 0)).collect()),
            other if other.contains(0) => Val::of(BTreeSet::from([0, 1])),
            _ => Val::one(0),
        };
        let rel = match operand.rel {
            Some(Rel::Offset { sym, off }) => Some(Rel::Test { sym, off, cmp: Cmp::Eq, k: 0 }),
            Some(Rel::Test { sym, off, cmp, k }) => Some(Rel::Test { sym, off, cmp: cmp.negated(), k }),
            None => None,
        };
        self.fall(&[Cell { val, rel }]);
    }
}

/// The value read from `address`. A single known cell and the value become the same symbol.
fn load_from(f: &mut Frame, pc: usize, address: &Val) -> Cell {
    match bounded_addresses(address) {
        Val::Known(set) if set.len() == 1 => {
            let a = *set.first().expect("one address");
            let mut cell = f.stored(a);
            if cell.rel.is_none() {
                f.forget(pc);
                cell.rel = Some(Rel::Offset { sym: pc, off: 0 });
                f.mem.insert(a, cell.clone());
            }
            cell
        }
        Val::Known(set) => {
            let mut val: Option<Val> = None;
            for &a in set.iter().filter(|&&a| a >= 0) {
                let v = f.cell(a);
                val = Some(val.map_or(v.clone(), |x: Val| x.join(&v)));
            }
            Cell::plain(val.unwrap_or(Val::Unknown))
        }
        other => {
            let (lo, hi) = other.bounds();
            let inside = f.mem.range(lo.max(0)..=hi.max(0)).map(|(_, c)| &c.val);
            Cell::plain(inside.fold(f.rest.clone(), |x, v| x.join(v)))
        }
    }
}

fn store_to(f: &mut Frame, value: &Cell, address: &Val) {
    match bounded_addresses(address) {
        Val::Known(set) if set.len() == 1 => {
            f.mem.insert(*set.first().expect("one address"), value.clone());
        }
        Val::Known(set) => {
            let written = Cell::plain(value.val.clone());
            for &a in set.iter().filter(|&&a| a >= 0) {
                let old = f.stored(a);
                f.mem.insert(a, old.join(&written));
            }
        }
        other => {
            // Only the cells in the interval can change.
            let (lo, hi) = other.bounds();
            let written = Cell::plain(value.val.clone());
            for (_, cell) in f.mem.range_mut(lo.max(0)..=hi.max(0)) {
                *cell = cell.join(&written);
            }
            f.rest = f.rest.join(&value.val);
        }
    }
}

fn operands(instr: Instr) -> usize {
    use Instr::*;
    match instr {
        Push(_) | Halt | Read => 0,
        Dup | Drop | Load | Jmp | Write | Not | Call | Ret => 1,
        Rot => 3,
        _ => 2,
    }
}

/// One instruction from one state, or from no known state.
pub(crate) fn transfer(program: &[Instr], pc: usize, frame: Option<&Frame>) -> Step {
    use Instr::*;
    let instr = program[pc];
    let needed = operands(instr);
    let mut step = Step::default();
    let (rest, ops): (Option<Frame>, Vec<Cell>) = match frame {
        Some(f) if f.stack.len() < needed => {
            step.issues.push((Kind::StackUnderflow, true));
            return step;
        }
        Some(f) => {
            let split = f.stack.len() - needed;
            let ops = f.stack[split..].to_vec();
            let mut r = f.clone();
            r.stack.truncate(split);
            (Some(r), ops)
        }
        None => {
            if needed > 0 {
                step.issues.push((Kind::StackUnderflow, false));
            }
            (None, vec![Cell::plain(Val::Unknown); needed])
        }
    };
    let mut flow = Flow { program, pc, rest, step };
    match instr {
        Push(n) => flow.fall(&[Cell::plain(Val::one(i64::from(n.index())))]),
        Dup | Over => flow.copy(&ops),
        Drop => flow.fall(&[]),
        Swap => flow.fall(&[ops[1].clone(), ops[0].clone()]),
        Rot => flow.fall(&[ops[1].clone(), ops[2].clone(), ops[0].clone()]),
        Add | Sub | Mul | Eq | Lt | Gt => flow.compute(instr, &ops),
        Div | Mod => flow.divide(instr, &ops),
        Load => flow.load(&ops[0].val),
        Store => flow.store(&ops[0], &ops[1].val),
        Jmp => flow.jump(&ops[0].val, flow.with(&[])),
        Jz | Jnz => flow.branch(instr, &ops),
        Call => flow.jump(&ops[0].val, flow.with(&[Cell::plain(Val::one(pc as i64 + 1))])),
        Ret => flow.ret(&ops[0].val),
        Halt => flow.step.halts = true,
        Read => flow.read(),
        Write => {
            if flow.step.check(Kind::InvalidByte, &ops[0].val, |v| (0..=255).contains(&v)) {
                flow.fall(&[]);
            }
        }
        Not => flow.not(&ops[0]),
    }
    flow.step
}

// emd: an esoteric language written only in Unicode dashes.
// Abstract states: cells with their relations, frames, and the frames reaching a program point.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::value::{Cmp, Val};
use std::collections::BTreeMap;

/// Past this many stack depths at one program point, its stack is unknown.
const MAX_DEPTHS: usize = 32;

/// A value in terms of a symbol: what the instruction at a `pc` last produced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rel {
    /// The symbol plus an offset.
    Offset { sym: usize, off: i64 },
    /// 1 if `symbol + off` compares so with `k`, else 0.
    Test { sym: usize, off: i64, cmp: Cmp, k: i64 },
}

impl Rel {
    pub(crate) fn sym(self) -> usize {
        match self {
            Rel::Offset { sym, .. } | Rel::Test { sym, .. } => sym,
        }
    }
}

/// A value and, if known, how it relates to a symbol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Cell {
    pub val: Val,
    pub(crate) rel: Option<Rel>,
}

impl Cell {
    pub(crate) fn plain(val: Val) -> Cell {
        Cell { val, rel: None }
    }

    pub(crate) fn join(&self, other: &Cell) -> Cell {
        Cell { val: self.val.join(&other.val), rel: if self.rel == other.rel { self.rel } else { None } }
    }
}

/// An abstract state: an exact stack and memory by cell. Unlisted cells hold a value of `rest`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Frame {
    pub stack: Vec<Cell>,
    pub mem: BTreeMap<i64, Cell>,
    pub rest: Val,
}

impl Frame {
    pub(crate) fn start() -> Frame {
        Frame { stack: Vec::new(), mem: BTreeMap::new(), rest: Val::one(0) }
    }

    pub fn cell(&self, address: i64) -> Val {
        self.mem.get(&address).map_or_else(|| self.rest.clone(), |c| c.val.clone())
    }

    /// What the cell holds, with its relation if it was written.
    pub(crate) fn stored(&self, address: i64) -> Cell {
        self.mem.get(&address).cloned().unwrap_or_else(|| Cell::plain(self.rest.clone()))
    }

    pub(crate) fn join(&self, other: &Frame) -> Frame {
        let stack = self.stack.iter().zip(&other.stack).map(|(a, b)| a.join(b)).collect();
        let mut mem = BTreeMap::new();
        for &a in self.mem.keys().chain(other.mem.keys()) {
            mem.insert(a, self.stored(a).join(&other.stored(a)));
        }
        Frame { stack, mem, rest: self.rest.join(&other.rest) }
    }

    /// With `all`, every changed value loses the bound that moved; without, only values past enumerating.
    pub(crate) fn widen_from(&mut self, old: &Frame, all: bool) {
        let widen = |cell: &mut Cell, before: Val| {
            let past_sets = !matches!(cell.val, Val::Known(_));
            if cell.val != before && (all || past_sets) {
                *cell = Cell::plain(cell.val.widened_from(&before));
            }
        };
        for (cell, before) in self.stack.iter_mut().zip(&old.stack) {
            widen(cell, before.val.clone());
        }
        for (a, cell) in &mut self.mem {
            widen(cell, old.cell(*a));
        }
        if self.rest != old.rest && (all || !matches!(self.rest, Val::Known(_))) {
            self.rest = self.rest.widened_from(&old.rest);
        }
    }

    /// The instruction at `sym` runs again: its old value is no longer the symbol's.
    pub(crate) fn forget(&mut self, sym: usize) {
        for cell in self.stack.iter_mut().chain(self.mem.values_mut()) {
            if cell.rel.is_some_and(|r| r.sym() == sym) {
                cell.rel = None;
            }
        }
    }

    /// Everything known once the symbol compares so with `b`. `None` if it never can.
    fn narrow(mut self, sym: usize, cmp: Cmp, b: i64) -> Option<Frame> {
        for cell in self.stack.iter_mut().chain(self.mem.values_mut()) {
            if let Some(Rel::Offset { sym: s, off }) = cell.rel
                && s == sym
                && let Some(bound) = b.checked_add(off)
            {
                cell.val = cell.val.restrict(cmp, bound)?;
            }
        }
        Some(self)
    }

    /// `self` when the condition in `cond` was zero, or was not.
    pub(crate) fn after_branch(self, cond: &Cell, zero: bool) -> Option<Frame> {
        match cond.rel {
            Some(Rel::Offset { sym, off }) => match off.checked_neg() {
                Some(b) => self.narrow(sym, if zero { Cmp::Eq } else { Cmp::Ne }, b),
                None => Some(self),
            },
            Some(Rel::Test { sym, off, cmp, k }) => match k.checked_sub(off) {
                Some(b) => self.narrow(sym, if zero { cmp.negated() } else { cmp }, b),
                None => Some(self),
            },
            None => Some(self),
        }
    }
}

/// States reaching a program point: one per depth, and possibly one of unknown depth.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stacks {
    pub by_depth: BTreeMap<usize, Frame>,
    pub unknown: bool,
}

impl Stacks {
    pub fn reached(&self) -> bool {
        self.unknown || !self.by_depth.is_empty()
    }

    pub(crate) fn variants(&self) -> Vec<Option<Frame>> {
        let mut out: Vec<Option<Frame>> = self.by_depth.values().cloned().map(Some).collect();
        if self.unknown {
            out.push(None);
        }
        out
    }

    /// Adds a state. True if this changes what is known. `widen` stops a loop growing a value.
    pub(crate) fn add(&mut self, incoming: Option<Frame>, widen: bool) -> bool {
        let Some(frame) = incoming else {
            let changed = !self.unknown;
            self.unknown = true;
            return changed;
        };
        let full = self.by_depth.len() >= MAX_DEPTHS;
        match self.by_depth.get_mut(&frame.stack.len()) {
            Some(old) => {
                let mut merged = old.join(&frame);
                merged.widen_from(old, widen);
                let changed = *old != merged;
                *old = merged;
                changed
            }
            None if full => {
                let changed = !self.unknown;
                self.unknown = true;
                changed
            }
            None => {
                self.by_depth.insert(frame.stack.len(), frame);
                true
            }
        }
    }
}

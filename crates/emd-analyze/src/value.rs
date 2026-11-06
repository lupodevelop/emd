// emd: an esoteric language written only in Unicode dashes.
// What a program point knows about one value: a set, an interval, or nothing.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use std::collections::BTreeSet;
use std::rc::Rc;

/// Past this many possible values, a value becomes an interval.
pub(crate) const MAX_VALUES: usize = 512;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Val {
    /// Shared: states copy their values far more often than they change them.
    Known(Rc<BTreeSet<i64>>),
    /// All of `lo..=hi`. A bound at `i64::MIN` or `i64::MAX` means no bound.
    Range(i64, i64),
    Unknown,
}

impl Val {
    pub fn one(v: i64) -> Val {
        Val::Known(Rc::new(BTreeSet::from([v])))
    }

    pub(crate) fn range(lo: i64, hi: i64) -> Val {
        if lo == hi {
            Val::one(lo)
        } else if lo == i64::MIN && hi == i64::MAX {
            Val::Unknown
        } else {
            Val::Range(lo, hi)
        }
    }

    pub fn of(values: BTreeSet<i64>) -> Val {
        match (values.first(), values.last()) {
            (Some(&lo), Some(&hi)) if values.len() > MAX_VALUES => Val::range(lo, hi),
            _ => Val::Known(Rc::new(values)),
        }
    }

    /// The smallest and largest values, for a value that has at least one.
    pub(crate) fn bounds(&self) -> (i64, i64) {
        match self {
            Val::Known(set) => {
                (set.first().copied().unwrap_or(i64::MAX), set.last().copied().unwrap_or(i64::MIN))
            }
            Val::Range(lo, hi) => (*lo, *hi),
            Val::Unknown => (i64::MIN, i64::MAX),
        }
    }

    pub(crate) fn join(&self, other: &Val) -> Val {
        match (self, other) {
            (Val::Known(a), Val::Known(b)) if Rc::ptr_eq(a, b) || a == b => Val::Known(a.clone()),
            (Val::Known(a), Val::Known(b)) => Val::of(a.union(b).copied().collect()),
            _ => {
                let ((a, b), (c, d)) = (self.bounds(), other.bounds());
                Val::range(a.min(c), b.max(d))
            }
        }
    }

    pub fn contains(&self, v: i64) -> bool {
        match self {
            Val::Known(set) => set.contains(&v),
            Val::Range(lo, hi) => *lo <= v && v <= *hi,
            Val::Unknown => true,
        }
    }

    pub(crate) fn single(&self) -> Option<i64> {
        match self {
            Val::Known(set) if set.len() == 1 => set.first().copied(),
            _ => None,
        }
    }

    /// The values that satisfy `cmp` against `b`. `None` if there are none.
    pub(crate) fn restrict(&self, cmp: Cmp, b: i64) -> Option<Val> {
        if let Val::Known(set) = self {
            let kept: BTreeSet<i64> = set.iter().copied().filter(|&x| cmp.holds(x, b)).collect();
            return if kept.is_empty() { None } else { Some(Val::of(kept)) };
        }
        let (mut lo, mut hi) = self.bounds();
        match cmp {
            Cmp::Eq => (lo, hi) = (lo.max(b), hi.min(b)),
            Cmp::Ne => {
                if lo == b {
                    lo = lo.saturating_add(1);
                }
                if hi == b {
                    hi = hi.saturating_sub(1);
                }
            }
            Cmp::Lt => hi = hi.min(b.checked_sub(1)?),
            Cmp::Le => hi = hi.min(b),
            Cmp::Gt => lo = lo.max(b.checked_add(1)?),
            Cmp::Ge => lo = lo.max(b),
        }
        if lo > hi { None } else { Some(Val::range(lo, hi)) }
    }

    /// Bounds that moved go to no bound at all, so that a loop stops soon.
    pub(crate) fn widened_from(&self, before: &Val) -> Val {
        let ((old_lo, old_hi), (lo, hi)) = (before.bounds(), self.bounds());
        Val::range(if lo < old_lo { i64::MIN } else { lo }, if hi > old_hi { i64::MAX } else { hi })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Cmp {
    Eq,
    Ne,
    Lt,
    Ge,
    Gt,
    Le,
}

impl Cmp {
    fn holds(self, a: i64, b: i64) -> bool {
        match self {
            Cmp::Eq => a == b,
            Cmp::Ne => a != b,
            Cmp::Lt => a < b,
            Cmp::Ge => a >= b,
            Cmp::Gt => a > b,
            Cmp::Le => a <= b,
        }
    }

    pub(crate) fn negated(self) -> Cmp {
        match self {
            Cmp::Eq => Cmp::Ne,
            Cmp::Ne => Cmp::Eq,
            Cmp::Lt => Cmp::Ge,
            Cmp::Ge => Cmp::Lt,
            Cmp::Gt => Cmp::Le,
            Cmp::Le => Cmp::Gt,
        }
    }
}

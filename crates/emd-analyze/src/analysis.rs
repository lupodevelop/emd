// emd: an esoteric language written only in Unicode dashes.
// The fixed point over the program, and the report it gives.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::state::{Frame, Stacks};
use crate::transfer::transfer;
use emd_core::Instr;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Past this many visits to a point, whatever still changes there becomes unknown.
const WIDEN_VISITS: usize = 1500;
/// The same, for the whole analysis, so that a large program cannot take long.
const WIDEN_STEPS: usize = 100_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    StackUnderflow,
    PcOutOfRange,
    DivisionByZero,
    NegativeAddress,
    InvalidByte,
    Overflow,
    UnknownJump,
}

impl Kind {
    pub const ALL: [(Kind, &str); 7] = [
        (Kind::StackUnderflow, "no stack underflow"),
        (Kind::PcOutOfRange, "pc stays inside the program"),
        (Kind::UnknownJump, "every jump and return has a known target"),
        (Kind::DivisionByZero, "no division by zero"),
        (Kind::NegativeAddress, "no negative address"),
        (Kind::InvalidByte, "WRITE only gets bytes"),
        (Kind::Overflow, "no overflow on known values"),
    ];
}

/// A fault this instruction may raise. `certain` means it raises it every time it runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Issue {
    pub pc: usize,
    pub kind: Kind,
    pub certain: bool,
}

#[derive(Debug)]
pub struct Analysis {
    pub stacks: Vec<Stacks>,
    pub edges: BTreeSet<(usize, usize)>,
    pub issues: BTreeSet<Issue>,
    pub halt_reachable: bool,
}

/// The analysis of a program, from an empty stack and zeroed memory at `pc` 0.
pub fn analyze(program: &[Instr]) -> Analysis {
    let mut analysis = Analysis {
        stacks: vec![Stacks::default(); program.len()],
        edges: BTreeSet::new(),
        issues: BTreeSet::new(),
        halt_reachable: false,
    };
    if program.is_empty() {
        analysis.issues.insert(Issue { pc: 0, kind: Kind::PcOutOfRange, certain: true });
        return analysis;
    }
    analysis.stacks[0].add(Some(Frame::start()), false);
    let mut work = BTreeSet::from([0]);
    let mut visits = vec![0; program.len()];
    let mut steps = 0;
    // Values only grow to a limit, relations are only lost, and depths are bounded: this ends.
    while let Some(pc) = work.pop_first() {
        for variant in analysis.stacks[pc].variants() {
            let step = transfer(program, pc, variant.as_ref());
            let mut next = step.next;
            if step.wild {
                next.extend((0..program.len()).map(|t| (t, None)));
            }
            steps += 1;
            for (target, incoming) in next {
                visits[target] += 1;
                let widen = visits[target] > WIDEN_VISITS || steps > WIDEN_STEPS;
                if analysis.stacks[target].add(incoming, widen) {
                    work.insert(target);
                }
            }
        }
    }
    // Certain only if every way of reaching the instruction raises it.
    for pc in 0..program.len() {
        let variants = analysis.stacks[pc].variants();
        let mut seen: BTreeMap<Kind, (usize, bool)> = BTreeMap::new();
        for variant in &variants {
            let step = transfer(program, pc, variant.as_ref());
            let mut kinds: BTreeMap<Kind, bool> = BTreeMap::new();
            for (kind, certain) in step.issues {
                let entry = kinds.entry(kind).or_insert(certain);
                *entry = *entry && certain;
            }
            for (kind, certain) in kinds {
                let entry = seen.entry(kind).or_insert((0, true));
                entry.0 += 1;
                entry.1 = entry.1 && certain;
            }
            analysis.edges.extend(step.next.iter().map(|&(t, _)| (pc, t)));
            if step.wild {
                analysis.edges.extend((0..program.len()).map(|t| (pc, t)));
            }
            analysis.halt_reachable |= step.halts;
        }
        for (kind, (count, certain)) in seen {
            analysis.issues.insert(Issue { pc, kind, certain: certain && count == variants.len() });
        }
    }
    analysis
}

impl Analysis {
    /// True when nothing in the report is left unproved.
    pub fn is_clean(&self) -> bool {
        self.issues.is_empty() && self.halt_reachable
    }
}

impl fmt::Display for Analysis {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let reached = self.stacks.iter().filter(|s| s.reached()).count();
        let mut out = format!("reachable: {reached} of {} instructions\n", self.stacks.len());
        let dead: Vec<usize> =
            self.stacks.iter().enumerate().filter_map(|(i, s)| (!s.reached()).then_some(i)).collect();
        if !dead.is_empty() {
            out += &format!("dead code at pc {dead:?}\n");
        }
        out += if self.halt_reachable {
            "proved:     HALT is reachable by the analysis\n"
        } else {
            "not proved: HALT is not reachable, so no run can halt\n"
        };
        for (kind, claim) in Kind::ALL {
            let found: Vec<&Issue> = self.issues.iter().filter(|i| i.kind == kind).collect();
            if found.is_empty() {
                out += &format!("proved:     {claim}\n");
                continue;
            }
            let shown: Vec<String> = found
                .iter()
                .take(8)
                .map(|i| format!("{}{}", i.pc, if i.certain { " (certain if reached)" } else { "" }))
                .collect();
            let more = if found.len() > 8 { format!(" and {} more", found.len() - 8) } else { String::new() };
            out += &format!("not proved: {claim}: pc {}{more}\n", shown.join(", "));
        }
        out += "not analyzed: overflow on unknown values, resource limits, termination";
        f.write_str(&out)
    }
}

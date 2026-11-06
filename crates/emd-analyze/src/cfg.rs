// emd: an esoteric language written only in Unicode dashes.
// The control flow graph, in Graphviz.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::analysis::analyze;
use crate::state::Stacks;
use emd_core::Instr;
use std::collections::BTreeSet;

/// The control flow graph, in Graphviz. A block ends at a jump or where a jump lands.
pub fn cfg(program: &[Instr]) -> String {
    const COLORS: [&str; 6] = ["#e06c75", "#e5c07b", "#98c379", "#56b6c2", "#61afef", "#c678dd"];
    let analysis = analyze(program);
    let reached = |pc: usize| analysis.stacks.get(pc).is_some_and(Stacks::reached);
    let mut leaders: BTreeSet<usize> = BTreeSet::from([0]);
    for &(from, to) in &analysis.edges {
        if to != from + 1 {
            leaders.insert(to);
            leaders.insert(from + 1);
        }
    }
    for (pc, instr) in program.iter().enumerate() {
        if matches!(instr, Instr::Jz | Instr::Jnz | Instr::Jmp | Instr::Halt | Instr::Call | Instr::Ret) {
            leaders.insert(pc + 1);
        }
    }
    let mut out = String::from("digraph emd {\n  node [shape=box style=filled fontname=monospace]\n");
    let starts: Vec<usize> = leaders.iter().copied().filter(|&pc| reached(pc)).collect();
    for (n, &start) in starts.iter().enumerate() {
        let mut pc = start;
        let mut label = String::new();
        loop {
            label += &format!("{pc}: {}\\l", program[pc]);
            if leaders.contains(&(pc + 1)) || !reached(pc + 1) {
                break;
            }
            pc += 1;
        }
        out += &format!("  b{start} [label=\"{label}\" fillcolor=\"{}\"]\n", COLORS[n % COLORS.len()]);
        for &(from, to) in analysis.edges.range((pc, 0)..=(pc, usize::MAX)) {
            debug_assert_eq!(from, pc);
            out += &format!("  b{start} -> b{to}\n");
        }
    }
    out + "}\n"
}

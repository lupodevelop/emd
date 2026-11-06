// emd: an esoteric language written only in Unicode dashes.
// Runs a program and counts what it did.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::Instr;
use emd_vm::{Limits, Status, Vm};
use std::collections::BTreeMap;
use std::fmt;
use std::io::{Read, Write};

/// What one run did.
pub struct Profile {
    pub steps: u64,
    pub status: Status,
    pub max_depth: usize,
    pub cells: usize,
    /// Executions per pc, indexed by pc.
    pub per_pc: Vec<u64>,
    pub per_instr: BTreeMap<String, u64>,
}

pub fn profile(program: &[Instr], input: &mut dyn Read, output: &mut dyn Write, limits: Limits) -> Profile {
    let mut vm = Vm::new(program, limits);
    let mut per_pc = vec![0; program.len()];
    let mut per_instr: BTreeMap<String, u64> = BTreeMap::new();
    let mut max_depth = 0;
    while vm.status == Status::Running {
        let pc = vm.pc;
        let steps = vm.steps;
        vm.step(input, output);
        // A step that hit the step limit never ran its instruction.
        if vm.steps > steps {
            per_pc[pc] += 1;
            *per_instr.entry(program[pc].to_string()).or_default() += 1;
        }
        max_depth = max_depth.max(vm.stack.len());
    }
    Profile {
        steps: vm.steps,
        status: vm.status.clone(),
        max_depth,
        cells: vm.memory.len(),
        per_pc,
        per_instr,
    }
}

impl fmt::Display for Profile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let end = match &self.status {
            Status::Faulted(fault) => format!("fault: {fault}"),
            _ => String::from("halted"),
        };
        let mut out = format!(
            "{end} after {} steps, max stack {}, {} cells written\n",
            self.steps, self.max_depth, self.cells
        );
        let share = |n: u64| 100.0 * n as f64 / self.steps.max(1) as f64;
        let mut instrs: Vec<(&String, &u64)> = self.per_instr.iter().collect();
        instrs.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        out += "by instruction:\n";
        for (name, n) in instrs.iter().take(10) {
            out += &format!("  {name:<8} {n:>10}  {:>5.1}%\n", share(**n));
        }
        let mut hot: Vec<(usize, u64)> =
            self.per_pc.iter().copied().enumerate().filter(|&(_, n)| n > 0).collect();
        hot.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        out += "hottest pc:";
        for (pc, n) in hot.iter().take(10) {
            out += &format!("\n  {pc:>8} {n:>10}  {:>5.1}%", share(*n));
        }
        f.write_str(&out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use emd_core::Sym;

    fn push(n: u8) -> Instr {
        Instr::Push(Sym::new(n).unwrap())
    }

    #[test]
    fn counts_every_execution_of_a_loop() {
        // 3 times: 1 SUB DUP, then JNZ back to the 1.
        let p = [
            push(3),
            push(1),
            Instr::Sub,
            Instr::Dup,
            push(0),
            push(6),
            Instr::Sub,
            Instr::Jnz,
            Instr::Drop,
            Instr::Halt,
        ];
        let r = profile(&p, &mut &b""[..], &mut std::io::sink(), Limits::default());
        assert_eq!(r.status, Status::Halted);
        assert_eq!(r.per_pc[1], 3);
        assert_eq!(r.per_instr["SUB"], 6);
        assert_eq!(r.steps, r.per_pc.iter().sum::<u64>());
        assert_eq!(r.max_depth, 4);
        let text = r.to_string();
        assert!(text.starts_with("halted after 24 steps, max stack 4, 0 cells written"), "{text}");
        assert!(text.contains("SUB"), "{text}");
    }

    #[test]
    fn a_fault_and_the_step_limit_are_reported_and_output_passes_through() {
        let p = [push(7), Instr::Write, Instr::Add];
        let mut out = Vec::new();
        let r = profile(&p, &mut &b""[..], &mut out, Limits::default());
        assert_eq!(out, [7]);
        assert!(r.to_string().contains("stack underflow"));
        assert_eq!(r.per_pc, [1, 1, 1]);

        let looping = [push(0), push(3), Instr::Sub, Instr::Jmp];
        let limited = Limits { max_steps: 10, ..Limits::default() };
        let r = profile(&looping, &mut &b""[..], &mut std::io::sink(), limited);
        assert_eq!(r.steps, 10);
        assert_eq!(r.per_pc.iter().sum::<u64>(), 10, "the step that hits the limit runs nothing");
    }
}

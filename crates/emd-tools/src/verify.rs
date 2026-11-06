// emd: an esoteric language written only in Unicode dashes.
// A quick verdict on a program: static checks, then a bounded run.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::Instr;
use emd_vm::{Fault, Limits, Status, Vm};
use std::io;

/// The step limit without `--max-steps`.
pub const VERIFY_STEPS: u64 = 10_000_000;

/// How a bounded run ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Halted,
    Faulted,
    /// The step limit came first, which says nothing about the program.
    NoVerdict,
}

/// A report on the program, decoded already, and how its bounded run on empty input ended.
pub fn verify(program: &[Instr], max_steps: u64) -> (String, Verdict) {
    let mut vm = Vm::new(program, Limits { max_steps, ..Limits::default() });
    vm.run(&mut io::empty(), &mut io::sink());
    let halt = if program.contains(&Instr::Halt) { "present" } else { "ABSENT, every run ends in a fault" };
    // The machine has stopped: it halted unless it faulted.
    let (text, verdict) = match &vm.status {
        Status::Faulted(Fault::StepLimit) => {
            ("no verdict, step limit reached".to_string(), Verdict::NoVerdict)
        }
        Status::Faulted(f) => {
            (format!("fault at pc {} after {} steps: {f}", vm.pc, vm.steps), Verdict::Faulted)
        }
        _ => (format!("halted after {} steps, stack depth {}", vm.steps, vm.stack.len()), Verdict::Halted),
    };
    let report = format!(
        "decoded: {} instructions\nhalt: {halt}\nbounded run (empty input, max_steps={max_steps}): {text}\n",
        program.len(),
    );
    (report, verdict)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn each_ending_has_its_verdict() {
        let (report, verdict) = verify(&[Instr::Halt], 10);
        assert_eq!(verdict, Verdict::Halted, "{report}");
        assert!(report.contains("halt: present"), "{report}");
        assert!(report.contains("halted after 1 steps, stack depth 0"), "{report}");

        let (report, verdict) = verify(&[Instr::Add], 10);
        assert_eq!(verdict, Verdict::Faulted, "{report}");
        assert!(report.contains("ABSENT"), "{report}");

        let looping = emd_asm::assemble("top: JMP top").unwrap();
        let (report, verdict) = verify(&looping, 10);
        assert_eq!(verdict, Verdict::NoVerdict, "{report}");
        assert!(report.contains("max_steps=10): no verdict"), "{report}");
    }
}

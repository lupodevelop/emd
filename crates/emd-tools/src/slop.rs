// emd: an esoteric language written only in Unicode dashes.
// Runs the dashes of any text, skipping the pairs that mean nothing.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::{Instr, Sym};
use emd_vm::{Limits, Status, Vm};
use std::io::{self, Write};

const SLOP_STEPS: u64 = 1_000_000;

#[derive(Debug, PartialEq, Eq)]
pub struct Slop {
    pub program: Vec<Instr>,
    pub characters: usize,
    pub dashes: usize,
    pub skipped_pairs: usize,
}

/// The dashes hiding in any text, read as a program. Unassigned pairs are skipped.
pub fn slop(text: &str) -> Slop {
    let dashes: Vec<Sym> = text.chars().filter_map(Sym::from_char).collect();
    let pairs = dashes.as_chunks::<2>().0;
    let program: Vec<Instr> = pairs.iter().filter_map(|&[f, o]| Instr::decode(f, o)).collect();
    Slop {
        characters: text.chars().count(),
        dashes: dashes.len(),
        skipped_pairs: pairs.len() - program.len(),
        program,
    }
}

impl Slop {
    /// Runs the program it found, and says what became of it.
    pub fn run(&self, output: &mut dyn Write) -> String {
        let mut vm = Vm::new(&self.program, Limits { max_steps: SLOP_STEPS, ..Limits::default() });
        vm.run(&mut io::empty(), output);
        let mut report = format!(
            "{} dashes in {} characters: {} instructions, {} pairs meant nothing\n",
            self.dashes,
            self.characters,
            self.program.len(),
            self.skipped_pairs
        );
        if !self.program.is_empty() {
            let names: Vec<String> = self.program.iter().take(16).map(Instr::to_string).collect();
            let more = if self.program.len() > 16 { " ..." } else { "" };
            report += &format!("program: {}{more}\n", names.join(" "));
        }
        match &vm.status {
            Status::Faulted(f) => report += &format!("it ran {} steps, then: {f}", vm.steps),
            _ => report += &format!("it ran {} steps and halted, somehow", vm.steps),
        }
        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prose_yields_the_program_hidden_in_its_dashes() {
        let text = "It\u{2019}s not just a tool - \u{2010}it\u{2019}s a mindset. Here - \u{2011}\u{2011}- ok \u{2013}\u{2012}.";
        let s = slop(text);
        assert_eq!(s.dashes, 8);
        assert_eq!(s.skipped_pairs, 0);
        let names: Vec<String> = s.program.iter().map(Instr::to_string).collect();
        assert_eq!(names, ["PUSH 1", "PUSH 2", "ADD", "HALT"]);
    }

    #[test]
    fn a_text_can_halt_by_accident_or_hold_nothing() {
        let halting = slop("\u{2013}\u{2012}").run(&mut Vec::new());
        assert!(halting.contains("it ran 1 steps and halted, somehow"), "{halting}");
        let empty = slop("no dashes at all").run(&mut Vec::new());
        assert!(!empty.contains("program:"), "{empty}");
        let long = slop(&"-\u{2010}".repeat(17)).run(&mut Vec::new());
        assert!(long.contains("PUSH 1 ..."), "{long}");
        assert!(!empty.contains("program:"), "{empty}");
    }

    #[test]
    fn em_dash_pairs_are_skipped_and_a_lone_dash_is_ignored() {
        let s = slop("a\u{2014}b\u{2014}c\u{2014}");
        assert_eq!((s.dashes, s.skipped_pairs), (3, 1));
        assert!(s.program.is_empty());
        assert_eq!(s.characters, 6);
        assert_eq!(slop("no dashes at all").dashes, 0);
    }
}

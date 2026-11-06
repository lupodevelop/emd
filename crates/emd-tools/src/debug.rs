// emd: an esoteric language written only in Unicode dashes.
// A debugger that goes backward by replaying from the start: the machine is deterministic.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::Instr;
use emd_vm::{Limits, Status, Vm};
use std::collections::BTreeSet;

/// Stops `c` on a program that never ends, or never reaches a breakpoint.
const CONTINUE_STEPS: u64 = 10_000_000;

const HELP: &str = "\
s [n]     step forward
b [n]     step back
c         continue to a breakpoint or the end
rc        continue backward to the previous breakpoint
goto n    move to step n, in either direction
break pc  set a breakpoint, del pc removes it
p         state, nonzero memory and output
l         the instructions around pc
mem a     the value of a cell
why a     the step that last wrote a cell
q         quit
An empty line repeats the last command.";

/// `text` as a JSON string.
pub fn json_text(text: &str) -> String {
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if u32::from(c) < 0x20 => out.push_str(&format!("\\u{:04x}", u32::from(c))),
            c => out.push(c),
        }
    }
    out + "\""
}

/// A debugger without snapshots: to go back, it runs the program again from the start.
pub struct Debugger<'p> {
    program: &'p [Instr],
    input: &'p [u8],
    vm: Vm<'p>,
    consumed: usize,
    output: Vec<u8>,
    breaks: BTreeSet<usize>,
}

impl<'p> Debugger<'p> {
    pub fn new(program: &'p [Instr], input: &'p [u8]) -> Self {
        Debugger {
            program,
            input,
            vm: Vm::new(program, Limits::default()),
            consumed: 0,
            output: Vec::new(),
            breaks: BTreeSet::new(),
        }
    }

    pub fn steps(&self) -> u64 {
        self.vm.steps
    }

    fn running(&self) -> bool {
        self.vm.status == Status::Running
    }

    fn step(&mut self) {
        let mut rest = &self.input[self.consumed..];
        self.vm.step(&mut rest, &mut self.output);
        self.consumed = self.input.len() - rest.len();
    }

    /// Replays from the start up to step `target`, or to the end if it comes first.
    fn replay_to(&mut self, target: u64) {
        self.vm = Vm::new(self.program, Limits::default());
        self.consumed = 0;
        self.output.clear();
        while self.running() && self.vm.steps < target {
            self.step();
        }
    }

    /// One line: step, pc, the next instruction, stack, and how it ended if it did.
    pub fn show(&self) -> String {
        let next = self.program.get(self.vm.pc).map_or(String::from("-"), Instr::to_string);
        let end = match &self.vm.status {
            Status::Running => String::new(),
            Status::Halted => String::from("  halted"),
            Status::Faulted(f) => format!("  fault: {f}"),
        };
        format!("step {}  pc {}  {next}  stack {:?}{end}", self.vm.steps, self.vm.pc, self.vm.stack)
    }

    /// The state as one line of JSON, for editors. Bytes stay numbers: output need not be text.
    pub fn json(&self, message: &str) -> String {
        let status = match &self.vm.status {
            Status::Running => String::from("running"),
            Status::Halted => String::from("halted"),
            Status::Faulted(f) => format!("fault: {f}"),
        };
        let memory: Vec<String> = self.vm.memory.iter().map(|(a, v)| format!("[{a},{v}]")).collect();
        format!(
            r#"{{"step":{},"pc":{},"status":{},"stack":{:?},"memory":[{}],"output":{:?},"breaks":{:?},"message":{}}}"#,
            self.vm.steps,
            self.vm.pc,
            json_text(&status),
            self.vm.stack,
            memory.join(","),
            self.output,
            self.breaks.iter().collect::<Vec<_>>(),
            json_text(message),
        )
    }

    /// Runs one command and returns what to print. Quitting is up to the caller.
    pub fn command(&mut self, line: &str) -> String {
        let words: Vec<&str> = line.split_whitespace().collect();
        let number = words.get(1).map(|w| w.parse::<i64>());
        let count = match number {
            None => 1,
            Some(Ok(n)) if n >= 0 => n as u64,
            Some(_) => return format!("`{}` is not a number", words[1]),
        };
        match words.first().copied().unwrap_or("") {
            "s" => {
                for _ in 0..count {
                    if !self.running() {
                        break;
                    }
                    self.step();
                }
                self.show()
            }
            "b" => {
                self.replay_to(self.vm.steps.saturating_sub(count));
                self.show()
            }
            "goto" if number.is_some() => {
                self.replay_to(count);
                self.show()
            }
            "c" => self.resume(),
            "rc" => self.resume_backward(),
            "break" if number.is_some() => {
                self.breaks.insert(count as usize);
                format!("breakpoints {:?}", self.breaks)
            }
            "del" if number.is_some() => {
                self.breaks.remove(&(count as usize));
                format!("breakpoints {:?}", self.breaks)
            }
            "p" => self.state(),
            "l" => self.listing(),
            "mem" if number.is_some() => {
                format!("[{count}] = {}", self.vm.memory.get(&(count as i64)).copied().unwrap_or(0))
            }
            "why" if number.is_some() => self.why(count as i64),
            "h" | "help" => HELP.to_string(),
            _ => format!("unknown command `{line}`, h lists them"),
        }
    }

    fn resume(&mut self) -> String {
        let start = self.vm.steps;
        while self.running() {
            self.step();
            if self.running() && self.breaks.contains(&self.vm.pc) {
                return format!("breakpoint\n{}", self.show());
            }
            if self.vm.steps - start >= CONTINUE_STEPS {
                return format!("stopped after {CONTINUE_STEPS} steps\n{}", self.show());
            }
        }
        self.show()
    }

    fn resume_backward(&mut self) -> String {
        let here = self.vm.steps;
        let mut found = None;
        self.replay_to(0);
        while self.running() && self.vm.steps < here {
            if self.breaks.contains(&self.vm.pc) {
                found = Some(self.vm.steps);
            }
            self.step();
        }
        match found {
            Some(step) => {
                self.replay_to(step);
                format!("breakpoint\n{}", self.show())
            }
            None => format!("no earlier breakpoint\n{}", self.show()),
        }
    }

    /// Replays up to the current step, watching each STORE that succeeds.
    fn why(&mut self, cell: i64) -> String {
        let here = self.vm.steps;
        let mut last = None;
        self.replay_to(0);
        while self.running() && self.vm.steps < here {
            let write = match (self.program.get(self.vm.pc), self.vm.stack.as_slice()) {
                (Some(Instr::Store), [.., value, address]) if *address == cell => {
                    Some((self.vm.steps, self.vm.pc, *value))
                }
                _ => None,
            };
            self.step();
            if write.is_some() && self.running() {
                last = write;
            }
        }
        match last {
            Some((step, pc, value)) => format!("[{cell}] last written at step {step}, pc {pc}, with {value}"),
            None => format!("[{cell}] never written, reads 0"),
        }
    }

    fn state(&self) -> String {
        let cells: Vec<String> =
            self.vm.memory.iter().filter(|&(_, &v)| v != 0).map(|(a, v)| format!("[{a}]={v}")).collect();
        format!(
            "{}\nmemory {}\noutput {:?}\nbreakpoints {:?}",
            self.show(),
            cells.join(" "),
            String::from_utf8_lossy(&self.output),
            self.breaks
        )
    }

    fn listing(&self) -> String {
        let from = self.vm.pc.saturating_sub(3);
        let lines: Vec<String> = (from..(from + 7).min(self.program.len()))
            .map(|i| {
                let here = if i == self.vm.pc { ">" } else { " " };
                let mark = if self.breaks.contains(&i) { "*" } else { " " };
                let instr = self.program[i];
                format!("{here}{mark}{i:>5}  {}  {instr}", instr.source())
            })
            .collect();
        lines.join("\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use emd_core::Sym;

    fn push(n: u8) -> Instr {
        Instr::Push(Sym::new(n).unwrap())
    }

    /// 5 stored in cell 3, then 6, then a read and a halt.
    fn program() -> Vec<Instr> {
        vec![
            push(5),
            push(3),
            Instr::Store,
            push(6),
            push(3),
            Instr::Store,
            Instr::Read,
            Instr::Write,
            Instr::Halt,
        ]
    }

    #[test]
    fn back_returns_to_the_same_state_with_input_and_output() {
        let p = program();
        let mut d = Debugger::new(&p, b"A");
        d.command("s 8");
        assert_eq!(d.output, b"A");
        assert_eq!(d.consumed, 1);
        d.command("b 2");
        assert_eq!((d.steps(), d.consumed), (6, 0));
        assert!(d.output.is_empty());
        d.command("s 3");
        assert_eq!(d.show(), "step 9  pc 8  HALT  stack []  halted");
        assert_eq!(d.output, b"A");
    }

    #[test]
    fn breakpoints_stop_both_directions() {
        let p = program();
        let mut d = Debugger::new(&p, b"A");
        d.command("break 2");
        d.command("break 5");
        assert!(d.command("c").contains("step 2  pc 2"));
        assert!(d.command("c").contains("step 5  pc 5"));
        assert!(d.command("rc").contains("step 2  pc 2"));
        assert!(d.command("rc").contains("no earlier breakpoint"));
        assert_eq!(d.steps(), 2);
        d.command("del 5");
        assert!(d.command("c").contains("halted"));
        // Backward means the nearest one, not the first one of the run.
        d.command("break 5");
        assert!(d.command("rc").contains("step 5  pc 5"));
        assert!(d.command("rc").contains("step 2  pc 2"));
    }

    #[test]
    fn why_finds_the_last_write_seen_from_the_current_step() {
        let p = program();
        let mut d = Debugger::new(&p, b"");
        assert!(d.command("why 3").contains("never written"));
        d.command("s 3");
        assert!(d.command("why 3").contains("step 2, pc 2, with 5"));
        d.command("s 3");
        assert!(d.command("why 3").contains("step 5, pc 5, with 6"));
        assert_eq!(d.steps(), 6, "asking does not move the machine");
        assert!(d.command("why 4").contains("never written"));
        assert_eq!(d.command("mem 3"), "[3] = 6");
        d.command("goto 3");
        assert_eq!(d.command("mem 3"), "[3] = 5");
    }

    #[test]
    fn a_step_after_the_end_stays_at_the_end_and_a_fault_can_be_undone() {
        let p = [Instr::Add];
        let mut d = Debugger::new(&p, b"");
        assert!(d.command("s 5").contains("fault: stack underflow"));
        assert_eq!(d.steps(), 1);
        assert!(!d.command("b").contains("fault"));
        assert_eq!(d.steps(), 0);
    }

    #[test]
    fn bad_commands_explain_themselves_and_change_nothing() {
        let p = program();
        let mut d = Debugger::new(&p, b"");
        assert!(d.command("s x").contains("not a number"));
        assert!(d.command("s -1").contains("not a number"));
        assert!(d.command("what").contains("unknown command"));
        assert!(d.command("mem").contains("unknown command"));
        assert!(d.command("h").contains("step back"));
        assert_eq!(d.steps(), 0);
    }

    #[test]
    fn continuing_gives_the_prompt_back_on_an_endless_loop() {
        let p = emd_asm::assemble("PUSH 0 PUSH 3 SUB JMP").unwrap();
        let mut d = Debugger::new(&p, b"");
        assert!(d.command("c").starts_with("stopped after 10000000 steps"));
    }

    #[test]
    fn json_text_escapes_what_json_requires() {
        assert_eq!(json_text("a\"b\\c\n\u{1}"), r#""a\"b\\c\n\u0001""#);
    }

    #[test]
    fn json_carries_the_whole_state() {
        let p = program();
        let mut d = Debugger::new(&p, b"A");
        d.command("break 7");
        let message = d.command("c");
        let line = d.json(&message);
        assert!(line.starts_with(r#"{"step":7,"pc":7,"status":"running","stack":[65],"memory":[[3,6]],"output":[],"breaks":[7],"message":"breakpoint\nstep 7"#), "{line}");
        assert!(!line.contains('\n'), "one line");
        d.command("s 2");
        assert!(
            d.json("say \"hi\"\\\u{1}")
                .contains(r#""output":[65],"breaks":[7],"message":"say \"hi\"\\\u0001"}"#)
        );
        let fault = [Instr::Add];
        let mut f = Debugger::new(&fault, b"");
        f.command("s");
        assert!(f.json("").contains(r#""status":"fault: stack underflow""#));
    }

    #[test]
    fn listing_marks_pc_and_breakpoints() {
        let p = program();
        let mut d = Debugger::new(&p, b"");
        d.command("s 3");
        d.command("break 4");
        let text = d.command("l");
        assert!(text.contains(">     3"), "{text}");
        assert!(text.contains(" *    4"), "{text}");
        assert!(d.command("p").contains("[3]=5"));
    }

    /// Going back lands exactly where going forward passed, for any program.
    #[test]
    fn random_programs_replay_exactly() {
        let all: Vec<Instr> = Instr::all().collect();
        let mut state = 0x2545_F491_4F6C_DD1D_u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..300 {
            let p: Vec<Instr> =
                (0..2 + next() % 30).map(|_| all[(next() % all.len() as u64) as usize]).collect();
            let input: Vec<u8> = (0..next() % 4).map(|_| next() as u8).collect();
            let mut d = Debugger::new(&p, &input);
            let mut seen = Vec::new();
            for _ in 0..60 {
                seen.push((d.show(), d.output.clone(), d.consumed));
                d.command("s");
            }
            for (step, expected) in seen.iter().enumerate() {
                let target = step as u64;
                if target > d.steps() {
                    break;
                }
                d.command(&format!("goto {target}"));
                // A stopped machine shows the same state at each later entry of `seen`.
                assert_eq!(&(d.show(), d.output.clone(), d.consumed), expected, "{p:?}");
            }
        }
    }
}

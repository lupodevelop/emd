// emd: an esoteric language written only in Unicode dashes.
// The machine on hand-written programs, and on random ones.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use super::*;
use emd_core::Sym;

fn asm(text: &str) -> Vec<Instr> {
    let mut out = Vec::new();
    let mut toks = text.split_whitespace();
    while let Some(t) = toks.next() {
        let m = if t == "PUSH" { format!("PUSH {}", toks.next().unwrap()) } else { t.to_string() };
        out.push(Instr::from_mnemonic(&m).unwrap_or_else(|| panic!("{m}")));
    }
    out
}

fn run(text: &str, input: &[u8]) -> (Status, Vec<i64>, Vec<u8>) {
    let program = asm(text);
    // Bounded: a bug must fail the test, not hang it.
    let limits = Limits { max_steps: 1_000_000, ..Limits::default() };
    let mut vm = Vm::new(&program, limits);
    let mut out = Vec::new();
    let status = vm.run(&mut &input[..], &mut out).clone();
    (status, vm.stack, out)
}

#[test]
fn spec_example_leaves_3() {
    let (s, stack, _) = run("PUSH 1 PUSH 2 ADD HALT", b"");
    assert_eq!(s, Status::Halted);
    assert_eq!(stack, [3]);
}

#[test]
fn operand_order_and_truncation() {
    assert_eq!(run("PUSH 2 PUSH 7 SUB HALT", b"").1, [-5]);
    assert_eq!(run("PUSH 7 PUSH 2 DIV HALT", b"").1, [3]);
    assert_eq!(run("PUSH 0 PUSH 7 SUB PUSH 2 DIV HALT", b"").1, [-3]);
    assert_eq!(run("PUSH 0 PUSH 7 SUB PUSH 2 MOD HALT", b"").1, [-1]);
    assert_eq!(run("PUSH 2 PUSH 7 LT HALT", b"").1, [1]);
    assert_eq!(run("PUSH 2 PUSH 7 GT HALT", b"").1, [0]);
    assert_eq!(run("PUSH 0 NOT PUSH 5 NOT HALT", b"").1, [1, 0]);
}

#[test]
fn stack_ops() {
    assert_eq!(run("PUSH 1 PUSH 2 SWAP HALT", b"").1, [2, 1]);
    assert_eq!(run("PUSH 1 PUSH 2 OVER HALT", b"").1, [1, 2, 1]);
    assert_eq!(run("PUSH 1 DUP DROP HALT", b"").1, [1]);
}

#[test]
fn memory() {
    // STORE: value below, address on top.
    assert_eq!(run("PUSH 7 PUSH 3 STORE PUSH 3 LOAD PUSH 4 LOAD HALT", b"").1, [7, 0]);
    assert_eq!(run("PUSH 0 PUSH 1 SUB LOAD HALT", b"").0, Status::Faulted(Fault::NegativeAddress(-1)));
}

#[test]
fn jumps_are_relative_to_the_jump() {
    // JMP at 1 with offset 2 lands on 3 (HALT), skipping PUSH 7.
    assert_eq!(run("PUSH 2 JMP PUSH 7 HALT", b"").1, []);
    assert_eq!(run("PUSH 0 PUSH 3 JZ PUSH 7 HALT HALT", b"").1, []);
    assert_eq!(run("PUSH 1 PUSH 3 JZ PUSH 7 HALT", b"").1, [7]);
    assert_eq!(run("PUSH 1 PUSH 3 JNZ PUSH 7 HALT HALT", b"").1, []);
    // Backward jump: countdown 3,2,1 written as digits ('0' = 48 = 6 + 6*7).
    // DUP is at index 1, JNZ at 27: offset -26 = -(6*5 - 4).
    let (s, stack, out) = run(
        "PUSH 3 \
         DUP PUSH 6 PUSH 7 ADD PUSH 7 ADD PUSH 7 ADD PUSH 7 ADD PUSH 7 ADD PUSH 7 ADD ADD WRITE \
         PUSH 1 SUB DUP PUSH 0 PUSH 6 PUSH 5 MUL PUSH 4 SUB SUB JNZ HALT",
        b"",
    );
    assert_eq!(s, Status::Halted);
    assert_eq!(out, b"321");
    assert_eq!(stack, [0]);
}

#[test]
fn faults() {
    assert_eq!(run("ADD HALT", b"").0, Status::Faulted(Fault::StackUnderflow));
    assert_eq!(run("PUSH 1 PUSH 0 DIV HALT", b"").0, Status::Faulted(Fault::DivisionByZero));
    assert_eq!(run("PUSH 1 PUSH 0 MOD HALT", b"").0, Status::Faulted(Fault::DivisionByZero));
    assert_eq!(run("PUSH 1", b"").0, Status::Faulted(Fault::PcOutOfRange(1)));
    assert_eq!(run("", b"").0, Status::Faulted(Fault::PcOutOfRange(0)));
    assert_eq!(run("PUSH 7 JMP HALT", b"").0, Status::Faulted(Fault::PcOutOfRange(8)));
    // JMP at index 3 with offset -4.
    assert_eq!(run("PUSH 0 PUSH 4 SUB JMP HALT", b"").0, Status::Faulted(Fault::PcOutOfRange(-1)));
    assert_eq!(run("PUSH 0 PUSH 1 SUB WRITE HALT", b"").0, Status::Faulted(Fault::InvalidByte(-1)));
}

#[test]
fn fault_leaves_stack_untouched() {
    let program = asm("PUSH 1 SWAP HALT");
    let mut vm = Vm::new(&program, Limits::default());
    vm.run(&mut &b""[..], &mut Vec::new());
    assert_eq!(vm.status, Status::Faulted(Fault::StackUnderflow));
    assert_eq!(vm.stack, [1]);
    assert_eq!(vm.pc, 1);

    // A jump outside the program: the operands stay.
    let program = asm("PUSH 1 PUSH 7 JNZ HALT");
    let mut vm = Vm::new(&program, Limits::default());
    vm.run(&mut &b""[..], &mut Vec::new());
    assert_eq!(vm.status, Status::Faulted(Fault::PcOutOfRange(9)));
    assert_eq!(vm.stack, [1, 7]);
    assert_eq!(vm.pc, 2);

    // A jump to -1 stops at the jump itself, not one step later at pc -1.
    let program = asm("PUSH 0 PUSH 4 SUB JMP HALT");
    let mut vm = Vm::new(&program, Limits::default());
    vm.run(&mut &b""[..], &mut Vec::new());
    assert_eq!(vm.status, Status::Faulted(Fault::PcOutOfRange(-1)));
    assert_eq!(vm.pc, 3);
    assert_eq!(vm.steps, 4);

    // Last instruction without HALT: the stack stays.
    let program = asm("PUSH 1 DROP");
    let mut vm = Vm::new(&program, Limits::default());
    vm.run(&mut &b""[..], &mut Vec::new());
    assert_eq!(vm.status, Status::Faulted(Fault::PcOutOfRange(2)));
    assert_eq!(vm.stack, [1]);
}

#[test]
fn fault_priority_matches_the_model() {
    // One operand, negative: underflow, not a bad address.
    assert_eq!(run("PUSH 0 PUSH 1 SUB STORE HALT", b"").0, Status::Faulted(Fault::StackUnderflow));
    // An offset that overflows pc + offset is out of range, not an overflow.
    let mut program = emd_max();
    program.extend([Instr::Jmp, Instr::Halt]);
    let mut vm = Vm::new(&program, Limits::default());
    vm.pc = 0;
    vm.run(&mut &b""[..], &mut Vec::new());
    assert!(matches!(vm.status, Status::Faulted(Fault::PcOutOfRange(_))), "{:?}", vm.status);
}

/// Instructions that leave i64::MAX on the stack: 2^62 - 1 + 2^62.
fn emd_max() -> Vec<Instr> {
    let two = Instr::Push(Sym::new(2).unwrap());
    let one = Instr::Push(Sym::new(1).unwrap());
    let mut p = vec![one];
    for _ in 0..62 {
        p.extend([two, Instr::Mul]);
    }
    p.extend([one, Instr::Sub, Instr::Push(Sym::new(1).unwrap())]);
    for _ in 0..62 {
        p.extend([two, Instr::Mul]);
    }
    p.push(Instr::Add);
    p
}

#[test]
fn io() {
    let (s, stack, out) = run("READ WRITE READ HALT", b"A");
    assert_eq!(s, Status::Halted);
    assert_eq!(out, b"A");
    assert_eq!(stack, [-1]);
}

#[test]
fn limits() {
    // JMP at index 3 with offset -3: loops forever.
    let program = asm("PUSH 0 PUSH 3 SUB JMP");
    let mut vm = Vm::new(&program, Limits { max_steps: 5, ..Limits::default() });
    vm.run(&mut &b""[..], &mut Vec::new());
    assert_eq!(vm.status, Status::Faulted(Fault::StepLimit));
    assert_eq!(vm.steps, 5);

    let program = asm("PUSH 1 PUSH 1 HALT");
    let mut vm = Vm::new(&program, Limits { max_stack: 1, ..Limits::default() });
    vm.run(&mut &b""[..], &mut Vec::new());
    assert_eq!(vm.status, Status::Faulted(Fault::StackLimit));

    let program = asm("PUSH 1 PUSH 1 STORE PUSH 1 PUSH 2 STORE HALT");
    let mut vm = Vm::new(&program, Limits { max_cells: 1, ..Limits::default() });
    vm.run(&mut &b""[..], &mut Vec::new());
    assert_eq!(vm.status, Status::Faulted(Fault::MemoryLimit));
}

#[test]
fn overflow_is_a_fault() {
    let mut program = vec![Instr::Push(Sym::new(7).unwrap())];
    for _ in 0..40 {
        program.extend([Instr::Dup, Instr::Mul]);
    }
    program.push(Instr::Halt);
    let mut vm = Vm::new(&program, Limits::default());
    vm.run(&mut &b""[..], &mut Vec::new());
    assert_eq!(vm.status, Status::Faulted(Fault::Overflow));
}

/// `MIN / -1` does not fit, so it faults. `MIN % -1` is 0, as in the model.
#[test]
fn min_by_minus_one() {
    let run = |instr| {
        let program = [instr, Instr::Halt];
        let mut vm = Vm::new(&program, Limits::default());
        vm.stack = vec![i64::MIN, -1];
        vm.run(&mut &b""[..], &mut Vec::new());
        (vm.status.clone(), vm.stack.clone())
    };
    assert_eq!(run(Instr::Div), (Status::Faulted(Fault::Overflow), vec![i64::MIN, -1]));
    assert_eq!(run(Instr::Mod), (Status::Halted, vec![0]));
}

fn xorshift(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

/// Every program stops within the limits without a panic, and a fault keeps the state.
#[test]
fn random_programs_terminate_and_faults_preserve_state() {
    let all: Vec<Instr> = Instr::all().collect();
    let mut s = 0xDEAD_BEEF_CAFE_F00D_u64;
    let limits = Limits { max_steps: 2_000, max_stack: 64, max_cells: 16 };
    let mut faults = 0;
    for _ in 0..2000 {
        let len = 1 + (xorshift(&mut s) % 12) as usize;
        let program: Vec<Instr> =
            (0..len).map(|_| all[(xorshift(&mut s) % all.len() as u64) as usize]).collect();
        let input: Vec<u8> = (0..xorshift(&mut s) % 4).map(|_| (xorshift(&mut s) % 256) as u8).collect();
        let mut vm = Vm::new(&program, limits);
        let (mut input, mut out) = (&input[..], Vec::new());
        loop {
            let (stack, memory, pc) = (vm.stack.clone(), vm.memory.clone(), vm.pc);
            match vm.step(&mut input, &mut out).clone() {
                Status::Running => assert!(vm.pc < program.len()),
                Status::Halted => break,
                Status::Faulted(f) => {
                    faults += 1;
                    assert_eq!((&vm.stack, &vm.memory, vm.pc), (&stack, &memory, pc), "{f}");
                    break;
                }
            }
        }
        assert!(vm.steps <= limits.max_steps);
        assert!(vm.stack.len() <= limits.max_stack);
        assert!(vm.memory.len() <= limits.max_cells);
    }
    assert!(faults > 100);
}

/// The machine's whole state after every step, then the output.
fn trace(program: &[Instr], input: &[u8], limits: Limits) -> (Vec<String>, Vec<u8>) {
    let mut vm = Vm::new(program, limits);
    let (mut input, mut out, mut states) = (input, Vec::new(), Vec::new());
    while vm.status == Status::Running {
        vm.step(&mut input, &mut out);
        states.push(format!(
            "{} {} {:?} {:?} {:?} {}",
            vm.pc,
            vm.steps,
            vm.stack,
            vm.memory,
            vm.status,
            input.len()
        ));
    }
    (states, out)
}

/// Same program, same input: the same state at every step, and the same output.
#[test]
fn runs_are_deterministic_step_by_step() {
    let all: Vec<Instr> = Instr::all().collect();
    let mut s = 0x0123_4567_89AB_CDEF_u64;
    let limits = Limits { max_steps: 500, max_stack: 64, max_cells: 16 };
    let mut longest = 0;
    for _ in 0..1000 {
        let len = 1 + (xorshift(&mut s) % 16) as usize;
        let program: Vec<Instr> =
            (0..len).map(|_| all[(xorshift(&mut s) % all.len() as u64) as usize]).collect();
        let input: Vec<u8> = (0..xorshift(&mut s) % 4).map(|_| (xorshift(&mut s) % 256) as u8).collect();
        let first = trace(&program, &input, limits);
        longest = longest.max(first.0.len());
        assert_eq!(first, trace(&program, &input, limits));
    }
    assert!(longest > 2);
}

#[test]
fn every_fault_says_what_happened() {
    for (fault, text) in [
        (Fault::StackUnderflow, "stack underflow"),
        (Fault::DivisionByZero, "division by zero"),
        (Fault::NegativeAddress(-2), "negative address -2"),
        (Fault::PcOutOfRange(9), "pc 9 is outside the program"),
        (Fault::InvalidByte(256), "256 is not a byte"),
        (Fault::Overflow, "64-bit overflow (implementation limit)"),
        (Fault::StepLimit, "step limit reached"),
        (Fault::StackLimit, "stack limit reached"),
        (Fault::MemoryLimit, "memory cell limit reached"),
        (Fault::Io("gone".into()), "i/o error: gone"),
    ] {
        assert_eq!(fault.to_string(), text);
    }
}

#[test]
fn a_stopped_machine_stays_stopped() {
    let program = asm("PUSH 1 HALT");
    let mut vm = Vm::new(&program, Limits::default());
    vm.run(&mut &b""[..], &mut Vec::new());
    let steps = vm.steps;
    assert_eq!(vm.step(&mut &b""[..], &mut Vec::new()), &Status::Halted);
    assert_eq!(vm.steps, steps);
}

#[test]
fn growing_the_stack_past_its_limit_faults() {
    for (text, max_stack) in [("PUSH 1 PUSH 2 OVER HALT", 2), ("READ HALT", 0)] {
        let program = asm(text);
        let mut vm = Vm::new(&program, Limits { max_stack, ..Limits::default() });
        assert_eq!(vm.run(&mut &b"x"[..], &mut Vec::new()), &Status::Faulted(Fault::StackLimit), "{text}");
    }
}

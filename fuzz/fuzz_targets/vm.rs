// emd: an esoteric language written only in Unicode dashes.
// A decoded program stops within low limits without a panic, and a fault keeps the state.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

#![no_main]
use emd_core::Instr;
use emd_vm::{Limits, Status, Vm};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let all: Vec<Instr> = Instr::all().collect();
    // First bytes are the input; the rest pick instructions, so that any bytes run.
    let (input, code) = data.split_at(data.len().min(4));
    let program: Vec<Instr> = code.iter().map(|b| all[*b as usize % all.len()]).collect();
    let limits = Limits { max_steps: 2_000, max_stack: 64, max_cells: 16 };
    let mut vm = Vm::new(&program, limits);
    let (mut input, mut out) = (input, Vec::new());
    loop {
        let (stack, memory, pc) = (vm.stack.clone(), vm.memory.clone(), vm.pc);
        match vm.step(&mut input, &mut out).clone() {
            Status::Running => assert!(vm.pc < program.len()),
            Status::Halted => break,
            Status::Faulted(_) => {
                assert_eq!((&vm.stack, &vm.memory, vm.pc), (&stack, &memory, pc));
                break;
            }
        }
    }
    assert!(vm.steps <= limits.max_steps);
    assert!(vm.stack.len() <= limits.max_stack);
    assert!(vm.memory.len() <= limits.max_cells);
});

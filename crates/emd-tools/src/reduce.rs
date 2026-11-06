// emd: an esoteric language written only in Unicode dashes.
// Shrinks a program to a smaller one that behaves the same on the same input.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::Instr;
use emd_vm::{Limits, Status, Vm};
use std::mem::discriminant;

type Outcome = (Vec<u8>, Option<std::mem::Discriminant<emd_vm::Fault>>);

/// Output and how it ended. `None` if it did not end within the limit.
fn outcome(program: &[Instr], input: &[u8], max_steps: u64) -> Option<Outcome> {
    let mut vm = Vm::new(program, Limits { max_steps, ..Limits::default() });
    let mut output = Vec::new();
    vm.run(&mut &input[..], &mut output);
    // The machine has stopped: it halted unless it faulted.
    match &vm.status {
        Status::Faulted(emd_vm::Fault::StepLimit) => None,
        Status::Faulted(f) => Some((output, Some(discriminant(f)))),
        _ => Some((output, None)),
    }
}

/// `None` if the program does not end within `max_steps`: nothing to preserve.
pub fn reduce(program: &[Instr], input: &[u8], max_steps: u64) -> Option<Vec<Instr>> {
    let goal = outcome(program, input, max_steps)?;
    let mut current = program.to_vec();
    loop {
        let before = current.len();
        let mut size = current.len().div_ceil(2).max(1);
        while size >= 1 {
            let mut start = 0;
            while start < current.len() {
                let end = (start + size).min(current.len());
                let mut candidate = current[..start].to_vec();
                candidate.extend_from_slice(&current[end..]);
                if outcome(&candidate, input, max_steps).as_ref() == Some(&goal) {
                    current = candidate;
                } else {
                    start += size;
                }
            }
            size /= 2;
        }
        if current.len() == before {
            return Some(current);
        }
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
    fn noise_goes_and_the_fault_stays() {
        let p = [
            push(1),
            push(2),
            Instr::Add,
            Instr::Drop,
            push(3),
            Instr::Drop,
            push(1),
            push(0),
            Instr::Div,
            Instr::Halt,
        ];
        let small = reduce(&p, b"", 1000).unwrap();
        assert_eq!(small.len(), 3, "{small:?}");
        assert_eq!(small[1..], [push(0), Instr::Div]);
    }

    #[test]
    fn output_is_kept_byte_for_byte() {
        let p = [push(1), Instr::Drop, push(7), Instr::Write, push(2), Instr::Drop, Instr::Halt];
        let small = reduce(&p, b"", 1000).unwrap();
        assert_eq!(small, [push(7), Instr::Write, Instr::Halt]);
    }

    #[test]
    fn input_counts_and_a_loop_is_refused() {
        let p = [Instr::Read, Instr::Write, Instr::Halt];
        assert_eq!(reduce(&p, b"A", 1000).unwrap(), p, "nothing here can go");
        let looping = [push(0), push(3), Instr::Sub, Instr::Jmp];
        assert_eq!(reduce(&looping, b"", 1000), None);
        assert_eq!(reduce(&[], b"", 1000).unwrap(), []);
    }

    #[test]
    fn any_reduction_behaves_like_the_original() {
        let all: Vec<Instr> = Instr::all().collect();
        let mut state = 0xD1B5_4A32_D192_ED03_u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..300 {
            let p: Vec<Instr> =
                (0..1 + next() % 24).map(|_| all[(next() % all.len() as u64) as usize]).collect();
            if let Some(small) = reduce(&p, b"xy", 500) {
                assert!(small.len() <= p.len());
                assert_eq!(outcome(&small, b"xy", 500), outcome(&p, b"xy", 500), "{p:?}");
            }
        }
    }
}

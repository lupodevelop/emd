// emd: an esoteric language written only in Unicode dashes.
// Kani harnesses: integer synthesis, by its base case and its step, and the jump layout.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::codegen::{fixed_point, push_int, push_len, seven_times_plus};
use emd_core::Instr;

/// What `program` leaves on a stack that holds `start`, computed on i128. Every intermediate
/// value must fit 64 bits, or the VM would fault on it.
fn pushed(start: &[i128], program: &[Instr]) -> i128 {
    let (mut stack, mut depth) = ([0i128; 3], start.len());
    stack[..depth].copy_from_slice(start);
    for instr in program {
        if let Instr::Push(n) = instr {
            stack[depth] = i128::from(n.index());
            depth += 1;
            continue;
        }
        let (a, b) = (stack[depth - 2], stack[depth - 1]);
        let r = match instr {
            Instr::Add => a + b,
            Instr::Sub => a - b,
            Instr::Mul => a * b,
            _ => panic!("not part of a synthesis"),
        };
        assert!(i128::from(i64::MIN) <= r && r <= i128::from(i64::MAX));
        depth -= 1;
        stack[depth - 1] = r;
    }
    assert_eq!(depth, 1);
    stack[0]
}

/// The base case: below 8, the value is one literal. Eight values, each checked.
#[kani::proof]
#[kani::unwind(9)]
fn small_values_are_one_literal() {
    for small in 0..8u8 {
        let program = push_int(i64::from(small));
        assert_eq!(program.len(), 1);
        assert_eq!(pushed(&[], &program), i128::from(small));
    }
}

/// The step, for every value: after the instructions for `n / 7`, it pushes `n` without
/// overflow. With the base case, every magnitude up to i64::MAX is pushed exactly, by
/// induction on its digits in base 7. Parsing rejects i64::MIN.
#[kani::proof]
#[kani::unwind(5)]
fn each_base_7_digit_adds_up() {
    let n: u64 = kani::any();
    kani::assume((8..=i64::MAX as u64).contains(&n));
    let mut step = Vec::with_capacity(4);
    seven_times_plus(n % 7, &mut step);
    assert_eq!(pushed(&[i128::from(n / 7)], &step), i128::from(n));
    assert_eq!(step.len(), if n % 7 == 0 { 2 } else { 4 });
}

/// The sign: a negative value is 0, its magnitude, and SUB, which cannot overflow.
#[kani::proof]
fn a_negative_value_is_zero_minus_its_magnitude() {
    let n: i64 = kani::any();
    kani::assume(n > 0);
    assert_eq!(pushed(&[0, i128::from(n)], &[Instr::Sub]), -i128::from(n));
}

/// `push_len` follows the same digits: one literal, then 2 or 4 per digit, then 2 for the sign.
/// Below 2^24 in size: on all of i64 the solver does not finish, so the unit tests check the
/// length at every power of 7 up to i64::MAX instead.
#[kani::proof]
#[kani::unwind(11)]
fn the_length_follows_the_digits() {
    let value: i64 = kani::any();
    kani::assume(value.unsigned_abs() < 1 << 24);
    let n = value.unsigned_abs() as i64;
    let step = if n % 7 == 0 { 2 } else { 4 };
    if value < 0 {
        assert_eq!(push_len(value), push_len(n) + 2);
    } else if n < 8 {
        assert_eq!(push_len(n), 1);
    } else {
        assert_eq!(push_len(n), push_len(n / 7) + step);
    }
}

const ITEMS: usize = 4;

/// Up to 4 items of up to 20 instructions, two jumps between them: every slot holds its offset,
/// with an even remainder for the no-op pairs, and the addresses add up.
#[kani::proof]
#[kani::unwind(12)]
fn every_jump_slot_holds_its_offset() {
    let sizes: [i64; ITEMS] = std::array::from_fn(|_| kani::any());
    let jumps: [(usize, usize); 2] = std::array::from_fn(|_| (kani::any(), kani::any()));
    for &size in &sizes {
        kani::assume((0..=20).contains(&size));
    }
    for &(jump, label) in &jumps {
        kani::assume(jump < ITEMS && label < ITEMS && sizes[jump] == 1);
    }
    kani::assume(jumps[0].0 != jumps[1].0);
    let layout = fixed_point(&sizes, &jumps);
    let mut pc = 0;
    for i in 0..ITEMS {
        assert_eq!(layout.addresses[i], pc);
        pc += sizes[i] + layout.slots[i] as i64;
    }
    assert_eq!(layout.total as i64, pc);
    for &(jump, label) in &jumps {
        let offset = layout.addresses[label] - (layout.addresses[jump] + layout.slots[jump] as i64);
        let need = push_len(offset);
        assert!(layout.slots[jump] >= need && (layout.slots[jump] - need) % 2 == 0);
    }
}

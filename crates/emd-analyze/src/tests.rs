// emd: an esoteric language written only in Unicode dashes.
// The analysis against its examples, the VM and the proved mirror.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::transfer::on_bounds;
use crate::value::{Cmp, MAX_VALUES};
use crate::{Analysis, Kind, Stacks, Val, analyze, cfg};
use emd_core::Instr;
use emd_core::Sym;
use emd_vm::{Fault, Limits, Status, Vm};
use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

fn push(n: u8) -> Instr {
    Instr::Push(Sym::new(n).unwrap())
}

fn kinds(program: &[Instr]) -> Vec<Kind> {
    analyze(program).issues.iter().map(|i| i.kind).collect()
}

fn depth(a: &Analysis, pc: usize, stack: &[Val]) -> bool {
    a.stacks[pc].by_depth.get(&stack.len()).is_some_and(|f| f.stack.iter().map(|c| &c.val).eq(stack))
}

fn set(values: impl IntoIterator<Item = i64>) -> Val {
    Val::of(values.into_iter().collect())
}

#[test]
fn straight_line_code_is_proved() {
    let p = [push(1), push(2), Instr::Add, Instr::Drop, Instr::Halt];
    let a = analyze(&p);
    assert!(a.is_clean(), "{a}");
    assert!(depth(&a, 2, &[Val::one(1), Val::one(2)]));
    assert!(depth(&a, 3, &[Val::one(3)]));
}

#[test]
fn constant_jumps_are_followed_and_dead_code_found() {
    // PUSH 2, JMP to index 3 skipping the ADD at 2.
    let p = [push(2), Instr::Jmp, Instr::Add, Instr::Halt];
    let a = analyze(&p);
    assert!(!a.stacks[2].reached(), "ADD is dead");
    assert!(a.is_clean(), "{a}");
    assert!(a.to_string().contains("dead code at pc [2]"));
}

#[test]
fn known_faults_are_certain() {
    let certain = |p: &[Instr], kind| {
        assert!(analyze(p).issues.iter().any(|i| i.kind == kind && i.certain), "{p:?}");
    };
    certain(&[Instr::Add], Kind::StackUnderflow);
    certain(&[push(1), push(0), Instr::Div, Instr::Halt], Kind::DivisionByZero);
    certain(&[push(0), push(1), Instr::Sub, Instr::Load, Instr::Halt], Kind::NegativeAddress);
    certain(&[push(0), push(1), Instr::Sub, Instr::Write, Instr::Halt], Kind::InvalidByte);
    certain(&emd_asm::assemble("PUSH 256 WRITE HALT").unwrap(), Kind::InvalidByte);
    assert!(analyze(&emd_asm::assemble("PUSH 255 WRITE HALT").unwrap()).is_clean(), "255 is a byte");
    assert!(kinds(&[push(0)]).contains(&Kind::PcOutOfRange), "falls off the end");
    assert!(kinds(&[]).contains(&Kind::PcOutOfRange));
}

#[test]
fn input_makes_values_unknown_not_faults() {
    let p = [Instr::Read, Instr::Drop, Instr::Halt];
    assert!(analyze(&p).is_clean());
    let p = [Instr::Read, Instr::Write, Instr::Halt];
    assert_eq!(kinds(&p), [Kind::InvalidByte], "READ can give -1");
    // READ is known to be a byte or -1, so a jump by it has known targets.
    let p = [Instr::Read, Instr::Jmp, Instr::Halt];
    assert!(!analyze(&p).stacks[2].unknown);
    // A product of two of them is past what is enumerated, so this jump can go anywhere.
    let p = [Instr::Read, Instr::Read, Instr::Mul, Instr::Jmp, Instr::Halt];
    assert!(analyze(&p).stacks[4].unknown, "a wild jump reaches everything");
}

#[test]
fn a_counting_loop_stays_bounded_by_its_own_test() {
    // 3, then: 1 SUB DUP, offset back to the 1: 0 6 SUB, JNZ, DROP, HALT.
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
    let a = analyze(&p);
    assert!(a.is_clean(), "{a}");
    assert!(depth(&a, 1, &[set([1, 2, 3])]), "{:?}", a.stacks[1]);
}

#[test]
fn a_test_on_a_copy_narrows_the_original() {
    // READ DUP +1 JZ end; WRITE; JMP back; end: DROP HALT. Past the JZ it cannot be -1.
    let p = [
        Instr::Read,
        Instr::Dup,
        push(1),
        Instr::Add,
        push(5),
        Instr::Jz, // 0..5, JZ to 10
        Instr::Write,
        push(0),
        push(7),
        Instr::Sub, // 6..9
        Instr::Drop,
        Instr::Halt,
    ];
    let a = analyze(&p);
    assert!(!a.issues.iter().any(|i| i.kind == Kind::InvalidByte), "{a}");
    assert!(depth(&a, 6, &[set(0..=255)]), "{:?}", a.stacks[6].by_depth.keys());
}

#[test]
fn memory_is_tracked_per_cell() {
    // 5 into cell 3, 6 into cell 4, read cell 3: 5, and cell 9: still 0.
    let p = [
        push(5),
        push(3),
        Instr::Store,
        push(6),
        push(4),
        Instr::Store,
        push(3),
        Instr::Load,
        push(7),
        push(2),
        Instr::Add,
        Instr::Load,
        Instr::Halt,
    ];
    let a = analyze(&p);
    assert!(depth(&a, 8, &[Val::one(5)]), "{:?}", a.stacks[8]);
    assert!(depth(&a, 12, &[Val::one(5), Val::one(0)]), "{:?}", a.stacks[12]);
    assert_eq!(a.stacks[8].by_depth[&1].cell(4), Val::one(6));
    assert_eq!(a.stacks[8].by_depth[&1].cell(100), Val::one(0));
}

#[test]
fn a_write_to_an_unknown_address_reaches_every_cell() {
    // 7 goes to an address read from input, then cell 3 is read.
    let p = [push(7), Instr::Read, Instr::Store, push(3), Instr::Load, Instr::Halt];
    let a = analyze(&p);
    assert!(a.stacks[5].by_depth[&1].stack[0].val.contains(0));
    assert!(a.stacks[5].by_depth[&1].stack[0].val.contains(7), "{:?}", a.stacks[5]);
}

#[test]
fn a_symbol_read_again_forgets_the_old_value() {
    // A test on the new byte says nothing about the old one. Loop: READ, if -1 leave.
    let p = [
        Instr::Read,
        Instr::Dup,
        push(1),
        Instr::Add,
        Instr::Not, // 0..4: 1 if -1
        push(0),
        push(6),
        Instr::Sub,
        Instr::Add, // nonsense on purpose: stays sound
        Instr::Drop,
        Instr::Halt,
    ];
    assert!(analyze(&p).halt_reachable);
    let looped = [Instr::Read, push(0), push(1), Instr::Sub, Instr::Jz, Instr::Halt];
    let a = analyze(&looped);
    assert!(a.stacks[0].reached());
}

/// OVER must not give its copy a fresh symbol while the top keeps the old one: it hid a fault.
#[test]
fn over_in_a_loop_does_not_keep_a_stale_symbol() {
    let p = emd_asm::assemble(
        "PUSH 0 PUSH 1\n\
         again: OVER PUSH 0 LOAD JNZ second\n\
         PUSH 5 SWAP PUSH 1 PUSH 0 STORE JMP again\n\
         second: JNZ boom HALT\n\
         boom: PUSH 1 PUSH 0 DIV HALT\n",
    )
    .unwrap();
    let mut vm = Vm::new(&p, Limits { max_steps: 200, ..Limits::default() });
    vm.run(&mut &b""[..], &mut std::io::sink());
    assert_eq!(vm.status, Status::Faulted(Fault::DivisionByZero));
    let a = analyze(&p);
    assert!(a.stacks[vm.pc].reached(), "{a}");
    assert!(a.issues.iter().any(|i| i.kind == Kind::DivisionByZero && i.pc == vm.pc), "{a}");
}

#[test]
fn a_test_after_subtracting_a_constant_narrows_by_that_constant() {
    // READ; x - 1 == 0 jumps to the HALT, so x is 1 there; otherwise x is not 1.
    let p =
        [Instr::Read, Instr::Dup, push(1), Instr::Sub, push(3), Instr::Jz, push(0), Instr::Halt, Instr::Halt];
    let a = analyze(&p);
    assert!(depth(&a, 8, &[Val::one(1)]), "{:?}", a.stacks[8]);
    assert!(!a.stacks[7].by_depth[&2].stack[0].val.contains(1), "{:?}", a.stacks[7]);
}

/// `10 < x` and `x < 10` narrow `x` in opposite directions.
#[test]
fn a_comparison_with_the_constant_first_narrows_the_right_way() {
    let last_two = |source: &str| {
        let p = emd_asm::assemble(source).unwrap();
        let a = analyze(&p);
        let at = |pc: usize| a.stacks[pc].by_depth[&1].stack[0].val.clone();
        (at(p.len() - 2), at(p.len() - 1))
    };
    // Falls through when the test is false, jumps when it is true.
    let (not_less, less) = last_two("READ DUP PUSH 10 SWAP LT JNZ yes\nHALT\nyes: HALT\n");
    assert_eq!((not_less.bounds(), less.bounds()), ((-1, 10), (11, 255)));
    let (not_more, more) = last_two("READ DUP PUSH 10 SWAP GT JNZ yes\nHALT\nyes: HALT\n");
    assert_eq!((not_more.bounds(), more.bounds()), ((10, 255), (-1, 9)));
    let (not_equal, equal) = last_two("READ DUP PUSH 10 SWAP EQ JNZ yes\nHALT\nyes: HALT\n");
    assert_eq!((not_equal.contains(10), equal), (false, Val::one(10)));
    let (x_not_less, x_less) = last_two("READ DUP PUSH 10 LT JNZ yes\nHALT\nyes: HALT\n");
    assert_eq!((x_not_less.bounds(), x_less.bounds()), ((10, 255), (-1, 9)));
}

#[test]
fn a_branch_that_cannot_happen_is_dead() {
    // 2 EQ 3 is 0 for sure: the JNZ never jumps. The DROP HALT after it is all that runs.
    let p = [push(2), push(3), Instr::Eq, push(3), Instr::Jnz, Instr::Halt, Instr::Add, Instr::Halt];
    let a = analyze(&p);
    assert!(!a.stacks[6].reached(), "{a}");
}

#[test]
fn each_depth_is_analyzed_on_its_own() {
    // If c = 0 jump over an extra push, then pop twice. At pc 5 the depth is 0 or 2.
    let p = [Instr::Read, push(3), Instr::Jz, push(1), push(2), Instr::Drop, Instr::Drop, Instr::Halt];
    let a = analyze(&p);
    assert_eq!(a.stacks[5].by_depth.keys().copied().collect::<Vec<_>>(), [0, 2]);
    assert!(!a.stacks[5].unknown);
    let issue = a.issues.iter().find(|i| i.kind == Kind::StackUnderflow).unwrap();
    assert_eq!((issue.pc, issue.certain), (5, false), "only one way of reaching it faults");
    assert!(!a.is_clean());
}

#[test]
fn a_routine_with_many_callers_returns_to_each_of_them() {
    // CALL at 1 lands on the RET at 5, back to 2; CALL at 3 lands on it too, back to 4.
    let two = [push(4), Instr::Call, push(2), Instr::Call, Instr::Halt, Instr::Ret];
    let a = analyze(&two);
    assert!(a.is_clean(), "{a}");
    assert!(depth(&a, 5, &[set([2, 4])]), "{:?}", a.stacks[5]);
    assert!(a.edges.contains(&(5, 2)) && a.edges.contains(&(5, 4)));
}

#[test]
fn callers_at_different_depths_do_not_blur() {
    // One caller has an extra value under the call. Both come back with the right depth.
    let p = [
        push(6),
        Instr::Call, // to 7
        push(1),
        push(3),
        Instr::Call, // to 7, with a 1 underneath
        Instr::Drop,
        Instr::Halt, // 5, 6
        Instr::Ret,  // 7
    ];
    let a = analyze(&p);
    assert!(a.is_clean(), "{a}");
    assert_eq!(a.stacks[7].by_depth.keys().copied().collect::<Vec<_>>(), [1, 2]);
    assert!(!a.stacks[7].unknown);
}

#[test]
fn an_argument_keeps_its_possible_values_through_a_routine() {
    // WRITE of 1 or 2 through one routine: both are bytes, and the analysis knows.
    let a = analyze(&[
        push(1),
        push(5),
        Instr::Call, // CALL at 2 to 7
        push(2),
        push(2),
        Instr::Call, // CALL at 5 to 7
        Instr::Halt,
        Instr::Swap,
        Instr::Write,
        Instr::Ret, // 7: the routine
    ]);
    assert!(a.is_clean(), "{a}");
    assert!(depth(&a, 8, &[set([3, 6]), set([1, 2])]), "{:?}", a.stacks[8]);
}

#[test]
fn unbounded_recursion_is_reported_not_guessed() {
    // A routine that calls itself before returning: the depth grows without limit.
    let p = [push(2), Instr::Call, Instr::Halt, push(0), push(3), Instr::Sub, Instr::Call, Instr::Ret];
    let a = analyze(&p);
    assert!(a.stacks[3].unknown || a.stacks[4].unknown, "{:?}", a.stacks[3]);
    assert!(!a.is_clean());
    assert!(a.to_string().contains("not proved"), "{a}");

    // A return address nothing is known about cannot be followed.
    let p = [Instr::Read, Instr::Read, Instr::Mul, Instr::Ret, Instr::Halt];
    let a = analyze(&p);
    assert!(a.issues.iter().any(|i| i.kind == Kind::UnknownJump && i.pc == 3), "{a}");
}

#[test]
fn a_value_with_too_many_possibilities_becomes_unknown() {
    let many: BTreeSet<i64> = (0..MAX_VALUES as i64).collect();
    let one_more = Val::of(many).join(&Val::one(1000));
    assert_eq!(one_more, Val::range(0, 1000), "past sets, an interval");
    assert_eq!(Val::one(1).join(&Val::one(2)), set([1, 2]));
    assert!(Val::Unknown.contains(7) && !Val::one(1).contains(7));
    assert_eq!(Val::range(i64::MIN, i64::MAX), Val::Unknown);
    assert_eq!(Val::range(3, 3), Val::one(3));
    // A moved bound is lost, a bound that held stays.
    assert_eq!(Val::range(0, 10).widened_from(&Val::range(0, 9)), Val::Range(0, i64::MAX));
    assert_eq!(Val::range(-1, 9).widened_from(&Val::range(0, 9)), Val::Range(i64::MIN, 9));
}

#[test]
fn narrowing_an_interval_moves_its_bounds() {
    let r = Val::range(0, 9);
    assert_eq!(r.restrict(Cmp::Lt, 5), Some(Val::range(0, 4)));
    assert_eq!(r.restrict(Cmp::Ge, 5), Some(Val::range(5, 9)));
    assert_eq!(r.restrict(Cmp::Gt, 8), Some(Val::one(9)));
    assert_eq!(r.restrict(Cmp::Eq, 3), Some(Val::one(3)));
    assert_eq!(r.restrict(Cmp::Eq, 30), None, "cannot happen");
    assert_eq!(r.restrict(Cmp::Lt, 0), None);
    assert_eq!(r.restrict(Cmp::Ne, 0), Some(Val::range(1, 9)));
    assert_eq!(r.restrict(Cmp::Ne, 4), Some(r.clone()), "a hole is not an interval");
    assert_eq!(set([1, 2, 3]).restrict(Cmp::Ne, 2), Some(set([1, 3])));
    assert_eq!(Val::Unknown.restrict(Cmp::Ge, 0), Some(Val::Range(0, i64::MAX)));
}

#[test]
fn bounds_cover_what_the_machine_computes() {
    let (a, b) = (Val::range(-5, 5), Val::range(1, 3));
    let cases = [Instr::Add, Instr::Sub, Instr::Eq, Instr::Lt, Instr::Gt, Instr::Mod];
    for instr in cases {
        let result = on_bounds(instr, &a, &b);
        for x in -5..=5i64 {
            for y in 1..=3i64 {
                let v = match instr {
                    Instr::Add => x + y,
                    Instr::Sub => x - y,
                    Instr::Eq => i64::from(x == y),
                    Instr::Lt => i64::from(x < y),
                    Instr::Gt => i64::from(x > y),
                    _ => x % y,
                };
                assert!(result.contains(v), "{instr} {x} {y}: {result:?}");
            }
        }
    }
    assert_eq!(on_bounds(Instr::Mod, &Val::Unknown, &Val::one(256)), Val::range(-255, 255));
    assert_eq!(on_bounds(Instr::Mod, &Val::Range(0, i64::MAX), &Val::one(256)), Val::range(0, 255));
    assert_eq!(on_bounds(Instr::Add, &Val::Range(0, i64::MAX), &Val::one(1)), Val::Range(1, i64::MAX));
    assert_eq!(on_bounds(Instr::Lt, &Val::range(0, 3), &Val::range(4, 9)), Val::one(1));
    assert_eq!(on_bounds(Instr::Eq, &Val::range(0, 3), &Val::range(4, 9)), Val::one(0));
}

#[test]
fn a_store_through_an_interval_leaves_other_cells_alone() {
    // Cell 0 holds 5. The address is a byte or -1, plus 3: at least 2, and too many to list.
    let p = emd_asm::assemble("PUSH 5 STORE 0\nPUSH 9 READ PUSH 3 ADD STORE\nLOAD 0 PUSH 40 LOAD HALT\n")
        .unwrap();
    let a = analyze(&p);
    let last = a.stacks.last().unwrap();
    let frame = &last.by_depth[&2];
    assert_eq!(frame.stack[0].val, Val::one(5), "{a}");
    assert!(frame.stack[1].val.contains(9) && frame.stack[1].val.contains(0), "cell 40 may be either");
}

#[test]
fn compiled_programs_are_proved() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let load = |name: &str| emd_parser::parse_bytes(&std::fs::read(root.join(name)).unwrap()).unwrap();
    let hello = analyze(&load("hello.emd"));
    assert!(hello.is_clean(), "{hello}");
    assert!(hello.edges.iter().all(|&(a, b)| b == a + 1), "hello runs straight");
    for name in ["functions.emd", "add.emd", "cat.emd", "truth.emd", "fizzbuzz.emd", "brainfuck.emd"] {
        let a = analyze(&load(name));
        assert!(a.is_clean(), "{name}: {a}");
    }
    let fizzbuzz = analyze(&load("fizzbuzz.emd"));
    assert!(
        fizzbuzz.issues.iter().all(|i| i.kind != Kind::StackUnderflow && i.kind != Kind::UnknownJump),
        "{fizzbuzz}"
    );
}

#[test]
fn cfg_is_graphviz_with_one_block_per_branch() {
    let p = [Instr::Read, push(3), Instr::Jz, push(1), Instr::Drop, Instr::Halt];
    let dot = cfg(&p);
    assert!(dot.starts_with("digraph emd {"));
    assert!(dot.contains("b0 -> b3"), "{dot}");
    assert!(dot.contains("b0 -> b5"), "{dot}");
    assert!(dot.contains("5: HALT"), "{dot}");
    assert_eq!(cfg(&[]).lines().count(), 3, "{}", cfg(&[]));
}

fn analyzed_kind(fault: &Fault) -> Option<Kind> {
    match fault {
        Fault::StackUnderflow => Some(Kind::StackUnderflow),
        Fault::PcOutOfRange(_) => Some(Kind::PcOutOfRange),
        Fault::DivisionByZero => Some(Kind::DivisionByZero),
        Fault::NegativeAddress(_) => Some(Kind::NegativeAddress),
        Fault::InvalidByte(_) => Some(Kind::InvalidByte),
        _ => None,
    }
}

fn matches(concrete: &[i64], memory: &BTreeMap<i64, i64>, stacks: &Stacks) -> bool {
    if stacks.unknown {
        return true;
    }
    stacks.by_depth.get(&concrete.len()).is_some_and(|f| {
        f.stack.iter().zip(concrete).all(|(a, c)| a.val.contains(*c))
            && f.mem.iter().all(|(a, cell)| cell.val.contains(memory.get(a).copied().unwrap_or(0)))
            && memory.iter().all(|(a, v)| f.cell(*a).contains(*v))
    })
}

/// Random code with a bounded backward jump: the program and the loop head.
fn looping_program(next: &mut impl FnMut() -> u64) -> (Vec<Instr>, usize) {
    let body = [
        Instr::Over,
        Instr::Dup,
        Instr::Swap,
        Instr::Rot,
        Instr::Read,
        Instr::Drop,
        Instr::Add,
        Instr::Sub,
        Instr::Eq,
        Instr::Lt,
        Instr::Gt,
        Instr::Not,
        Instr::Load,
        Instr::Store,
    ];
    let mut p: Vec<Instr> = (0..3 + next() % 4).map(|_| push((next() % 3) as u8)).collect();
    let head = p.len();
    for _ in 0..2 + next() % 7 {
        match next() % 6 {
            0 => p.push(push((next() % 4) as u8)),
            // Skips the next instruction on a condition.
            1 => p.extend([push(2), [Instr::Jz, Instr::Jnz][(next() % 2) as usize]]),
            2 => p.extend([
                Instr::Dup,
                push((next() % 4) as u8),
                Instr::Swap,
                [Instr::Eq, Instr::Lt, Instr::Gt][(next() % 3) as usize],
            ]),
            _ => p.push(body[(next() % body.len() as u64) as usize]),
        }
    }
    // A divisor that may be zero, after everything the loop may have proved about it.
    if next().is_multiple_of(2) {
        p.extend([Instr::Dup, push(1), Instr::Swap, Instr::Div, Instr::Drop]);
    }
    // Cell 6 counts the turns: 3 at most. 0 - (7a + b) is the way back.
    let at = p.len() + 8 + 7 + 1;
    let back = (at - head) as u64;
    p.extend([push(6), Instr::Load, push(1), Instr::Add, Instr::Dup, push(6), Instr::Store, push(3)]);
    p.extend([
        Instr::Lt,
        push(0),
        push((back / 7) as u8),
        push(7),
        Instr::Mul,
        push((back % 7) as u8),
        Instr::Add,
    ]);
    p.extend([Instr::Sub, Instr::Jnz, Instr::Halt]);
    debug_assert_eq!(p[at], Instr::Jnz, "{at}");
    (p, head)
}

/// Random code with constant jumps, tests on copies and memory at constant addresses.
fn branching_program(next: &mut impl FnMut() -> u64) -> Vec<Instr> {
    let all: Vec<Instr> = Instr::all().collect();
    let mut p: Vec<Instr> = Vec::new();
    for _ in 0..1 + next() % 16 {
        match next() % 7 {
            0 | 1 => p.push(push((next() % 8) as u8)),
            // What relations are about: a test on a copy, then a branch.
            5 => p.extend([
                Instr::Read,
                Instr::Dup,
                push((next() % 3) as u8),
                [Instr::Add, Instr::Sub][(next() % 2) as usize],
                push((next() % 6) as u8),
                [Instr::Jz, Instr::Jnz][(next() % 2) as usize],
            ]),
            // And memory at a constant address, tested after loading.
            6 => {
                let cell = push((next() % 3) as u8);
                p.extend([
                    cell,
                    Instr::Load,
                    Instr::Dup,
                    push((next() % 4) as u8),
                    [Instr::Eq, Instr::Lt, Instr::Gt][(next() % 3) as usize],
                    push((next() % 6) as u8),
                    [Instr::Jz, Instr::Jnz][(next() % 2) as usize],
                    push(1),
                    Instr::Add,
                    cell,
                    Instr::Store,
                ]);
            }
            2 => {
                // A constant jump, forward or backward.
                let k = (next() % 6) as u8;
                if next().is_multiple_of(2) {
                    p.extend([push(k), all[(next() % all.len() as u64) as usize]]);
                } else {
                    p.extend([
                        push(0),
                        push(k),
                        Instr::Sub,
                        [Instr::Jmp, Instr::Jz, Instr::Jnz][(next() % 3) as usize],
                    ]);
                }
            }
            _ => p.push(all[(next() % all.len() as u64) as usize]),
        }
    }
    if next().is_multiple_of(2) {
        p.push(Instr::Halt);
    }
    p
}

/// Same answers as the Lean model, whose checker accepts each result.
/// A missing `emdanalyze` skips; `EMD_REQUIRE_LEAN=1` fails.
#[test]
fn the_analysis_is_the_proved_mirror() {
    let exe =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../formal/lean/.lake/build/bin/emdanalyze");
    if !exe.exists() {
        assert!(std::env::var_os("EMD_REQUIRE_LEAN").is_none(), "{} missing", exe.display());
        eprintln!("mirror test skipped: {} missing", exe.display());
        return;
    }
    let file = std::env::temp_dir().join(format!("emd-analyze-mirror-{}.emd", std::process::id()));
    let mut state = 0x2545_F491_4F6C_DD1D_u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let examples = ["hello", "functions", "add", "cat", "truth", "fizzbuzz", "brainfuck"].map(|name| {
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../examples/{name}.asm"));
        emd_asm::assemble(&std::fs::read_to_string(path).unwrap()).unwrap()
    });
    let random = (0..1600)
        .map(|i| if i % 2 == 0 { looping_program(&mut next).0 } else { branching_program(&mut next) });
    let (mut compared, mut with_issues) = (0, 0);
    for p in examples.into_iter().chain(random).filter(|p| !p.is_empty()) {
        std::fs::write(&file, emd_core::format_program(&p)).unwrap();
        let out = std::process::Command::new(&exe).arg(&file).output().unwrap();
        assert!(out.status.success(), "{p:?}");
        let text = String::from_utf8(out.stdout).unwrap();
        let mut lines = text.lines();
        assert_eq!(lines.next(), Some("certified 1"), "{p:?}");
        let a = analyze(&p);
        assert_eq!(lines.next().unwrap(), format!("halt {}", u8::from(a.halt_reachable)), "{p:?}");
        let reached: String = a
            .stacks
            .iter()
            .enumerate()
            .filter(|(_, s)| s.reached())
            .map(|(pc, _)| format!(" {pc}"))
            .collect();
        assert_eq!(lines.next().unwrap(), format!("reached{reached}"), "{p:?}");
        let lean: BTreeSet<&str> = lines.collect();
        let rust: Vec<String> =
            a.issues.iter().map(|i| format!("issue {} {:?} {}", i.pc, i.kind, u8::from(i.certain))).collect();
        assert_eq!(lean, rust.iter().map(String::as_str).collect(), "{p:?}");
        compared += 1;
        with_issues += usize::from(!rust.is_empty());
    }
    let _ = std::fs::remove_file(&file);
    eprintln!("analyzer mirror: {compared} programs, {with_issues} with issues");
    assert!(compared > 1500 && with_issues > 300, "{compared} {with_issues}");
}

#[test]
fn loops_that_revisit_copies_are_foreseen_too() {
    let mut state = 0x4CF5_AD43_2745_937F_u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let (mut looped, mut faults) = (0, 0);
    for _ in 0..6_000 {
        let (p, head) = looping_program(&mut next);
        let analysis = analyze(&p);
        for input in [&b""[..], b"\x00\x01", b"\x02"] {
            let mut vm = Vm::new(&p, Limits { max_steps: 400, ..Limits::default() });
            let mut rest = input;
            let mut turns = 0;
            while vm.status == Status::Running {
                if vm.pc == head {
                    turns += 1;
                }
                let described = &analysis.stacks[vm.pc];
                assert!(described.reached(), "pc {} reached in {p:?}: {analysis}", vm.pc);
                assert!(
                    matches(&vm.stack, &vm.memory, described),
                    "pc {} stack {:?} memory {:?} vs {described:?} in {p:?}",
                    vm.pc,
                    vm.stack,
                    vm.memory
                );
                vm.step(&mut rest, &mut std::io::sink());
            }
            looped += usize::from(turns >= 2);
            if let Status::Faulted(f) = &vm.status
                && let Some(kind) = analyzed_kind(f)
            {
                faults += 1;
                assert!(
                    analysis.issues.iter().any(|i| i.pc == vm.pc
                        && (i.kind == kind || (kind == Kind::PcOutOfRange && i.kind == Kind::UnknownJump))),
                    "{f} at pc {} not foreseen in {p:?}: {analysis}",
                    vm.pc
                );
            }
        }
    }
    assert!(looped > 1_000, "only {looped} runs looped");
    assert!(faults > 1_000, "only {faults} faults");
}

/// Runs `p` on `input` and checks the analysis at every step: each state is described, each
/// move is an edge, a fault was reported at its pc, and a halt was foreseen. True on a fault the
/// analyzer models.
fn run_is_foreseen(p: &[Instr], analysis: &Analysis, input: &[u8], max_steps: u64) -> bool {
    let mut vm = Vm::new(p, Limits { max_steps, ..Limits::default() });
    let mut rest = input;
    while vm.status == Status::Running {
        if let Some(described) = analysis.stacks.get(vm.pc) {
            assert!(described.reached(), "pc {} reached in {p:?}", vm.pc);
            assert!(
                matches(&vm.stack, &vm.memory, described),
                "pc {} stack {:?} memory {:?} vs {described:?} in {p:?}",
                vm.pc,
                vm.stack,
                vm.memory
            );
        }
        let before = vm.pc;
        vm.step(&mut rest, &mut std::io::sink());
        if vm.status == Status::Running {
            assert!(analysis.edges.contains(&(before, vm.pc)), "edge {before}->{} in {p:?}", vm.pc);
        }
    }
    match &vm.status {
        Status::Faulted(f) => analyzed_kind(f).is_some_and(|kind| {
            let seen = analysis.issues.iter().any(|i| {
                i.pc == vm.pc
                    && (i.kind == kind || (kind == Kind::PcOutOfRange && i.kind == Kind::UnknownJump))
            });
            assert!(seen, "{f} at pc {} not foreseen in {p:?}: {analysis}", vm.pc);
            true
        }),
        _ => {
            assert!(analysis.halt_reachable, "{p:?}");
            false
        }
    }
}

/// Every state a run visits is described, and every fault was reported at that pc.
#[test]
fn every_fault_is_foreseen() {
    let mut state = 0x9E37_79B9_7F4A_7C15_u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let (mut clean, mut faulted) = (0, 0);
    for _ in 0..3_000 {
        let p = branching_program(&mut next);
        let analysis = analyze(&p);
        for input in [&b""[..], b"\x00", b"\x05A"] {
            faulted += usize::from(run_is_foreseen(&p, &analysis, input, 300));
        }
        clean += usize::from(analysis.is_clean());
    }
    assert!(clean > 50, "only {clean} proved clean");
    assert!(faulted > 500, "only {faulted} faults");
}

/// The same check on every program of up to three instructions, not a sample, for end of
/// input and for three bytes.
#[test]
fn every_short_program_is_foreseen() {
    let all: Vec<Instr> = Instr::all().collect();
    let (mut programs, mut faulted) = (0, 0);
    for len in 0..=3u32 {
        for n in 0..all.len().pow(len) {
            let p: Vec<Instr> = (0..len).map(|i| all[n / all.len().pow(i) % all.len()]).collect();
            let analysis = analyze(&p);
            for input in [&b""[..], b"\x00", b"\x05A", b"\xff"] {
                faulted += usize::from(run_is_foreseen(&p, &analysis, input, 100));
            }
            programs += 1;
        }
    }
    assert_eq!(programs, 1 + 32 + 32 * 32 + 32 * 32 * 32);
    assert!(faulted > 50_000, "only {faulted} faults");
}

#[test]
fn a_known_overflow_is_reported_as_certain() {
    let p = emd_asm::assemble("PUSH 9223372036854775807 PUSH 2 MUL HALT").unwrap();
    assert!(analyze(&p).issues.iter().any(|i| i.kind == Kind::Overflow && i.certain));
}

#[test]
fn an_overflow_on_some_values_is_reported_as_possible() {
    let p = emd_asm::assemble("READ PUSH 9223372036854775807 ADD HALT").unwrap();
    assert!(analyze(&p).issues.iter().any(|i| i.kind == Kind::Overflow && !i.certain));
}

#[test]
fn not_of_a_range_without_zero_is_zero() {
    // 257 values times 1000, plus 1 to 3: too many to list, so a range, and none is 0.
    let text = "READ PUSH 2 ADD PUSH 1000 MUL READ PUSH 2 MOD PUSH 2 ADD ADD NOT HALT";
    let p = emd_asm::assemble(text).unwrap();
    let a = analyze(&p);
    let halt = p.len() - 1;
    assert!(depth(&a, halt, &[Val::one(0)]), "{a}");
}

#[test]
fn a_range_loses_only_the_ends_it_cannot_be() {
    let range = Val::range(1, 1000);
    assert_eq!(range.restrict(Cmp::Ne, 1000), Some(Val::range(1, 999)));
    assert_eq!(range.restrict(Cmp::Ne, 1), Some(Val::range(2, 1000)));
    assert_eq!(range.restrict(Cmp::Ne, 500), Some(range));
}

#[test]
fn a_branch_too_extreme_to_narrow_keeps_both_ways() {
    // Comparing x + 5 with a constant so low that the constant minus 5 does not fit.
    let test = "READ PUSH 5 ADD PUSH -9223372036854775807 LT JZ out PUSH 1 HALT out: PUSH 2 HALT";
    assert!(analyze(&emd_asm::assemble(test).unwrap()).stacks.iter().any(|s| s.reached()));
    // An offset that cannot be negated: x + i64::MIN, built in two steps.
    let offset = "PUSH -9223372036854775807 PUSH 1 SUB READ ADD JZ out PUSH 1 HALT out: PUSH 2 HALT";
    let p = emd_asm::assemble(offset).unwrap();
    let first_halt = p.iter().position(|i| *i == Instr::Halt).unwrap();
    let a = analyze(&p);
    assert!(a.stacks[first_halt].reached(), "{a}");
}

#[test]
fn a_comparison_past_the_integers_holds_for_no_value() {
    let range = Val::range(0, 1000);
    assert_eq!(range.restrict(Cmp::Lt, i64::MIN), None);
    assert_eq!(range.restrict(Cmp::Gt, i64::MAX), None);
}

#[test]
fn an_offset_that_overflows_is_forgotten_not_wrapped() {
    for text in [
        "READ PUSH 9223372036854775807 ADD PUSH 1 ADD HALT",
        "READ PUSH 9223372036854775807 ADD PUSH 1 SWAP ADD HALT",
        "READ PUSH -9223372036854775807 ADD PUSH 2 SUB HALT",
    ] {
        let p = emd_asm::assemble(text).unwrap();
        assert!(kinds(&p).contains(&Kind::Overflow), "{text}");
    }
}

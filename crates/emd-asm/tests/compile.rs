// emd: an esoteric language written only in Unicode dashes.
// The compiler is checked by running what it emits on the VM.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_asm::{assemble, push_int};
use emd_core::{Instr, encode_program};
use emd_vm::{Limits, Status, Vm};

fn exec(text: &str, input: &[u8]) -> (Status, Vec<i64>, Vec<u8>) {
    let program = assemble(text).unwrap_or_else(|e| panic!("{e}"));
    let mut vm = Vm::new(&program, Limits { max_steps: 10_000_000, ..Limits::default() });
    let mut out = Vec::new();
    let status = vm.run(&mut &input[..], &mut out).clone();
    (status, vm.stack, out)
}

fn top(program: Vec<Instr>) -> i64 {
    let mut program = program;
    program.push(Instr::Halt);
    let mut vm = Vm::new(&program, Limits { max_steps: 10_000_000, ..Limits::default() });
    vm.run(&mut &b""[..], &mut Vec::new());
    assert_eq!(vm.status, Status::Halted);
    assert_eq!(vm.stack.len(), 1);
    vm.stack[0]
}

#[test]
fn push_int_builds_every_value() {
    for n in -200_000..200_000 {
        assert_eq!(top(push_int(n)), n);
    }
    for n in [i64::MAX, -i64::MAX, 1 << 40, -(1 << 40), 7, 8, 49, 343, 344] {
        assert_eq!(top(push_int(n)), n);
    }
    let mut s = 0x9E37_79B9_7F4A_7C15_u64;
    for _ in 0..2000 {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        let n = (s >> 1) as i64 >> (s % 62);
        assert_eq!(top(push_int(n)), n);
        assert_eq!(top(push_int(-n)), -n);
    }
}

#[test]
fn flat_programs_match_mnemonics() {
    let p = assemble("PUSH 1 PUSH 2\nADD HALT ; comment\n").unwrap();
    assert_eq!(encode_program(&p), "-\u{2010}-\u{2011}\u{2011}-\u{2013}\u{2012}");
}

#[test]
fn disassembly_reassembles() {
    let all: Vec<Instr> = Instr::all().collect();
    let text: String = all.iter().map(|i| format!("{i}\n")).collect();
    assert_eq!(assemble(&text).unwrap(), all);
}

#[test]
fn labels_forward_backward_and_raw_jumps() {
    let (s, stack, _) = exec("JMP end\nPUSH 7\nend: HALT", b"");
    assert_eq!((s, stack), (Status::Halted, vec![]));
    let (s, _, out) = exec(
        "CONST N 0\nPUSH 3 STORE N\nloop:\nLOAD N PUSH '0' ADD WRITE\nLOAD N PUSH 1 SUB DUP STORE N\nJNZ loop\nHALT",
        b"",
    );
    assert_eq!(s, Status::Halted);
    assert_eq!(out, b"321");
    assert_eq!(exec("PUSH 2 JMP PUSH 7 HALT", b"").1, Vec::<i64>::new());
    assert_eq!(exec("self: PUSH 0 JZ end HALT end: PUSH 5 HALT", b"").1, [5]);
}

#[test]
fn strings_keep_bytes_and_semicolons() {
    let (_, _, out) = exec("PRINT \"a;b\\n\\\"é\" HALT", b"");
    assert_eq!(out, "a;b\n\"é".as_bytes());
}

/// Every distance in a range, forward and backward, including padding.
#[test]
fn layout_converges_for_any_distance() {
    for gap in 0..400 {
        let filler = "PUSH 0 ".repeat(gap);
        let forward = format!("PUSH 1 JNZ end {filler} PUSH 7 end: HALT");
        assert_eq!(exec(&forward, b"").0, Status::Halted);
        assert_eq!(exec(&forward, b"").1, Vec::<i64>::new());

        let backward = format!("JMP start\nback: {filler} PUSH 1 HALT\nstart: PUSH 1 JNZ back\nPUSH 7 HALT");
        let (status, stack, _) = exec(&backward, b"");
        assert_eq!(status, Status::Halted);
        assert_eq!((stack.len(), stack.last()), (gap + 1, Some(&1)));
    }
    // Several interdependent jumps.
    let mut text = String::new();
    for i in 0..300 {
        text += &format!("JMP l{}\nl{i}:\n", (i + 150) % 300);
        text += "PUSH 0 DROP\n";
    }
    text += "HALT";
    assemble(&text).unwrap();
}

#[test]
fn errors_point_at_the_token() {
    let span = |t: &str| {
        let s = assemble(t).unwrap_err().span;
        (s.line, s.column, s.length)
    };
    assert_eq!(span("ADD\n  NOPE x"), (2, 3, 4));
    assert_eq!(span("JMP nowhere"), (1, 5, 7));
    assert_eq!(span("PUSH 1 PUSH zz"), (1, 13, 2));
    assert_eq!(span("PUSH"), (1, 1, 4));
    assert_eq!(span("a: HALT\n  a:"), (2, 3, 2));
    assert_eq!(span("PUSH 99999999999999999999"), (1, 6, 20));
    assert_eq!(span("HALT @"), (1, 6, 1));
    assert_eq!(span("PRINT \"abc"), (1, 7, 4));
    assert_eq!(span("PUSH 'ab'"), (1, 6, 3));
}

#[test]
fn a_rendered_error_shows_the_line_and_underlines_the_token() {
    let source = "HALT\n\tJNZ nowhere ; comment\n";
    let error = assemble(source).unwrap_err();
    assert_eq!(
        error.render("x.asm", source),
        "error: undefined label `nowhere`\n --> x.asm:2:6\n  |\n2 | \tJNZ nowhere ; comment\n  | \t    ^^^^^^^\n"
    );
}

#[test]
fn a_rendered_error_does_not_pass_control_characters_to_the_terminal() {
    let source = "PUSH \u{1b}[31m";
    let error = assemble(source).unwrap_err();
    assert!(!error.message.contains('\u{1b}'), "{error}");
    assert!(!error.render("x.asm", source).contains('\u{1b}'), "{error}");
}

#[test]
fn errors_name_the_line() {
    let line = |t: &str| assemble(t).unwrap_err();
    assert_eq!(line("ADD\nNOPE").span.line, 2);
    assert!(line("ADD\nNOPE").message.contains("NOPE"));
    assert!(line("JMP nowhere").message.contains("nowhere"));
    assert!(line("a: a: HALT").message.contains("twice"));
    assert!(line("CONST A 1\nCONST A 2").message.contains("twice"));
    assert!(line("PUSH").message.contains("value"));
    assert!(line("PUSH\n1").message.contains("value"));
    assert!(line("PUSH B").message.contains("undefined"));
    assert!(line("PUSH 9223372036854775808").message.contains("fit"));
    assert!(line("PRINT \"x").message.contains("unterminated"));
    assert!(line("PUSH 'ab'").message.contains("one character"));
    assert!(line("@").message.contains("unexpected"));
    assert!(line("halt: HALT").message.contains("not a usable name"));
    assert!(line("Add: HALT").message.contains("not a usable name"));
    assert!(line("CONST swap 1").message.contains("not a usable name"));
    assert!(line("1").message.contains("instruction"));
}

/// Every example compiles to exactly its committed `.emd`.
#[test]
fn committed_examples_are_up_to_date() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut n = 0;
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "asm") {
            let text = std::fs::read_to_string(&path).unwrap();
            let program = assemble(&text).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
            let committed = std::fs::read_to_string(path.with_extension("emd")).unwrap();
            assert_eq!(emd_core::format_program(&program), committed, "{}: re-run emd asm", path.display());
            n += 1;
        }
    }
    assert!(n >= 5);
}

/// Subroutines through CALL and RET, with an argument moved by ROT and SWAP.
#[test]
fn call_and_ret_make_subroutines() {
    let program = assemble(
        "PUSH 65 CALL show\n\
         PUSH 66 CALL show\n\
         HALT\n\
         show:\n\
         SWAP WRITE RET\n",
    )
    .unwrap();
    let mut vm = Vm::new(&program, Limits { max_steps: 1000, ..Limits::default() });
    let mut output = Vec::new();
    vm.run(&mut &b""[..], &mut output);
    assert_eq!(vm.status, Status::Halted);
    assert_eq!(output, b"AB");
    assert!(vm.stack.is_empty());

    // ROT reaches under an argument pair.
    let sub = assemble("PUSH 5 PUSH 3 CALL minus WRITE HALT\nminus:\nROT ROT SUB SWAP RET\n");
    let program = sub.unwrap();
    let mut vm = Vm::new(&program, Limits { max_steps: 1000, ..Limits::default() });
    let mut output = Vec::new();
    vm.run(&mut &b""[..], &mut output);
    assert_eq!(vm.status, Status::Halted);
    assert_eq!(output, [2]);
}

#[test]
fn every_escape_is_the_character_it_names() {
    for (escape, code) in
        [("\\n", 10), ("\\t", 9), ("\\r", 13), ("\\0", 0), ("\\\\", 92), ("\\\"", 34), ("\\'", 39)]
    {
        assert_eq!(
            assemble(&format!("PUSH '{escape}' HALT")),
            assemble(&format!("PUSH {code} HALT")),
            "{escape}"
        );
    }
}

#[test]
fn an_error_prints_where_it_is() {
    let error = assemble("  JNZ nope").unwrap_err();
    assert_eq!(error.to_string(), "line 1, column 7: undefined label `nope`");
}

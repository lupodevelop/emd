// emd: an esoteric language written only in Unicode dashes.
// Compiled code must behave like a direct interpretation of the statements.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::parser::{self, Statement};
use crate::{Located, codegen, lexer};
use emd_core::Instr;
use emd_vm::{Fault, Limits, Status, Vm};
use std::collections::{BTreeMap, HashMap};

const SOURCE_STEPS: usize = 20_000;
const RETURN_BASE: i64 = 1 << 40;

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Halted {
        stack: Vec<i64>,
        output: Vec<u8>,
    },
    /// The stack is not compared: a fault may land inside an expanded statement.
    Faulted {
        kind: &'static str,
        output: Vec<u8>,
    },
}

/// Faults by kind: payloads such as the pc differ between source and compiled code.
fn kind(fault: &Fault) -> &'static str {
    match fault {
        Fault::StackUnderflow => "underflow",
        Fault::DivisionByZero => "div0",
        Fault::NegativeAddress(_) => "address",
        Fault::PcOutOfRange(_) => "pc",
        Fault::InvalidByte(_) => "byte",
        Fault::Overflow => "overflow",
        Fault::StepLimit | Fault::StackLimit | Fault::MemoryLimit | Fault::Io(_) => "limit",
    }
}

fn binary(op: Instr, a: i64, b: i64) -> Result<i64, &'static str> {
    Ok(match op {
        Instr::Add => a.checked_add(b).ok_or("overflow")?,
        Instr::Sub => a.checked_sub(b).ok_or("overflow")?,
        Instr::Mul => a.checked_mul(b).ok_or("overflow")?,
        Instr::Div | Instr::Mod if b == 0 => return Err("div0"),
        Instr::Div => a.checked_div(b).ok_or("overflow")?,
        Instr::Mod => a.checked_rem(b).ok_or("overflow")?,
        Instr::Eq => i64::from(a == b),
        Instr::Lt => i64::from(a < b),
        Instr::Gt => i64::from(a > b),
        _ => unreachable!(),
    })
}

/// `None`: ran out of steps, so nothing can be concluded.
fn interpret(lines: &[Located<Statement>], input: &[u8]) -> Option<Outcome> {
    let code: Vec<&Statement> =
        lines.iter().map(|l| &l.value).filter(|s| !matches!(s, Statement::Label(_))).collect();
    let mut labels = HashMap::new();
    let mut index = 0;
    for line in lines {
        match &line.value {
            Statement::Label(name) => {
                labels.insert(*name, index);
            }
            _ => index += 1,
        }
    }

    let (mut pc, mut stack, mut output) = (0usize, Vec::<i64>::new(), Vec::new());
    let mut memory: BTreeMap<i64, i64> = BTreeMap::new();
    let mut input = input.iter();
    for _ in 0..SOURCE_STEPS {
        let fault = |kind, output: &Vec<u8>| Some(Outcome::Faulted { kind, output: output.clone() });
        let Some(&statement) = code.get(pc) else { return fault("pc", &output) };
        let depth = stack.len();
        // Checks happen before effects, so that a fault leaves output untouched.
        macro_rules! need {
            ($n:expr) => {
                if depth < $n {
                    return fault("underflow", &output);
                }
            };
        }
        macro_rules! fall_through {
            () => {
                if pc + 1 >= code.len() {
                    return fault("pc", &output);
                }
            };
        }
        match statement {
            Statement::Label(_) => unreachable!(),
            Statement::Push(v) => {
                fall_through!();
                stack.push(*v);
                pc += 1;
            }
            Statement::Jump(instr, name) => {
                let taken = match instr {
                    Instr::Jmp | Instr::Call => true,
                    Instr::Jz | Instr::Jnz => {
                        need!(1);
                        let c = stack[depth - 1];
                        if *instr == Instr::Jz { c == 0 } else { c != 0 }
                    }
                    _ => unreachable!(),
                };
                let target = if taken { labels[*name] } else { pc + 1 };
                if target >= code.len() {
                    return fault("pc", &output);
                }
                match instr {
                    Instr::Jmp => {}
                    // A return address here is a statement index, in a range programs do not reach.
                    Instr::Call => stack.push(RETURN_BASE + pc as i64 + 1),
                    _ => {
                        stack.pop();
                    }
                }
                pc = target;
            }
            Statement::Instr(instr) => {
                match instr {
                    Instr::Push(n) => {
                        fall_through!();
                        stack.push(i64::from(n.index()));
                    }
                    Instr::Dup => {
                        need!(1);
                        fall_through!();
                        stack.push(stack[depth - 1]);
                    }
                    Instr::Drop => {
                        need!(1);
                        fall_through!();
                        stack.pop();
                    }
                    Instr::Swap => {
                        need!(2);
                        fall_through!();
                        stack.swap(depth - 1, depth - 2);
                    }
                    Instr::Over => {
                        need!(2);
                        fall_through!();
                        stack.push(stack[depth - 2]);
                    }
                    Instr::Rot => {
                        need!(3);
                        fall_through!();
                        stack[depth - 3..].rotate_left(1);
                    }
                    Instr::Add
                    | Instr::Sub
                    | Instr::Mul
                    | Instr::Div
                    | Instr::Mod
                    | Instr::Eq
                    | Instr::Lt
                    | Instr::Gt => {
                        need!(2);
                        let r = match binary(*instr, stack[depth - 2], stack[depth - 1]) {
                            Ok(r) => r,
                            Err(kind) => return fault(kind, &output),
                        };
                        fall_through!();
                        stack.truncate(depth - 2);
                        stack.push(r);
                    }
                    Instr::Not => {
                        need!(1);
                        fall_through!();
                        stack[depth - 1] = i64::from(stack[depth - 1] == 0);
                    }
                    Instr::Load => {
                        need!(1);
                        let a = stack[depth - 1];
                        if a < 0 {
                            return fault("address", &output);
                        }
                        fall_through!();
                        stack[depth - 1] = memory.get(&a).copied().unwrap_or(0);
                    }
                    Instr::Store => {
                        need!(2);
                        let a = stack[depth - 1];
                        if a < 0 {
                            return fault("address", &output);
                        }
                        fall_through!();
                        memory.insert(a, stack[depth - 2]);
                        stack.truncate(depth - 2);
                    }
                    Instr::Read => {
                        fall_through!();
                        stack.push(input.next().map_or(-1, |&b| i64::from(b)));
                    }
                    Instr::Write => {
                        need!(1);
                        let Ok(byte) = u8::try_from(stack[depth - 1]) else {
                            return fault("byte", &output);
                        };
                        fall_through!();
                        output.push(byte);
                        stack.pop();
                    }
                    Instr::Halt => return Some(Outcome::Halted { stack, output }),
                    Instr::Ret => {
                        need!(1);
                        let target = stack[depth - 1] - RETURN_BASE;
                        if target < 0 || target >= code.len() as i64 {
                            return fault("pc", &output);
                        }
                        stack.pop();
                        pc = target as usize;
                        continue;
                    }
                    Instr::Jmp | Instr::Jz | Instr::Jnz | Instr::Call => {
                        unreachable!("not generated: offsets on the stack have no source-level meaning")
                    }
                }
                pc += 1;
            }
        }
    }
    None
}

fn execute(program: &[Instr], input: &[u8]) -> Outcome {
    let limits = Limits { max_steps: 2_000_000, ..Limits::default() };
    let mut vm = Vm::new(program, limits);
    let mut output = Vec::new();
    vm.run(&mut &input[..], &mut output);
    match &vm.status {
        Status::Halted => Outcome::Halted { stack: vm.stack, output },
        Status::Faulted(f) => Outcome::Faulted { kind: kind(f), output },
        Status::Running => unreachable!(),
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// Random text with labels. Long filler crosses the sizes where layout changes.
fn random_program(rng: &mut Rng) -> String {
    const PLAIN: [&str; 17] = [
        "ROT", "DUP", "DROP", "SWAP", "OVER", "ADD", "SUB", "MUL", "DIV", "MOD", "EQ", "LT", "GT", "NOT",
        "READ", "WRITE", "LOAD",
    ];
    let labels = 1 + rng.below(5);
    let statements = 1 + rng.below(40);
    let mut text = String::new();
    let mut placed = vec![false; labels as usize];
    for _ in 0..statements {
        if rng.below(5) == 0 {
            let l = rng.below(labels) as usize;
            if !placed[l] {
                placed[l] = true;
                text += &format!("l{l}:\n");
            }
        }
        let line = match rng.below(12) {
            0..=4 => {
                let magnitude = 1i64 << rng.below(20);
                let value = (rng.below(2 * magnitude as u64) as i64) - magnitude;
                format!("PUSH {value}")
            }
            5 => format!("{} l{}", ["JMP", "JZ", "JNZ"][rng.below(3) as usize], rng.below(labels)),
            6 => format!("JNZ l{}", rng.below(labels)),
            7 => format!("STORE {}", rng.below(4)),
            8 => format!("LOAD {}", rng.below(4)),
            9 => "PRINT \"ab\"".to_string(),
            10 => "PUSH 0 ".repeat(rng.below(120) as usize) + "HALT",
            _ => PLAIN[rng.below(17) as usize].to_string(),
        };
        text += &line;
        text.push('\n');
    }
    for (l, done) in placed.iter().enumerate() {
        if !done {
            text += &format!("l{l}:\n");
        }
    }
    // Sometimes no final HALT, so that falling off the end is compared too.
    if rng.below(4) == 0 { text } else { text + "HALT\n" }
}

/// Routines call only later routines, so every run ends. Filler crosses layout sizes.
fn random_routines(rng: &mut Rng) -> String {
    let routines = 1 + rng.below(5);
    let mut text = String::new();
    for _ in 0..1 + rng.below(8) {
        let keep = rng.below(4) == 0;
        if keep {
            text += &format!("PUSH {}\n", rng.below(100));
        }
        text += &format!("PUSH {} CALL r{}\n", rng.below(300), rng.below(routines));
        if keep {
            text += "DROP\n";
        }
        text += &"PUSH 0 DROP ".repeat(rng.below(150) as usize);
        text.push('\n');
    }
    text += "HALT\n";
    for r in 0..routines {
        // On entry: the argument, then the return address on top.
        text += &format!("r{r}:\nSWAP\n");
        match rng.below(4) {
            0 => text += "PUSH 256 MOD WRITE\n",
            1 => text += &format!("PUSH {} ADD PUSH 256 MOD WRITE\n", rng.below(50)),
            2 => text += &format!("PUSH {} SUB WRITE\n", rng.below(400)),
            // Three ROTs are the identity, if each one really rotates.
            _ => text += &format!("PUSH {} ROT ROT ROT ADD PUSH 256 MOD WRITE\n", rng.below(9)),
        }
        text += &"PUSH 0 DROP ".repeat(rng.below(60) as usize);
        if r + 1 < routines && rng.below(2) == 0 {
            let callee = r + 1 + rng.below(routines - r - 1);
            text += &format!("\nPUSH {} CALL r{callee}\n", rng.below(200));
        }
        text += "\nRET\n";
    }
    text
}

/// Same bytes as the Lean model of `generate`.
/// A missing `emdlower` skips; `EMD_REQUIRE_LEAN=1` fails.
#[test]
fn generate_is_the_proved_mirror() {
    use std::io::Write;
    use std::process::{Command, Stdio};
    let exe =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../formal/lean/.lake/build/bin/emdlower");
    if !exe.exists() {
        assert!(std::env::var_os("EMD_REQUIRE_LEAN").is_none(), "{} missing", exe.display());
        eprintln!("mirror test skipped: {} missing", exe.display());
        return;
    }
    let mut rng = Rng(0x0DDB_A11C_AFE5_7EA1);
    let mut texts: Vec<String> = ["hello", "functions", "add", "cat", "truth", "fizzbuzz", "brainfuck"]
        .iter()
        .map(|name| {
            std::fs::read_to_string(format!("{}/../../examples/{name}.asm", env!("CARGO_MANIFEST_DIR")))
                .unwrap()
        })
        .collect();
    for _ in 0..600 {
        texts.push(random_program(&mut rng));
        texts.push(random_routines(&mut rng));
    }
    let mut jumps = 0;
    for text in &texts {
        let lines = parser::parse(&lexer::lex(text).unwrap()).unwrap();
        let mut statements = String::new();
        for line in &lines {
            let row = match &line.value {
                Statement::Label(name) => format!("label {name}"),
                Statement::Instr(i) => format!("instr {i}"),
                Statement::Push(v) => format!("push {v}"),
                Statement::Jump(i, name) => {
                    jumps += 1;
                    format!("jump {i} {name}")
                }
            };
            statements += &row;
            statements.push('\n');
        }
        let mut child = Command::new(&exe).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        child.stdin.take().unwrap().write_all(statements.as_bytes()).unwrap();
        let out = child.wait_with_output().unwrap();
        assert!(out.status.success(), "{text}");
        let program = codegen::generate(&lines).unwrap_or_else(|e| panic!("{e}\n{text}"));
        assert_eq!(String::from_utf8(out.stdout).unwrap(), emd_core::encode_program(&program), "\n{text}");
    }
    eprintln!("compiler mirror: {} programs, {jumps} label jumps", texts.len());
    assert!(jumps > 5000, "{jumps}");
}

#[test]
fn subroutines_behave_like_the_source() {
    let mut rng = Rng(0x0F1E_2D3C_4B5A_6978);
    let (mut halted, mut faulted, mut calls) = (0, 0, 0);
    for _ in 0..1500 {
        let text = random_routines(&mut rng);
        let tokens = lexer::lex(&text).unwrap();
        let lines = parser::parse(&tokens).unwrap_or_else(|e| panic!("{e}\n{text}"));
        let program = codegen::generate(&lines).unwrap_or_else(|e| panic!("{e}\n{text}"));
        calls += program.iter().filter(|i| **i == Instr::Call).count();
        let expected = interpret(&lines, &[]).unwrap_or_else(|| panic!("no answer\n{text}"));
        assert_eq!(execute(&program, &[]), expected, "\n{text}");
        match expected {
            Outcome::Halted { .. } => halted += 1,
            Outcome::Faulted { .. } => faulted += 1,
        }
    }
    eprintln!("subroutines: {halted} halted, {faulted} faulted, {calls} calls");
    assert!(halted >= 200 && faulted >= 50 && calls >= 3000, "{halted} {faulted} {calls}");
}

#[test]
fn compiled_code_behaves_like_the_source() {
    let mut rng = Rng(0x1234_5678_9ABC_DEF1);
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    let mut undecided = 0;
    for _ in 0..4000 {
        let text = random_program(&mut rng);
        let tokens = lexer::lex(&text).unwrap();
        let lines = parser::parse(&tokens).unwrap_or_else(|e| panic!("{e}\n{text}"));
        let program = codegen::generate(&lines).unwrap_or_else(|e| panic!("{e}\n{text}"));
        let input = [7u8, 200];
        let Some(expected) = interpret(&lines, &input) else {
            undecided += 1;
            continue;
        };
        assert_eq!(execute(&program, &input), expected, "\n{text}");
        let kind = match expected {
            Outcome::Halted { .. } => "halted".to_string(),
            Outcome::Faulted { kind, .. } => kind.to_string(),
        };
        *kinds.entry(kind).or_default() += 1;
    }
    eprintln!("oracle: {kinds:?}, {undecided} undecided");
    for kind in ["halted", "underflow", "pc", "div0", "address", "byte"] {
        assert!(kinds.get(kind).is_some_and(|&n| n >= 5), "too few `{kind}`: {kinds:?}");
    }
}

/// No input can make the compiler panic.
#[test]
fn any_text_compiles_or_reports_an_error() {
    const POOL: [&str; 24] = [
        "PUSH ",
        "JMP ",
        "JNZ ",
        "LOAD ",
        "STORE ",
        "CONST ",
        "PRINT ",
        "HALT ",
        "a",
        "a: ",
        "b:",
        "1",
        "-",
        "9223372036854775807",
        "99999999999999999999999999999999999999999",
        "\"",
        "'",
        "\\",
        "\n",
        " ",
        ";",
        "é",
        "\u{2014}",
        "\u{0}",
    ];
    let mut rng = Rng(0xABCD_EF01_2345_6789);
    let (mut ok, mut rejected) = (0, 0);
    for _ in 0..20_000 {
        let text: String = (0..rng.below(14)).map(|_| POOL[rng.below(24) as usize]).collect();
        match crate::assemble(&text) {
            Ok(_) => ok += 1,
            Err(_) => rejected += 1,
        }
    }
    assert!(ok > 100 && rejected > 100, "ok={ok} rejected={rejected}");
}

/// The compiler written in emd, run on the VM, against this one: the same bytes for every
/// text this one compiles, and an error on the same line for every text it rejects.
#[test]
fn the_compiler_in_emd_agrees_with_this_one() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let source = std::fs::read_to_string(root.join("compiler/asm.asm")).unwrap();
    let compiler = crate::assemble(&source).unwrap();
    let shipped = std::fs::read_to_string(root.join("compiler/asm.emd")).unwrap();
    assert_eq!(shipped, emd_core::format_program(&compiler), "compiler/asm.emd is out of date");

    let run = |text: &str| {
        let mut vm = Vm::new(&compiler, Limits { max_steps: 2_000_000_000, ..Limits::default() });
        let mut output = Vec::new();
        vm.run(&mut text.as_bytes(), &mut output);
        (vm.status.clone(), String::from_utf8(output).unwrap())
    };
    let check = |text: &str| match crate::assemble(text) {
        Ok(program) => {
            assert_eq!(run(text), (Status::Halted, emd_core::format_program(&program)), "\n{text}");
            true
        }
        Err(e) => {
            let (status, output) = run(text);
            assert_eq!(status, Status::Faulted(Fault::DivisionByZero), "\n{text}");
            assert_eq!(output, format!("error at line {}\n", e.span.line), "{e}\n{text}");
            false
        }
    };

    for name in ["hello", "functions", "add", "cat", "truth", "fizzbuzz", "brainfuck"] {
        assert!(check(&std::fs::read_to_string(root.join(format!("examples/{name}.asm"))).unwrap()));
    }
    let mut rng = Rng(0x5E1F_C0DE_0BAD_F00D);
    const POOL: [&str; 37] = [
        "PUSH ",
        "JMP ",
        "JNZ ",
        "CALL ",
        "LOAD ",
        "STORE ",
        "CONST ",
        "PRINT ",
        "HALT ",
        "push ",
        "a",
        "B_1",
        "a: ",
        "b:",
        "1",
        "-",
        "9223372036854775807",
        "9223372036854775808",
        "\"x\\n\"",
        "'",
        "'\\t'",
        "\\",
        "\n",
        "\r\n",
        "\r",
        " ",
        "\t",
        "\u{a0}",
        ";",
        "é",
        "\u{2014}",
        "\u{0}",
        // The ends of what Rust reads as an i128.
        "170141183460469231731687303715884105727",
        "170141183460469231731687303715884105728",
        "-170141183460469231731687303715884105728",
        "-170141183460469231731687303715884105729",
        "0001701411834604692317316873037158841057270",
    ];
    let (mut ok, mut rejected) = (0, 0);
    for _ in 0..10_000 {
        let text: String = (0..rng.below(14)).map(|_| POOL[rng.below(37) as usize]).collect();
        if check(&text) { ok += 1 } else { rejected += 1 }
    }
    assert!(ok > 100 && rejected > 100, "ok={ok} rejected={rejected}");
    for _ in 0..200 {
        assert!(check(&random_program(&mut rng)));
        assert!(check(&random_routines(&mut rng)));
    }
    // It compiles itself to itself, which compiler/asm.emd already is.
    assert!(check(&source));
}

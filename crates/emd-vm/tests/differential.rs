// emd: an esoteric language written only in Unicode dashes.
// The VM against the interpreters extracted from Lean and Rocq.
// A missing one skips; `EMD_REQUIRE_LEAN=1` and `EMD_REQUIRE_ROCQ=1` fail.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::{Instr, LINE_MAX, encode_program, format_program};
use emd_vm::{Fault, Limits, Status, Vm};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Low: the models keep memory as a chain of closures, so a long run slows each LOAD.
const FUEL: u64 = 5_000;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn interpreter(relative: &str, require: &str, build: &str) -> Option<PathBuf> {
    let path = repo().join(relative);
    if path.exists() {
        return Some(path);
    }
    let msg = format!("{} missing: {build}", path.display());
    assert!(std::env::var_os(require).is_none(), "{msg}");
    eprintln!("differential test skipped: {msg}");
    None
}

/// The Rust outcome in the interpreters' format; `None` if outside the models.
fn rust_outcome(program: &[Instr], input: &[u8]) -> Option<String> {
    let limits = Limits { max_steps: FUEL, ..Limits::default() };
    let mut vm = Vm::new(program, limits);
    let mut out = Vec::new();
    vm.run(&mut &input[..], &mut out);
    let name = match &vm.status {
        Status::Halted => return Some(format!("halt\n{}", state(&vm, &out))),
        Status::Faulted(Fault::StepLimit) => return Some(format!("running\n{}", state(&vm, &out))),
        Status::Faulted(Fault::StackUnderflow) => "stackUnderflow",
        Status::Faulted(Fault::DivisionByZero) => "divisionByZero",
        Status::Faulted(Fault::NegativeAddress(_)) => "negativeAddress",
        Status::Faulted(Fault::PcOutOfRange(_)) => "pcOutOfRange",
        Status::Faulted(Fault::InvalidByte(_)) => "invalidByte",
        Status::Faulted(Fault::Overflow | Fault::StackLimit | Fault::MemoryLimit | Fault::Io(_)) => {
            return None;
        }
        Status::Running => unreachable!(),
    };
    Some(format!("fault Emd.Fault.{name}\n"))
}

/// The models list the stack from the top down.
fn state(vm: &Vm<'_>, out: &[u8]) -> String {
    let top_down: Vec<i64> = vm.stack.iter().rev().copied().collect();
    format!("stack {top_down:?}\noutput {out:?}\n")
}

struct Case {
    name: String,
    program: Vec<Instr>,
    input: Vec<u8>,
}

fn conformance_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for entry in fs::read_dir(repo().join("tests/conformance")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "out") {
            continue;
        }
        let stem = path.file_stem().unwrap();
        let source = repo().join("examples").join(stem).with_extension("emd");
        cases.push(Case {
            name: source.display().to_string(),
            program: emd_parser::parse_bytes(&fs::read(&source).unwrap()).unwrap(),
            input: fs::read(path.with_extension("in")).unwrap_or_default(),
        });
    }
    cases
}

/// Half pushes: uniform random instructions die on the first underflow.
fn random_cases(n: usize) -> Vec<Case> {
    let all: Vec<Instr> = Instr::all().collect();
    let pushes: Vec<Instr> = all.iter().copied().filter(|i| matches!(i, Instr::Push(_))).collect();
    let mut state = 0x9E37_79B9_7F4A_7C15_u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    (0..n)
        .map(|k| {
            let mut program: Vec<Instr> = Vec::new();
            for _ in 0..next() % 6 {
                program.push(pushes[(next() % 8) as usize]);
            }
            for _ in 0..1 + next() % 24 {
                let r = next();
                program.push(if r.is_multiple_of(2) {
                    pushes[(r / 2 % 8) as usize]
                } else {
                    all[(r / 2 % all.len() as u64) as usize]
                });
            }
            if !next().is_multiple_of(4) {
                program.push(Instr::Halt);
            }
            let input = (0..next() % 4).map(|_| (next() % 256) as u8).collect();
            Case { name: format!("random #{k}"), program, input }
        })
        .collect()
}

/// Every instruction on boundary operands: pins operand order, rounding and fault priority.
fn directed_cases() -> Vec<Case> {
    const VALUES: [i64; 7] = [-9, -1, 0, 1, 3, 255, 256];
    let mut stacks: Vec<Vec<i64>> = vec![vec![]];
    stacks.extend(VALUES.map(|v| vec![v]));
    for a in VALUES {
        stacks.extend(VALUES.map(|b| vec![a, b]));
    }
    let mut cases = Vec::new();
    for instr in Instr::all().filter(|i| !matches!(i, Instr::Push(_))) {
        for stack in &stacks {
            let mut program: Vec<Instr> = stack.iter().flat_map(|&v| emd_asm::push_int(v)).collect();
            program.push(instr);
            // Room for short forward jumps to land on something other than a fault.
            program.extend(emd_asm::push_int(1));
            program.extend([Instr::Load, Instr::Halt, Instr::Halt, Instr::Halt, Instr::Halt]);
            cases.push(Case { name: format!("{instr} on {stack:?}"), program, input: vec![65] });
        }
    }
    cases
}

/// Every program of at most 3 instructions. Those that read also run at end of input.
fn exhaustive_cases() -> Vec<Case> {
    let all: Vec<Instr> = Instr::all().collect();
    let mut programs: Vec<Vec<Instr>> = vec![vec![]];
    let mut last = programs.clone();
    for _ in 0..3 {
        last = last.iter().flat_map(|p| all.iter().map(|i| [p.as_slice(), &[*i]].concat())).collect();
        programs.extend(last.iter().cloned());
    }
    let n = all.len();
    assert_eq!(programs.len(), 1 + n + n * n + n * n * n);
    let mut cases = Vec::new();
    for program in programs {
        if program.contains(&Instr::Read) {
            cases.push(Case { name: "exhaustive, no input".into(), program: program.clone(), input: vec![] });
        }
        cases.push(Case { name: "exhaustive".into(), program, input: vec![65] });
    }
    cases
}

/// Conformance, random and directed cases.
fn sampled_cases() -> Vec<Case> {
    let mut cases = conformance_cases();
    assert!(cases.len() >= 5);
    cases.extend(random_cases(1000));
    cases.extend(directed_cases());
    cases
}

fn compare_with(exe: &Path, tag: &str, cases: &[Case]) {
    let tmp = std::env::temp_dir().join(format!("emd-differential-{tag}-{}", std::process::id()));
    fs::create_dir_all(&tmp).unwrap();
    let program_file = tmp.join("p.emd");
    let input_file = tmp.join("p.in");

    let mut skipped = 0;
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    for case in cases {
        let Some(expected) = rust_outcome(&case.program, &case.input) else {
            skipped += 1;
            continue;
        };
        fs::write(&program_file, format_program(&case.program)).unwrap();
        fs::write(&input_file, &case.input).unwrap();
        let out =
            Command::new(exe).arg(&program_file).arg(&input_file).arg(FUEL.to_string()).output().unwrap();
        let actual = String::from_utf8_lossy(&out.stdout);
        let listing = case.program.iter().map(ToString::to_string).collect::<Vec<_>>().join(" ");
        assert!(
            out.status.success(),
            "{tag} failed on {}: {}\n{listing}",
            case.name,
            String::from_utf8_lossy(&out.stderr)
        );
        assert_eq!(actual, expected, "{tag} disagrees on {}: {listing}", case.name);
        *kinds.entry(expected.lines().next().unwrap().to_string()).or_default() += 1;
    }
    fs::remove_dir_all(&tmp).unwrap();
    eprintln!("{tag}: {} compared, {skipped} outside the model: {kinds:?}", cases.len() - skipped);

    for kind in [
        "halt",
        "fault Emd.Fault.stackUnderflow",
        "fault Emd.Fault.pcOutOfRange",
        "fault Emd.Fault.divisionByZero",
        "fault Emd.Fault.negativeAddress",
        "fault Emd.Fault.invalidByte",
    ] {
        assert!(kinds.get(kind).is_some_and(|&n| n >= 20), "too few `{kind}`: {kinds:?}");
    }
}

/// Raw sources, valid and damaged: the three decoders must agree.
fn raw_sources() -> Vec<Vec<u8>> {
    const EXAMPLE: &str = "-\u{2010}-\u{2011}\u{2011}-\u{2013}\u{2012}";
    let chars: Vec<char> = EXAMPLE.chars().collect();
    let mut sources: Vec<Vec<u8>> = Vec::new();
    for cut in 0..=chars.len() {
        let (a, b): (String, String) = (chars[..cut].iter().collect(), chars[cut..].iter().collect());
        sources.push(format!("{a}\n{b}").into_bytes());
        sources.push(format!("\n\n{a}\n\n\n{b}\n\n").into_bytes());
    }
    let push0 = "--";
    for fixed in [
        String::new(),
        "\n".to_string(),
        format!("{EXAMPLE}\n"),
        format!("{EXAMPLE}\r\n"),
        format!("{EXAMPLE} "),
        format!("\u{FEFF}{EXAMPLE}"),
        format!("{EXAMPLE}\u{2028}"),
        format!("{EXAMPLE}\u{FE58}"),
        "-".to_string(),
        "-\n-\n-".to_string(),
        "\u{2212}\u{2212}".to_string(),
        "-\n\u{2212}\n\u{2212}\n\u{2212}".to_string(),
        "x".to_string(),
        push0.repeat(LINE_MAX / 2),
        format!("{}-", push0.repeat(LINE_MAX / 2)),
        format!("{}\n", push0.repeat(LINE_MAX / 2)),
        format!("{}--", push0.repeat(LINE_MAX / 2)),
        format!("{}\n--", push0.repeat(LINE_MAX / 2)),
        format!("--\n{}--", push0.repeat(LINE_MAX / 2)),
        // A foreign code point past the limit: both faults, either way a rejection.
        format!("{}x", push0.repeat(LINE_MAX)),
        // The limit counts code points, not bytes.
        "\u{2010}-".repeat(LINE_MAX / 2),
        format!("{}\u{2010}", "\u{2010}-".repeat(LINE_MAX / 2)),
    ] {
        sources.push(fixed.into_bytes());
    }
    sources.extend([
        vec![0xFF],
        vec![b'-', 0xE2, 0x80],
        vec![0xC0, 0xAD],
        // Overlong `-`, twice: an even count of what a lax decoder would call dashes.
        vec![0xC0, 0xAD, 0xC0, 0xAD],
        // Overlong U+2010 in four bytes, and a surrogate.
        vec![0xF0, 0x82, 0x80, 0x90, b'-'],
        vec![0xED, 0xA0, 0x80, b'-'],
        "\u{1F600}-".as_bytes().to_vec(),
        "\u{1F600}\u{1F600}".as_bytes().to_vec(),
    ]);

    let all: Vec<Instr> = Instr::all().collect();
    let mut state = 0xBF58_476D_1CE4_E5B9_u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..600 {
        let length = next() % 90;
        let program: Vec<Instr> = (0..length).map(|_| all[(next() % all.len() as u64) as usize]).collect();
        let mut text = String::new();
        let mut column = 0;
        let width = 1 + next() % (LINE_MAX as u64 + 6);
        for c in encode_program(&program).chars() {
            // Usually within the limit, sometimes past it.
            if column == width || next().is_multiple_of(23) {
                text.push('\n');
                column = 0;
            }
            text.push(c);
            column += 1;
        }
        if next().is_multiple_of(5) {
            let damage =
                ["\r", " ", "\t", "-", "x", "\u{FEFF}", "\u{2028}", "\u{FE58}"][(next() % 8) as usize];
            let at = text
                .char_indices()
                .map(|(i, _)| i)
                .nth((next() % (text.chars().count() as u64 + 1)) as usize)
                .unwrap_or(text.len());
            text.insert_str(at, damage);
        }
        sources.push(text.into_bytes());
    }
    sources
}

fn compare_sources(exe: &Path, tag: &str) {
    let tmp = std::env::temp_dir().join(format!("emd-layouts-{tag}-{}", std::process::id()));
    fs::create_dir_all(&tmp).unwrap();
    let (file, input) = (tmp.join("p.emd"), tmp.join("p.in"));
    fs::write(&input, b"").unwrap();
    let (mut accepted, mut rejected) = (0, 0);
    for source in raw_sources() {
        fs::write(&file, &source).unwrap();
        let out = Command::new(exe).arg(&file).arg(&input).arg(FUEL.to_string()).output().unwrap();
        let shown = String::from_utf8_lossy(&source).into_owned();
        match emd_parser::parse_bytes(&source) {
            Err(e) => {
                rejected += 1;
                assert!(!out.status.success(), "{tag} accepts what Rust rejects ({e}): {shown:?}");
            }
            Ok(program) => {
                accepted += 1;
                assert!(out.status.success(), "{tag} rejects what Rust accepts: {shown:?}");
                if let Some(expected) = rust_outcome(&program, b"") {
                    assert_eq!(String::from_utf8_lossy(&out.stdout), expected, "{tag} on {shown:?}");
                }
            }
        }
    }
    fs::remove_dir_all(&tmp).unwrap();
    eprintln!("{tag}: {accepted} sources accepted by both, {rejected} rejected by both");
    assert!(accepted > 100 && rejected > 100, "{accepted} accepted, {rejected} rejected");
}

#[test]
fn rust_and_lean_accept_the_same_sources() {
    if let Some(exe) = interpreter(LEAN[0], LEAN[1], LEAN[2]) {
        compare_sources(&exe, "lean-sources");
    }
}

#[test]
fn rust_and_rocq_accept_the_same_sources() {
    if let Some(exe) = interpreter(ROCQ[0], ROCQ[1], ROCQ[2]) {
        compare_sources(&exe, "rocq-sources");
    }
}

const LEAN: [&str; 3] =
    ["formal/lean/.lake/build/bin/emdref", "EMD_REQUIRE_LEAN", "cd formal/lean && lake build"];
const ROCQ: [&str; 3] = ["formal/rocq/emdref-rocq", "EMD_REQUIRE_ROCQ", "formal/rocq/build.sh"];

#[test]
fn rust_matches_lean() {
    if let Some(exe) = interpreter(LEAN[0], LEAN[1], LEAN[2]) {
        compare_with(&exe, "lean", &sampled_cases());
    }
}

#[test]
fn rust_matches_rocq() {
    if let Some(exe) = interpreter(ROCQ[0], ROCQ[1], ROCQ[2]) {
        compare_with(&exe, "rocq", &sampled_cases());
    }
}

#[test]
fn rust_matches_lean_on_every_short_program() {
    if let Some(exe) = interpreter(LEAN[0], LEAN[1], LEAN[2]) {
        compare_with(&exe, "lean-exhaustive", &exhaustive_cases());
    }
}

#[test]
fn rust_matches_rocq_on_every_short_program() {
    if let Some(exe) = interpreter(ROCQ[0], ROCQ[1], ROCQ[2]) {
        compare_with(&exe, "rocq-exhaustive", &exhaustive_cases());
    }
}

/// The compiler written in emd, run by a model: the bytes `emd asm` gives. Only examples that
/// fit: the models walk their memory for every access, so the compiler compiling itself does not.
fn compile_in(exe: &Path, names: &[&str]) {
    for name in names {
        let out = Command::new(exe)
            .arg(repo().join("compiler/asm.emd"))
            .arg(repo().join(format!("examples/{name}.asm")))
            .arg("10000000")
            .output()
            .unwrap();
        let expected = fs::read(repo().join(format!("examples/{name}.emd"))).unwrap();
        assert_eq!(
            String::from_utf8(out.stdout).unwrap(),
            format!("halt\nstack []\noutput {expected:?}\n"),
            "{name}"
        );
    }
}

#[test]
fn lean_runs_the_compiler_in_emd() {
    if let Some(exe) = interpreter(LEAN[0], LEAN[1], LEAN[2]) {
        compile_in(&exe, &["add", "hello", "cat"]);
    }
}

#[test]
fn rocq_runs_the_compiler_in_emd() {
    if let Some(exe) = interpreter(ROCQ[0], ROCQ[1], ROCQ[2]) {
        compile_in(&exe, &["add"]);
    }
}

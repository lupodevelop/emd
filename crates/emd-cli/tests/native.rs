// emd: an esoteric language written only in Unicode dashes.
// C backend against VM under UBSan. A missing `cc` skips; `EMD_REQUIRE_CC=1` fails.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::Instr;
use emd_vm::{Fault, Limits, Status, Vm};
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn cc_available() -> bool {
    let found = Command::new("cc").arg("--version").output().is_ok_and(|o| o.status.success());
    assert!(found || std::env::var_os("EMD_REQUIRE_CC").is_none(), "cc is required");
    if !found {
        eprintln!("native test skipped: cc not found");
    }
    found
}

fn compile(program: &[Instr], dir: &Path, name: &str) -> PathBuf {
    let (c, exe) = (dir.join(format!("{name}.c")), dir.join(name));
    fs::write(&c, emd_c::to_c(program)).unwrap();
    let done = Command::new("cc")
        .args(["-O0", "-w", "-fsanitize=undefined", "-fno-sanitize-recover=all", "-o"])
        .arg(&exe)
        .arg(&c)
        .output()
        .unwrap();
    assert!(done.status.success(), "{}", String::from_utf8_lossy(&done.stderr));
    exe
}

fn fault_name(fault: &Fault) -> String {
    match fault {
        Fault::NegativeAddress(_) => "negative address".into(),
        Fault::PcOutOfRange(_) => "pc is outside the program".into(),
        Fault::InvalidByte(_) => "not a byte".into(),
        Fault::Overflow => "64-bit overflow".into(),
        other => other.to_string(),
    }
}

/// `true` if compared, `false` if the VM does not finish on it.
fn compare(program: &[Instr], input: &[u8], exe: &Path) -> bool {
    let limits = Limits { max_steps: 200_000, ..Limits::default() };
    let mut vm = Vm::new(program, limits);
    let mut expected = Vec::new();
    vm.run(&mut &input[..], &mut expected);
    if vm.status == Status::Faulted(Fault::StepLimit) {
        return false;
    }
    let mut child = Command::new(exe)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let _ = child.stdin.take().unwrap().write_all(input);
    let got = child.wait_with_output().unwrap();
    let stderr = String::from_utf8_lossy(&got.stderr);
    assert_eq!(got.stdout, expected, "{program:?} on {input:?}, stderr {stderr}");
    match &vm.status {
        Status::Halted => assert_eq!(got.status.code(), Some(0), "{program:?}: {stderr}"),
        Status::Faulted(f) => {
            assert_eq!(got.status.code(), Some(1), "{program:?}: {stderr}, expected {f}");
            assert_eq!(stderr.trim(), format!("fault: {}", fault_name(f)), "{program:?}");
        }
        Status::Running => unreachable!(),
    }
    true
}

/// A file that fails, for the VM.
struct Broken;

impl Read for Broken {
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        Err(io::Error::other("broken"))
    }
}

impl Write for Broken {
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(io::Error::other("broken"))
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// A closed descriptor is the failing file for C. `sh` closes it: Rust would reopen it.
#[test]
fn io_errors_fault_like_the_vm() {
    if !cc_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("emd-native-io-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let one = Instr::from_mnemonic("PUSH 1").unwrap();
    let zero = Instr::from_mnemonic("PUSH 0").unwrap();
    // A division by zero waits after each failure: a program that ignores the error reaches it.
    let then_fault = [one, zero, Instr::Div, Instr::Halt];
    let past_the_buffer = [[one, Instr::Write].repeat(10_000), then_fault.to_vec()].concat();
    let before_a_read = [&[one, Instr::Write, Instr::Read][..], &then_fault].concat();
    for (name, program, closed) in [
        ("at-halt", vec![one, Instr::Write, Instr::Halt], ">&-"),
        ("at-write", past_the_buffer, ">&-"),
        ("at-prompt", before_a_read, ">&-"),
        ("at-read", [&[Instr::Read][..], &then_fault].concat(), "<&-"),
    ] {
        let mut vm = Vm::new(&program, Limits::default());
        vm.run(&mut Broken, &mut Broken);
        assert!(matches!(vm.status, Status::Faulted(Fault::Io(_))), "{name}");
        let exe = compile(&program, &dir, name);
        let got =
            Command::new("sh").arg("-c").arg(format!("exec \"$0\" {closed}")).arg(&exe).output().unwrap();
        let stderr = String::from_utf8_lossy(&got.stderr);
        assert_eq!(got.status.code(), Some(1), "{name}: {stderr}");
        assert_eq!(stderr.trim(), "fault: i/o error", "{name}");
    }
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn examples_match_the_vm() {
    if !cc_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("emd-native-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    for (name, input) in [
        ("hello", &b""[..]),
        ("cat", b"ciao"),
        ("truth", b"0"),
        ("fizzbuzz", b""),
        ("add", b"34"),
        ("brainfuck", b",[.,]!hi"),
        ("functions", b""),
    ] {
        let program =
            emd_parser::parse_bytes(&fs::read(root.join(name).with_extension("emd")).unwrap()).unwrap();
        let exe = compile(&program, &dir, name);
        assert!(compare(&program, input, &exe), "{name} did not finish");
    }
    fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn random_programs_match_the_vm() {
    if !cc_available() {
        return;
    }
    let dir = std::env::temp_dir().join(format!("emd-native-r-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let all: Vec<Instr> = Instr::all().collect();
    let pushes: Vec<Instr> = all.iter().copied().filter(|i| matches!(i, Instr::Push(_))).collect();
    let mut state = 0xA076_1D64_78BD_642F_u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut compared = 0;
    for k in 0..150 {
        let mut program: Vec<Instr> = Vec::new();
        for _ in 0..1 + next() % 30 {
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
        let exe = compile(&program, &dir, &format!("r{k}"));
        let input: Vec<u8> = (0..next() % 4).map(|_| next() as u8).collect();
        compared += usize::from(compare(&program, &input, &exe));
    }
    assert!(compared > 100, "only {compared} compared");
    // Values the random programs rarely reach: the C must not hit undefined behavior on them.
    let min = |ops: &[&str]| -> Vec<Instr> {
        // i64::MIN as -2^62 * 2: PUSH 2, then doubled 62 times, negated, doubled.
        let mut p: Vec<Instr> = vec![Instr::from_mnemonic("PUSH 1").unwrap()];
        for _ in 0..62 {
            p.extend([Instr::from_mnemonic("PUSH 2").unwrap(), Instr::Mul]);
        }
        p.extend([
            Instr::from_mnemonic("PUSH 0").unwrap(),
            Instr::Swap,
            Instr::Sub,
            Instr::from_mnemonic("PUSH 2").unwrap(),
            Instr::Mul,
        ]);
        p.extend(ops.iter().map(|m| Instr::from_mnemonic(m).unwrap()));
        p.push(Instr::Halt);
        p
    };
    let minus_one = ["PUSH 0", "PUSH 1", "SUB"];
    for (i, last) in [["DIV"], ["MOD"], ["MUL"]].iter().enumerate() {
        let p = min(&[minus_one[0], minus_one[1], minus_one[2], last[0]]);
        let exe = compile(&p, &dir, &format!("min{i}"));
        assert!(compare(&p, b"", &exe));
    }
    fs::remove_dir_all(&dir).unwrap();
}

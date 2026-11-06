// emd: an esoteric language written only in Unicode dashes.
// The binary as a user meets it: exit codes, exact bytes, closed pipes.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

const EXAMPLE: &str = "-\u{2010}-\u{2011}\u{2011}-\u{2013}\u{2012}";

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn example(name: &str) -> String {
    root().join("examples").join(name).display().to_string()
}

fn emd(args: &[&str], stdin: &[u8]) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_emd"))
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // The program may stop reading first; a closed stdin here is not a failure.
    let _ = child.stdin.take().unwrap().write_all(stdin);
    child.wait_with_output().unwrap()
}

/// A file of exact bytes, deleted on drop.
struct Temp(PathBuf);

impl Temp {
    fn new(name: &str, bytes: &[u8]) -> Temp {
        let path = std::env::temp_dir().join(format!("emd-cli-{}-{name}", std::process::id()));
        fs::write(&path, bytes).unwrap();
        Temp(path)
    }

    fn path(&self) -> &str {
        self.0.to_str().unwrap()
    }
}

impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn code(o: &Output) -> i32 {
    o.status.code().expect("killed by a signal")
}

#[test]
fn run_writes_exact_bytes_and_reads_stdin() {
    let o = emd(&["run", &example("hello.emd")], b"");
    assert_eq!((code(&o), &o.stdout[..]), (0, &b"Hello, world!\n"[..]));

    let o = emd(&["run", &example("cat.emd")], "é\n\u{2014}\0".as_bytes());
    assert_eq!((code(&o), &o.stdout[..]), (0, "é\n\u{2014}\0".as_bytes()));

    let o = emd(&["run", &example("brainfuck.emd")], b",[.,]!hi");
    assert_eq!((code(&o), &o.stdout[..]), (0, &b"hi"[..]));
}

#[test]
fn a_fault_exits_1_and_keeps_earlier_output() {
    // PUSH 0 WRITE, then DROP on an empty stack.
    let bad = Temp::new("fault.emd", "--\u{2014}\u{2010}\u{2010}\u{2010}\u{2013}\u{2012}".as_bytes());
    let o = emd(&["run", bad.path()], b"");
    assert_eq!((code(&o), &o.stdout[..]), (1, &[0u8][..]));
    assert!(String::from_utf8_lossy(&o.stderr).contains("stack underflow"));
}

#[test]
fn newlines_mean_nothing_and_a_long_line_is_rejected_and_explained() {
    let spaced = Temp::new("newline.emd", "-\u{2010}-\n\u{2011}\u{2011}-\u{2013}\u{2012}\n".as_bytes());
    let file = spaced.0.display().to_string();
    assert!(emd(&["run", &file], b"").status.success());
    let fmt = emd(&["fmt", &file], b"");
    assert_eq!(String::from_utf8(fmt.stdout).unwrap(), format!("{EXAMPLE}\n"));

    let long = Temp::new("long.emd", "-".repeat(34).as_bytes());
    let file = long.0.display().to_string();
    let o = emd(&["run", &file], b"");
    assert_eq!(o.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&o.stderr).contains("line 1 is longer than 32"), "{o:?}");
    let o = emd(&["doctor", &file], b"");
    assert_eq!(o.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&o.stdout).contains("line 1 has 34 code points, the limit is 32"),
        "{o:?}"
    );
    let fixed = emd(&["fmt", &file], b"");
    assert!(fixed.status.success(), "fmt repairs what the decoder rejects: {fixed:?}");
    assert_eq!(fixed.stdout.iter().filter(|&&b| b == b'\n').count(), 2);

    let crlf = Temp::new("crlf.emd", format!("{EXAMPLE}\r\n").as_bytes());
    let o = emd(&["doctor", &crlf.0.display().to_string()], b"");
    assert!(String::from_utf8_lossy(&o.stdout).contains("carriage return"), "{o:?}");
    assert!(emd(&["fmt", &crlf.0.display().to_string()], b"").status.code() == Some(1));
}

#[test]
fn asm_emits_only_dashes_and_disasm_reverses_it() {
    let o = emd(&["asm", &example("add.asm")], b"");
    assert_eq!((code(&o), String::from_utf8(o.stdout).unwrap()), (0, format!("{EXAMPLE}\n")));

    let good = Temp::new("rt.emd", EXAMPLE.as_bytes());
    let listing = emd(&["disasm", good.path()], b"");
    assert_eq!(String::from_utf8(listing.stdout.clone()).unwrap(), "PUSH 1\nPUSH 2\nADD\nHALT\n");
    let text = Temp::new("rt.asm", &listing.stdout);
    assert_eq!(emd(&["asm", text.path()], b"").stdout, format!("{EXAMPLE}\n").as_bytes());

    let broken = Temp::new("broken.asm", b"ADD\nNOPE\n");
    let o = emd(&["asm", broken.path()], b"");
    assert!(o.stdout.is_empty(), "no partial output on a compile error");
    assert_eq!(code(&o), 1);
    let stderr = String::from_utf8_lossy(&o.stderr).into_owned();
    assert!(stderr.contains(&format!("{}:2:1\n", broken.path())), "{stderr}");
    assert!(stderr.contains("2 | NOPE\n"), "{stderr}");
    assert!(stderr.contains("^^^^"), "{stderr}");
}

#[test]
fn every_example_is_up_to_date_and_passes_check() {
    for entry in fs::read_dir(root().join("examples")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_some_and(|e| e == "asm") {
            let compiled = emd(&["asm", path.to_str().unwrap()], b"");
            let committed = fs::read(path.with_extension("emd")).unwrap();
            assert_eq!(compiled.stdout, committed, "{}", path.display());
            let source = path.with_extension("emd");
            assert_eq!(code(&emd(&["check", source.to_str().unwrap()], b"")), 0);
            assert_eq!(code(&emd(&["doctor", source.to_str().unwrap()], b"")), 0);
        }
    }
}

#[test]
fn verify_reports_three_verdicts() {
    assert_eq!(code(&emd(&["verify", &example("hello.emd")], b"")), 0);
    let forever = Temp::new("forever.asm", b"loop: JMP loop\n");
    let compiled = emd(&["asm", forever.path()], b"");
    let source = Temp::new("forever.emd", &compiled.stdout);
    assert_eq!(code(&emd(&["verify", "--max-steps", "100", source.path()], b"")), 3);
    let nohalt = Temp::new("nohalt.emd", b"--");
    let o = emd(&["verify", nohalt.path()], b"");
    assert_eq!(code(&o), 1);
    assert!(String::from_utf8_lossy(&o.stdout).contains("ABSENT"));
}

#[test]
fn max_steps_stops_run_and_trace() {
    let o = emd(&["run", "--max-steps", "50", &example("truth.emd")], b"1");
    assert_eq!(code(&o), 1);
    assert!(String::from_utf8_lossy(&o.stderr).contains("step limit"));
    let o = emd(&["trace", "--max-steps", "3", &example("truth.emd")], b"1");
    assert_eq!(code(&o), 1);
    assert!(String::from_utf8_lossy(&o.stderr).contains("pc="));
}

#[test]
fn color_refuses_control_sequences_but_paints_invalid_programs() {
    let hostile = Temp::new("esc.emd", b"\x1b[2J");
    let o = emd(&["color", hostile.path()], b"");
    assert_eq!(code(&o), 1);
    assert!(o.stdout.is_empty());

    // Odd length and unassigned pairs still get their colors.
    let odd = Temp::new("odd.emd", "\u{2212}\u{2212}-".as_bytes());
    let o = emd(&["color", odd.path()], b"");
    assert_eq!(code(&o), 0);
    assert!(o.stdout.starts_with(b"\x1b[31m"));
}

#[test]
fn wrong_usage_exits_2_and_missing_files_exit_1() {
    assert_eq!(code(&emd(&[], b"")), 2);
    assert_eq!(code(&emd(&["nosuch"], b"")), 2);
    assert_eq!(code(&emd(&["run"], b"")), 2);
    assert_eq!(code(&emd(&["run", "--max-steps", "x", "f"], b"")), 2);
    assert_eq!(code(&emd(&["run", "--max-steps"], b"")), 2);
    assert_eq!(code(&emd(&["run", "--input"], b"")), 2);
    let hello = example("hello.emd");
    for wrong in [
        vec!["c", "--max-steps", "5", hello.as_str()],
        vec!["debug", "--max-steps", "5", hello.as_str()],
        vec!["run", "--input", hello.as_str(), hello.as_str()],
        vec!["run", "--machine", hello.as_str()],
        vec!["reduce", "--machine", hello.as_str()],
    ] {
        let o = emd(&wrong, b"");
        assert_eq!(code(&o), 2, "{wrong:?}");
        assert!(String::from_utf8_lossy(&o.stderr).contains("does not apply"), "{wrong:?}");
    }
    // Flags go anywhere.
    for order in [
        vec!["debug", hello.as_str(), "--input", hello.as_str(), "--machine"],
        vec!["debug", "--machine", "--input", hello.as_str(), hello.as_str()],
    ] {
        assert_eq!(code(&emd(&order, b"q\n")), 0, "{order:?}");
    }
    assert_eq!(code(&emd(&["run", "/nonexistent/file.emd"], b"")), 1);
    assert_eq!(code(&emd(&["--help"], b"")), 0);
    let v = emd(&["--version"], b"");
    assert!(String::from_utf8_lossy(&v.stdout).starts_with("emd "));
}

/// `emd inspect x | head` must not panic: panics exit 101.
#[test]
fn a_closed_stdout_is_not_a_panic() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_emd"))
        .args(["inspect", &example("brainfuck.emd")])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    drop(child.stdout.take());
    let o = child.wait_with_output().unwrap();
    assert_ne!(o.status.code(), Some(101), "{}", String::from_utf8_lossy(&o.stderr));
}

#[test]
fn diff_shows_the_code_points_that_differ() {
    let a = Temp::new("a.emd", EXAMPLE.as_bytes());
    // ADD (U+2011 U+002D) becomes SUB (U+2011 U+2010).
    let b = Temp::new("b.emd", "-\u{2010}-\u{2011}\u{2011}\u{2010}\u{2013}\u{2012}".as_bytes());
    let o = emd(&["diff", a.path(), b.path()], b"");
    let text = String::from_utf8(o.stdout).unwrap();
    assert!(text.contains("U+2011 U+002D  ADD") && text.contains("U+2011 U+2010  SUB"), "{text}");
    assert!(text.ends_with("-1 +1: 4 instructions -> 4\n"), "{text}");
}

/// A prompt with no newline must reach the user before the program waits for input.
#[test]
fn a_prompt_appears_before_the_program_reads() {
    use std::io::Read;
    let text = Temp::new("prompt.asm", b"PRINT \"?\" READ WRITE HALT\n");
    let source = Temp::new("prompt.emd", &emd(&["asm", text.path()], b"").stdout);
    let mut child = Command::new(env!("CARGO_BIN_EXE_emd"))
        .args(["run", source.path()])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut stdin = child.stdin.take().unwrap();
    let mut stdout = child.stdout.take().unwrap();
    // Stdin stays open here, so the program can only get this far by flushing.
    let mut prompt = [0u8; 1];
    stdout.read_exact(&mut prompt).unwrap();
    assert_eq!(&prompt, b"?");
    stdin.write_all(b"x").unwrap();
    drop(stdin);
    let mut rest = Vec::new();
    stdout.read_to_end(&mut rest).unwrap();
    assert_eq!(rest, b"x");
    assert!(child.wait().unwrap().success());
}

#[test]
fn keys_turn_letters_into_a_program_that_runs() {
    let typed = "as ad dd da gf";
    let typed = emd(&["keys"], typed.as_bytes());
    assert!(typed.status.success());
    let program = Temp::new("keys.emd", &typed.stdout);
    let check = emd(&["check", &program.0.display().to_string()], b"");
    assert!(check.status.success(), "{check:?}");

    let missing = emd(&["keys", "/nonexistent/keys"], b"");
    assert_eq!(missing.status.code(), Some(1));

    let wrong = emd(&["keys"], b"asz");
    assert_eq!(wrong.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&wrong.stderr).contains("`z`"));
}

#[test]
fn debug_steps_forward_and_back_from_a_script() {
    let program = Temp::new("debug.emd", EXAMPLE.as_bytes());
    let script = b"s\n\nb\np\nc\nq\nnever\n";
    let out = emd(&["debug", &program.0.display().to_string()], script);
    assert!(out.status.success(), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    // Two steps forward (the empty line repeats), one back, leaving only PUSH 1 done.
    assert!(text.contains("step 2  pc 2  ADD  stack [1, 2]"), "{text}");
    assert!(text.matches("step 1  pc 1  PUSH 2  stack [1]").count() >= 2, "{text}");
    assert!(text.contains("halted"), "{text}");
}

#[test]
fn analyze_proves_what_it_can_and_says_what_it_cannot() {
    let proved = emd(&["analyze", &example("hello.emd")], b"");
    assert_eq!(proved.status.code(), Some(0), "{proved:?}");
    assert!(String::from_utf8_lossy(&proved.stdout).contains("proved:     no stack underflow"));

    let underflow = Temp::new("under.emd", "\u{2011}-\u{2013}\u{2012}".as_bytes());
    let found = emd(&["analyze", &underflow.0.display().to_string()], b"");
    assert_eq!(found.status.code(), Some(3));
    assert!(
        String::from_utf8_lossy(&found.stdout)
            .contains("not proved: no stack underflow: pc 0 (certain if reached)")
    );
}

#[test]
fn cfg_profile_reduce_and_slop_work_from_the_command_line() {
    let cfg = emd(&["cfg", &example("hello.emd")], b"");
    assert!(String::from_utf8_lossy(&cfg.stdout).starts_with("digraph emd {"));

    let profiled = emd(&["profile", &example("hello.emd")], b"");
    assert!(profiled.status.success(), "{profiled:?}");
    assert_eq!(profiled.stdout, b"Hello, world!\n");
    assert!(String::from_utf8_lossy(&profiled.stderr).contains("hottest pc:"));

    let noisy = Temp::new("noisy.emd", format!("--\u{2010}\u{2010}{EXAMPLE}").as_bytes());
    let small = emd(&["reduce", &noisy.0.display().to_string()], b"");
    assert!(small.status.success(), "{small:?}");
    assert!(small.stdout.len() < EXAMPLE.len() + 8);
    assert!(String::from_utf8_lossy(&small.stderr).contains("instructions down to"));

    let looping = Temp::new("loop.emd", "--\u{2010}\u{2013}-".as_bytes());
    let refused = emd(&["reduce", "--max-steps", "1000", &looping.0.display().to_string()], b"");
    assert!(refused.status.success() || refused.status.code() == Some(1));

    let prose = Temp::new(
        "prose.txt",
        "Not just code - \u{2010}it is a vibe. Truly \u{2014}\u{2014} deep.".as_bytes(),
    );
    let slop = emd(&["slop", &prose.0.display().to_string()], b"");
    assert!(slop.status.success(), "{slop:?}");
    let report = String::from_utf8_lossy(&slop.stderr);
    assert!(report.contains("4 dashes"), "{report}");
    assert!(report.contains("1 pairs meant nothing"), "{report}");
    assert!(report.contains("PUSH 1"), "{report}");
}

#[test]
fn debug_machine_mode_answers_each_command_with_one_json_line() {
    let program = Temp::new("machine.emd", EXAMPLE.as_bytes());
    let out = emd(&["debug", &program.0.display().to_string(), "--machine"], b"s 3\nq\n");
    assert!(out.status.success(), "{out:?}");
    let text = String::from_utf8(out.stdout).unwrap();
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 2, "{text}");
    assert!(lines[0].starts_with(r#"{"step":0,"pc":0,"status":"running","stack":[]"#), "{text}");
    assert!(lines[1].starts_with(r#"{"step":3,"pc":3,"status":"running","stack":[3]"#), "{text}");
}

/// A reader that leaves, as `head` does, is not an error and never a panic.
#[test]
fn a_closed_pipe_ends_quietly() {
    let closed_stdout = |args: &[&str]| {
        let mut child = Command::new(env!("CARGO_BIN_EXE_emd"))
            .args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        drop(child.stdout.take());
        let out = child.wait_with_output().unwrap();
        (out.status.code(), String::from_utf8_lossy(&out.stderr).into_owned())
    };
    let closed_stderr = |args: &[&str]| {
        let mut child = Command::new(env!("CARGO_BIN_EXE_emd"))
            .args(args)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        drop(child.stderr.take());
        child.wait().unwrap().code()
    };
    let program = example("fizzbuzz.emd");
    let program = program.as_str();
    assert_eq!(closed_stdout(&["run", program]), (Some(0), String::new()));
    assert_eq!(closed_stdout(&["inspect", program]), (Some(0), String::new()));
    assert_eq!(closed_stdout(&["profile", program]), (Some(0), String::new()));
    assert_eq!(closed_stderr(&["run", program]), Some(0));
    // The step limit would end in a fault: the trace has to stop at the first line it can't write.
    assert_eq!(closed_stderr(&["trace", "--max-steps", "1000", program]), Some(0));
    assert_eq!(closed_stderr(&["profile", program]), Some(0));
    assert_eq!(closed_stderr(&["nope"]), Some(2));
}

#[test]
fn the_report_commands_print_what_they_promise() {
    let hello = example("hello.emd");
    let hello = hello.as_str();
    let stdout = |args: &[&str]| {
        let out = emd(args, b"");
        assert_eq!(out.status.code(), Some(0), "{args:?}");
        String::from_utf8(out.stdout).unwrap()
    };
    assert!(stdout(&["c", hello]).contains("int main(void)"));
    assert!(stdout(&["explain", hello]).contains("HALT"));
    let trace = emd(&["trace", hello], b"");
    assert!(String::from_utf8_lossy(&trace.stderr).contains("halted after"));
}

#[test]
fn the_debugger_ends_when_its_input_does() {
    assert_eq!(emd(&["debug", example("hello.emd").as_str()], b"").status.code(), Some(0));
}

#[test]
fn every_command_names_the_file_it_cannot_read() {
    let missing = root().join("no-such-file.emd").display().to_string();
    let hello = example("hello.emd");
    let (m, h) = (missing.as_str(), hello.as_str());
    let commands: [&[&str]; 22] = [
        &["run", m],
        &["trace", m],
        &["debug", m],
        &["debug", h, "--input", m],
        &["profile", m],
        &["slop", m],
        &["asm", m],
        &["disasm", m],
        &["keys", m],
        &["fmt", m],
        &["c", m],
        &["check", m],
        &["inspect", m],
        &["explain", m],
        &["color", m],
        &["diff", m, h],
        &["diff", h, m],
        &["analyze", m],
        &["cfg", m],
        &["doctor", m],
        &["reduce", m],
        &["reduce", h, "--input", m],
    ];
    for args in commands {
        let out = emd(args, b"");
        assert_eq!(out.status.code(), Some(1), "{args:?}");
        assert!(String::from_utf8_lossy(&out.stderr).contains("no-such-file"), "{args:?}");
    }
    let out = emd(&["verify", m], b"");
    assert!(String::from_utf8_lossy(&out.stderr).contains("no-such-file"));
}

#[test]
fn reduce_needs_a_program_that_ends() {
    // PUSH 0, PUSH 3, SUB, JMP: jumps back to the start forever.
    let looping = Temp::new("endless.emd", "---\u{2012}\u{2011}\u{2010}\u{2013}-".as_bytes());
    let out = emd(&["reduce", "--max-steps", "100", &looping.0.display().to_string()], b"");
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("does not end within 100 steps"));
}

/// emd with stdout on a file that cannot grow past `kib` KiB, so a write past it fails with
/// EFBIG. SIGXFSZ stays ignored across `exec`: the error reaches emd instead of killing it.
fn on_a_full_disk(args: &[&str], kib: u32, stdin: &[u8]) -> Output {
    static RUNS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = RUNS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let file = std::env::temp_dir().join(format!("emd-cli-{}-full-{n}", std::process::id()));
    // Under coverage the limit would also cut the profile, and one bad profile fails the merge
    // of all of them: the profile goes through a pipe, which no file size limit applies to.
    let profile = std::env::var_os("LLVM_PROFILE_FILE").map(|p| {
        let dir = std::path::Path::new(&p).parent().unwrap().to_path_buf();
        dir.join(format!("emd-full-{}-{n}.profraw", std::process::id()))
    });
    let through_pipe = if profile.is_some() {
        "exec 3> >(cat > \"$EMD_PROFILE\"); export LLVM_PROFILE_FILE=/dev/fd/3; "
    } else {
        ""
    };
    let mut child = Command::new("bash")
        .arg("-c")
        .arg(format!("trap '' XFSZ; {through_pipe}ulimit -f {kib}; exec \"$0\" \"$@\" > \"$EMD_FULL\""))
        .arg(env!("CARGO_BIN_EXE_emd"))
        .args(args)
        .env("EMD_FULL", &file)
        .env("EMD_PROFILE", profile.unwrap_or_default())
        .stdin(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let _ = child.stdin.take().unwrap().write_all(stdin);
    let out = child.wait_with_output().unwrap();
    let _ = fs::remove_file(&file);
    out
}

#[test]
fn a_full_disk_is_an_error() {
    let (hello, source) = (example("hello.emd"), example("hello.asm"));
    let letters = Temp::new("letters.txt", b"asaddagf");
    // PUSH 7, WRITE, HALT: the byte waits in the buffer until the final flush.
    let waiting = Temp::new("waiting.emd", "-\u{2212}\u{2014}\u{2010}\u{2013}\u{2012}".as_bytes());
    let (h, l, w) = (hello.as_str(), letters.0.display().to_string(), waiting.0.display().to_string());
    let commands: [&[&str]; 19] = [
        &["check", h],
        &["inspect", h],
        &["explain", h],
        &["disasm", h],
        &["c", h],
        &["color", h],
        &["cfg", h],
        &["analyze", h],
        &["doctor", h],
        &["verify", h],
        &["fmt", h],
        &["asm", &source],
        &["keys", &l],
        &["reduce", h],
        &["diff", h, h],
        &["debug", h],
        &["run", &w],
        &["profile", &w],
        &["slop", &w],
    ];
    for args in commands {
        let out = on_a_full_disk(args, 0, b"");
        assert_eq!(out.status.code(), Some(1), "{args:?}");
        assert!(String::from_utf8_lossy(&out.stderr).contains("too large"), "{args:?}");
    }
    // Past the first state, a reply is what no longer fits.
    let out = on_a_full_disk(&["debug", h, "--machine"], 1, "s\n".repeat(100).as_bytes());
    assert_eq!(out.status.code(), Some(1));
    // READ flushes first, and the waiting byte fails there: the run stops on the disk's error.
    let reading = Temp::new("reading.emd", "-\u{2212}\u{2014}\u{2010}\u{2014}-\u{2013}\u{2012}".as_bytes());
    let out = on_a_full_disk(&["run", &reading.0.display().to_string()], 0, b"");
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("too large"));
}

#[test]
fn an_unreadable_stdin_is_an_error() {
    let hello = example("hello.emd");
    for args in [&["keys"][..], &["debug", hello.as_str()]] {
        let out = Command::new(env!("CARGO_BIN_EXE_emd"))
            .args(args)
            .stdin(fs::File::open("/").unwrap())
            .output()
            .unwrap();
        assert_eq!(out.status.code(), Some(1), "{args:?}");
        assert!(String::from_utf8_lossy(&out.stderr).contains("directory"), "{args:?}");
    }
}

#[test]
fn text_commands_need_utf8() {
    let bad = Temp::new("bad-utf8.asm", &[0xFF]);
    let out = emd(&["fmt", &bad.0.display().to_string()], b"");
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("utf-8"));
}

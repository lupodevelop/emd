// emd: an esoteric language written only in Unicode dashes.
// The parser and VM for the website. Exports return 4 bytes of little-endian length, then JSON.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_tools::json_text;
use emd_vm::{Limits, Status, Vm};

/// Short enough that a loop in a browser tab ends on its own.
const MAX_STEPS: u64 = 5_000_000;
/// A page should not hold more output than this.
const MAX_OUTPUT: usize = 1 << 20;

/// A writer that refuses to grow past [`MAX_OUTPUT`]: the VM reports it as an I/O fault.
struct Capped(Vec<u8>);

impl std::io::Write for Capped {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        if self.0.len() + buf.len() > MAX_OUTPUT {
            return Err(std::io::Error::other("output limit reached"));
        }
        self.0.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// `{"ok":bool,"status":text,"steps":n,"stack":[...],"output":text}`.
pub fn run(source: &[u8], input: &[u8]) -> String {
    let program = match emd_parser::parse_bytes(source) {
        Ok(p) => p,
        Err(e) => {
            return format!(
                r#"{{"ok":false,"status":{},"steps":0,"stack":[],"output":""}}"#,
                json_text(&e.to_string())
            );
        }
    };
    let limits = Limits { max_steps: MAX_STEPS, ..Limits::default() };
    let mut vm = Vm::new(&program, limits);
    let mut output = Capped(Vec::new());
    vm.run(&mut &input[..], &mut output);
    // The machine has stopped: the step limit makes sure of it.
    let (ok, status) = match &vm.status {
        Status::Faulted(f) => (false, format!("fault at pc {}: {f}", vm.pc)),
        _ => (true, String::from("halted")),
    };
    format!(
        r#"{{"ok":{ok},"status":{},"steps":{},"stack":{:?},"output":{}}}"#,
        json_text(&status),
        vm.steps,
        vm.stack,
        json_text(&String::from_utf8_lossy(&output.0))
    )
}

/// `{"problems":[...],"instructions":[{"index":n,"source":text,"name":text,"effect":text}]}`.
/// Instructions are listed only if the whole source decodes.
pub fn explain(source: &[u8]) -> String {
    let report = emd_parser::doctor(source);
    let problems: Vec<String> = report.problems.iter().map(|p| json_text(p)).collect();
    let instructions: Vec<String> = emd_parser::parse_bytes(source)
        .unwrap_or_default()
        .iter()
        .enumerate()
        .map(|(index, instr)| {
            format!(
                r#"{{"index":{index},"source":{},"name":{},"effect":{}}}"#,
                json_text(&instr.source()),
                json_text(&instr.to_string()),
                json_text(&instr.describe())
            )
        })
        .collect();
    format!(r#"{{"problems":[{}],"instructions":[{}]}}"#, problems.join(","), instructions.join(","))
}

/// The page reads the result, then frees it with [`emd_free`]: it asks on every keystroke.
fn deliver(json: String) -> *const u8 {
    let mut buffer = (json.len() as u32).to_le_bytes().to_vec();
    buffer.extend_from_slice(json.as_bytes());
    Box::leak(buffer.into_boxed_slice()).as_ptr()
}

/// Memory for the page to write its arguments into.
#[unsafe(no_mangle)]
pub extern "C" fn emd_alloc(len: usize) -> *mut u8 {
    Box::leak(vec![0u8; len].into_boxed_slice()).as_mut_ptr()
}

/// # Safety
/// `at` and `len` describe one whole buffer from [`emd_alloc`] or a result, not yet freed.
/// A result is 4 bytes longer than the length it carries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn emd_free(at: *mut u8, len: usize) {
    drop(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(at, len)) });
}

/// # Safety
/// The pointers come from [`emd_alloc`] with at least these lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn emd_run(
    source: *const u8,
    source_len: usize,
    input: *const u8,
    input_len: usize,
) -> *const u8 {
    let (source, input) = unsafe {
        (std::slice::from_raw_parts(source, source_len), std::slice::from_raw_parts(input, input_len))
    };
    deliver(run(source, input))
}

/// # Safety
/// The pointer comes from [`emd_alloc`] with at least this length.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn emd_explain(source: *const u8, source_len: usize) -> *const u8 {
    deliver(explain(unsafe { std::slice::from_raw_parts(source, source_len) }))
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE: &str = "-\u{2010}-\u{2011}\u{2011}-\u{2013}\u{2012}";

    #[test]
    fn run_reports_the_stack_and_the_output() {
        assert_eq!(
            run(EXAMPLE.as_bytes(), b""),
            r#"{"ok":true,"status":"halted","steps":4,"stack":[3],"output":""}"#
        );
        let hello = std::fs::read(concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples/hello.emd")).unwrap();
        assert!(run(&hello, b"").contains(r#""output":"Hello, world!\n""#));
    }

    #[test]
    fn errors_and_faults_are_reported_not_raised() {
        assert!(run(b"x", b"").contains(r#""ok":false"#));
        assert!(run("\u{2011}-".as_bytes(), b"").contains("stack underflow"));
        assert!(run(&[0xFF], b"").contains(r#""ok":false"#));
    }

    fn source(mnemonics: &[&str]) -> String {
        let program: Vec<_> = mnemonics.iter().map(|m| emd_core::Instr::from_mnemonic(m).unwrap()).collect();
        emd_core::encode_program(&program)
    }

    #[test]
    fn a_loop_ends_at_the_step_limit() {
        let looping = source(&["PUSH 0", "PUSH 3", "SUB", "JMP"]);
        assert!(run(looping.as_bytes(), b"").contains("step limit"));
    }

    #[test]
    fn output_is_capped() {
        // Offset -3 stays on the stack: 4 steps per byte, so the output limit comes first.
        let writes = source(&["PUSH 0", "PUSH 3", "SUB", "PUSH 1", "WRITE", "DUP", "JMP"]);
        let result = run(writes.as_bytes(), b"");
        assert!(result.contains("output limit reached"));
        assert!(std::io::Write::flush(&mut Capped(Vec::new())).is_ok());
    }

    #[test]
    fn explain_lists_instructions_only_for_a_valid_source() {
        let good = explain(EXAMPLE.as_bytes());
        assert!(good.contains(r#""problems":[]"#), "{good}");
        assert!(good.contains(r#""name":"HALT""#), "{good}");
        assert!(explain(format!("{EXAMPLE}\n").as_bytes()).contains(r#""problems":[]"#));
        let bad = explain(format!("{EXAMPLE} ").as_bytes());
        assert!(bad.contains("whitespace"), "{bad}");
        assert!(bad.contains(r#""instructions":[]"#), "{bad}");
    }

    /// The bytes written where the page would write them, as `emd_alloc` hands them out.
    fn written(bytes: &[u8]) -> (*mut u8, usize) {
        let at = emd_alloc(bytes.len());
        unsafe { std::ptr::copy_nonoverlapping(bytes.as_ptr(), at, bytes.len()) };
        (at, bytes.len())
    }

    /// The text of a result, which it then frees.
    fn taken(result: *const u8) -> String {
        let length = u32::from_le_bytes(unsafe { *result.cast::<[u8; 4]>() }) as usize;
        let bytes = unsafe { std::slice::from_raw_parts(result.add(4), length) };
        let text = String::from_utf8(bytes.to_vec()).unwrap();
        unsafe { emd_free(result.cast_mut(), 4 + length) };
        text
    }

    #[test]
    fn the_exports_work_the_way_the_page_calls_them() {
        let (source, source_len) = written(EXAMPLE.as_bytes());
        let (input, input_len) = written(b"");
        let ran = taken(unsafe { emd_run(source, source_len, input, input_len) });
        assert_eq!(ran, run(EXAMPLE.as_bytes(), b""));
        let explained = taken(unsafe { emd_explain(source, source_len) });
        assert_eq!(explained, explain(EXAMPLE.as_bytes()));
        unsafe {
            emd_free(source, source_len);
            emd_free(input, input_len);
        }
    }

    #[test]
    fn buffers_carry_their_length() {
        let p = deliver(String::from("{}"));
        let bytes = unsafe { std::slice::from_raw_parts(p, 6) };
        assert_eq!(bytes, [2, 0, 0, 0, b'{', b'}']);
        unsafe { emd_free(p.cast_mut(), 6) };
    }
}

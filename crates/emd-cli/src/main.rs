// emd: an esoteric language written only in Unicode dashes.
// The `emd` binary. Exit codes: 0 success, 1 decoding error or fault, 2 wrong usage, 3 `verify` without a verdict.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

mod commands;
mod system;

use std::process::ExitCode;

const USAGE: &str = "\
usage: emd <command> [--max-steps N] <file>

run:
  run <file>       execute: stdin feeds READ, WRITE goes to stdout
  trace <file>     like run, with one line per step on stderr
  debug <file> [--input <file>] [--machine]
                   debugger that also steps backward; h lists its commands.
                   --machine answers each command with one line of JSON
  profile <file>   run, then step counts per instruction and pc on stderr
  slop <file>      run the dashes hiding in any text, such as an LLM's prose
compile:
  asm <file>       compile readable assembly to dashes on stdout
  disasm <file>    dashes to one mnemonic per line, accepted by asm
  keys [file]      letters asdfghjk to dashes, from a file or stdin
  fmt <file>       the canonical layout: lines of 32 code points, on stdout
  c <file>         compile to C: emd c x.emd | cc -x c - -o x
understand:
  check <file>     decode only
  inspect <file>   instruction table with code points
  explain <file>   instruction table with effects
  color <file>     syntax highlighting: one color per line, zero information
  diff <a> <b>     instruction-level diff with code points
  analyze <file>   static analysis: reachability and the faults it can rule out
  cfg <file>       control flow graph for Graphviz: emd cfg x.emd | dot -Tsvg
diagnose:
  doctor <file>    Unicode diagnostics for a source that will not decode
  reduce <file> [--input <file>]
                   smaller program with the same output and ending
  verify <file>    decode, then a bounded run with empty input

--max-steps N limits run, trace, profile, verify and reduce. run, trace and profile
default to no limit, verify to 10000000, reduce to 1000000.
";

#[derive(Default)]
struct Flags {
    max_steps: Option<u64>,
    input: Option<String>,
    machine: bool,
}

impl Flags {
    /// Takes the flags out of the arguments, wherever they are.
    fn take(args: &mut Vec<String>) -> Result<Flags, String> {
        let max_steps = take_value(args, "--max-steps")?
            .map(|v| v.parse().map_err(|_| format!("--max-steps: `{v}` is not a number")))
            .transpose()?;
        let input = take_value(args, "--input")?;
        let machine = args.iter().position(|a| a == "--machine").map(|i| args.remove(i)).is_some();
        Ok(Flags { max_steps, input, machine })
    }

    /// A flag the command would ignore is wrong usage.
    fn check(&self, command: &str) -> Result<(), String> {
        let limited = matches!(command, "run" | "trace" | "profile" | "verify" | "reduce");
        let wrong = [
            ("--max-steps", self.max_steps.is_some() && !limited),
            ("--input", self.input.is_some() && !matches!(command, "debug" | "reduce")),
            ("--machine", self.machine && command != "debug"),
        ];
        match wrong.iter().find(|(_, is_wrong)| *is_wrong) {
            Some((flag, _)) => Err(format!("{flag} does not apply to `{command}`")),
            None => Ok(()),
        }
    }
}

fn take_value(args: &mut Vec<String>, flag: &str) -> Result<Option<String>, String> {
    let Some(i) = args.iter().position(|a| a == flag) else {
        return Ok(None);
    };
    if i + 1 == args.len() {
        return Err(format!("{flag} needs a value"));
    }
    let value = args.remove(i + 1);
    args.remove(i);
    Ok(Some(value))
}

fn dispatch(args: &[&str], flags: &Flags) -> Result<u8, String> {
    use commands as c;
    use system::emit;
    let input = flags.input.as_deref();
    match args {
        ["--help" | "-h" | "help"] => emit(USAGE.as_bytes()),
        ["--version" | "-V"] => emit(concat!("emd ", env!("CARGO_PKG_VERSION"), "\n").as_bytes()),
        ["run", file] => c::run(file, false, flags.max_steps),
        ["trace", file] => c::run(file, true, flags.max_steps),
        ["debug", file] => c::debug(file, input, flags.machine),
        ["profile", file] => c::profile(file, flags.max_steps),
        ["slop", file] => c::slop(file),
        ["asm", file] => c::asm(file),
        ["disasm", file] => c::disasm(file),
        ["keys"] => c::keys(None),
        ["keys", file] => c::keys(Some(file)),
        ["fmt", file] => c::fmt(file),
        ["c", file] => c::to_c(file),
        ["check", file] => c::check(file),
        ["inspect", file] => c::inspect(file),
        ["explain", file] => c::explain(file),
        ["color", file] => c::color(file),
        ["diff", a, b] => c::diff(a, b),
        ["analyze", file] => c::analyze(file),
        ["cfg", file] => c::cfg(file),
        ["doctor", file] => c::doctor(file),
        ["reduce", file] => c::reduce(file, input, flags.max_steps),
        ["verify", file] => c::verify(file, flags.max_steps),
        _ => {
            system::note(USAGE.trim_end());
            Ok(2)
        }
    }
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let flags = Flags::take(&mut args);
    let usable = flags.and_then(|f| f.check(args.first().map_or("", String::as_str)).map(|()| f));
    let flags = match usable {
        Ok(flags) => flags,
        Err(e) => {
            system::note(&format!("emd: {e}"));
            return ExitCode::from(2);
        }
    };
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    match dispatch(&args, &flags) {
        Ok(code) => ExitCode::from(code),
        Err(e) => {
            system::note(&format!("emd: {e}"));
            ExitCode::from(1)
        }
    }
}

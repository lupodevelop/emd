// emd: an esoteric language written only in Unicode dashes.
// One function per command: from arguments to a program, and from a result to the terminal.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::system::{PromptingStdin, emit, flush, load, note, read, text};
use emd_core::{Instr, format_program};
use emd_tools::Verdict;
use emd_vm::{Limits, Status, Vm};
use std::io::{self, Read};

const REDUCE_STEPS: u64 = 1_000_000;

pub fn run(file: &str, trace: bool, max_steps: Option<u64>) -> Result<u8, String> {
    let program = load(file)?;
    let limits = Limits { max_steps: max_steps.unwrap_or(u64::MAX), ..Limits::default() };
    let mut vm = Vm::new(&program, limits);
    let (mut input, mut output) = (PromptingStdin, io::stdout());
    if trace {
        while vm.status == Status::Running {
            let instr = program.get(vm.pc).map_or(String::new(), Instr::to_string);
            if !note(&format!("{:>8}  pc={:<5} {:<8} {:?}", vm.steps, vm.pc, instr, vm.stack)) {
                return Ok(0);
            }
            vm.step(&mut input, &mut output);
        }
    } else {
        vm.run(&mut input, &mut output);
    }
    if !flush()? {
        return Ok(0);
    }
    // The machine has stopped: it halted unless it faulted.
    if let Status::Faulted(f) = &vm.status {
        note(&format!("emd: {file}: fault at pc {} after {} steps: {f}", vm.pc, vm.steps));
        return Ok(1);
    }
    if trace {
        note(&format!("halted after {} steps, stack {:?}", vm.steps, vm.stack));
    }
    Ok(0)
}

/// The program's input comes from a file: stdin belongs to the debugger's commands.
pub fn debug(file: &str, input: Option<&str>, machine: bool) -> Result<u8, String> {
    let program = load(file)?;
    let input = input.map_or(Ok(Vec::new()), read)?;
    let mut debugger = emd_tools::Debugger::new(&program, &input);
    let first = if machine { debugger.json("") } else { debugger.show() };
    // Each reply ends with the next prompt, in one write.
    let prompt = if machine { "" } else { "(emd) " };
    emit(format!("{first}\n{prompt}").as_bytes())?;
    let mut last = String::from("s");
    let stdin = io::stdin();
    loop {
        let mut line = String::new();
        if stdin.read_line(&mut line).map_err(|e| e.to_string())? == 0 {
            return Ok(0);
        }
        // An empty line repeats the last command, as in gdb.
        let command = if line.trim().is_empty() { last.clone() } else { line.trim().to_string() };
        if command == "q" || command == "quit" {
            return Ok(0);
        }
        let reply = debugger.command(&command);
        let reply = if machine { debugger.json(&reply) } else { reply };
        emit(format!("{reply}\n{prompt}").as_bytes())?;
        last = command;
    }
}

pub fn profile(file: &str, max_steps: Option<u64>) -> Result<u8, String> {
    let program = load(file)?;
    let limits = Limits { max_steps: max_steps.unwrap_or(u64::MAX), ..Limits::default() };
    let mut output = io::stdout();
    let report = emd_tools::profile(&program, &mut PromptingStdin, &mut output, limits);
    if !flush()? {
        return Ok(0);
    }
    note(&report.to_string());
    Ok(u8::from(report.status != Status::Halted))
}

/// A fault is the expected ending for prose, so it still exits 0.
pub fn slop(file: &str) -> Result<u8, String> {
    let found = emd_tools::slop(&String::from_utf8_lossy(&read(file)?));
    let mut output = io::stdout();
    let report = found.run(&mut output);
    flush()?;
    note(&report);
    Ok(0)
}

pub fn asm(file: &str) -> Result<u8, String> {
    let text = text(file)?;
    match emd_asm::assemble(&text) {
        Ok(program) => emit(format_program(&program).as_bytes()),
        Err(e) => {
            note(e.render(file, &text).trim_end());
            Ok(1)
        }
    }
}

pub fn disasm(file: &str) -> Result<u8, String> {
    let lines: String = load(file)?.iter().map(|i| format!("{i}\n")).collect();
    emit(lines.as_bytes())
}

pub fn keys(file: Option<&str>) -> Result<u8, String> {
    let typed = match file {
        Some(file) => text(file)?,
        None => {
            let mut typed = String::new();
            io::stdin().read_to_string(&mut typed).map_err(|e| e.to_string())?;
            typed
        }
    };
    emit(emd_tools::keys(&typed).map_err(|e| e.to_string())?.as_bytes())
}

pub fn fmt(file: &str) -> Result<u8, String> {
    emit(emd_tools::fmt(&text(file)?).map_err(|e| format!("{file}: {e}"))?.as_bytes())
}

pub fn to_c(file: &str) -> Result<u8, String> {
    emit(emd_c::to_c(&load(file)?).as_bytes())
}

pub fn check(file: &str) -> Result<u8, String> {
    emit(format!("ok: {} instructions\n", load(file)?.len()).as_bytes())
}

pub fn inspect(file: &str) -> Result<u8, String> {
    emit(emd_tools::inspect(&load(file)?).as_bytes())
}

pub fn explain(file: &str) -> Result<u8, String> {
    emit(emd_tools::explain(&load(file)?).as_bytes())
}

pub fn color(file: &str) -> Result<u8, String> {
    let syms = emd_parser::lex_bytes(&read(file)?).map_err(|e| format!("{file}: {e}"))?;
    emit(emd_tools::color(&syms).as_bytes())
}

pub fn diff(a: &str, b: &str) -> Result<u8, String> {
    emit(emd_tools::diff(&load(a)?, &load(b)?).as_bytes())
}

/// 0 if everything checked is proved, 3 otherwise: not proved is not a bug found.
pub fn analyze(file: &str) -> Result<u8, String> {
    let analysis = emd_analyze::analyze(&load(file)?);
    emit(format!("{analysis}\n").as_bytes())?;
    Ok(if analysis.is_clean() { 0 } else { 3 })
}

pub fn cfg(file: &str) -> Result<u8, String> {
    emit(emd_analyze::cfg(&load(file)?).as_bytes())
}

pub fn doctor(file: &str) -> Result<u8, String> {
    let report = emd_parser::doctor(&read(file)?);
    emit(report.to_string().as_bytes())?;
    Ok(u8::from(!report.is_healthy()))
}

pub fn reduce(file: &str, input: Option<&str>, max_steps: Option<u64>) -> Result<u8, String> {
    let program = load(file)?;
    let input = input.map_or(Ok(Vec::new()), read)?;
    let limit = max_steps.unwrap_or(REDUCE_STEPS);
    let small = emd_tools::reduce(&program, &input, limit)
        .ok_or_else(|| format!("{file}: does not end within {limit} steps, nothing to preserve"))?;
    emit(format_program(&small).as_bytes())?;
    note(&format!("{} instructions down to {}", program.len(), small.len()));
    Ok(0)
}

pub fn verify(file: &str, max_steps: Option<u64>) -> Result<u8, String> {
    let (report, verdict) = emd_tools::verify(&load(file)?, max_steps.unwrap_or(emd_tools::VERIFY_STEPS));
    emit(report.as_bytes())?;
    Ok(match verdict {
        Verdict::Halted => 0,
        Verdict::Faulted => 1,
        Verdict::NoVerdict => 3,
    })
}

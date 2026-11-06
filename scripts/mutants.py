#!/usr/bin/env python3
"""Measures the tests: breaks the code on purpose and expects a test to fail.

usage: mutants.py [group]

Works on a temporary copy, never on the repository. Each mutant is a fixed list of
edits in one group of files, run against the crates that should notice. A test run
that outlives TIMEOUT counts as killed: the mutant made a program hang. Needs
emdref and emdref-rocq built, because the VM group runs the differential tests.
"""

import os
import pathlib
import shutil
import signal
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
TIMEOUT = 300
VM = "crates/emd-vm/src/lib.rs"
SYM = "crates/emd-core/src/sym.rs"
INSTR = "crates/emd-core/src/instr.rs"
LAYOUT = "crates/emd-core/src/source.rs"
PARSER = "crates/emd-parser/src/lib.rs"
LEXER = "crates/emd-asm/src/lexer.rs"
ASM_PARSER = "crates/emd-asm/src/parser.rs"
CODEGEN = "crates/emd-asm/src/codegen.rs"
SOURCE = "crates/emd-tools/src/source.rs"
VIEW = "crates/emd-tools/src/view.rs"
DOCTOR = "crates/emd-parser/src/doctor.rs"
ERROR = "crates/emd-asm/src/error.rs"
MAIN = "crates/emd-cli/src/main.rs"
COMMANDS = "crates/emd-cli/src/commands.rs"
SYSTEM = "crates/emd-cli/src/system.rs"
VERIFY = "crates/emd-tools/src/verify.rs"
DEBUG = "crates/emd-tools/src/debug.rs"
VALUE = "crates/emd-analyze/src/value.rs"
STATE = "crates/emd-analyze/src/state.rs"
TRANSFER = "crates/emd-analyze/src/transfer.rs"
ANALYSIS = "crates/emd-analyze/src/analysis.rs"
CFG = "crates/emd-analyze/src/cfg.rs"
PROFILE = "crates/emd-tools/src/profile.rs"
REDUCE = "crates/emd-tools/src/reduce.rs"
SLOP = "crates/emd-tools/src/slop.rs"
C = "crates/emd-c/src/lib.rs"
WASM = "crates/emd-wasm/src/lib.rs"

TESTS = {
    "vm": ["emd-vm"],
    "core": ["emd-core", "emd-parser"],
    "parser": ["emd-parser", "emd-cli"],
    "asm": ["emd-asm", "emd-cli"],
    "tools": ["emd-tools", "emd-cli"],
    "cli": ["emd-cli"],
    "analysis": ["emd-analyze", "emd-tools"],
    "native": ["emd-cli"],
    "wasm": ["emd-wasm"],
}

# (group, [(file, old, new), ...]). `old` must occur exactly once, or the run stops.
MUTANTS = [
    ("vm", [(VM, "a.checked_sub(b)", "b.checked_sub(a)")]),
    ("vm", [(VM, "Ok(i64::from(a < b))", "Ok(i64::from(a <= b))")]),
    ("vm", [(VM, "Ok(i64::from(a > b))", "Ok(i64::from(a >= b))")]),
    ("vm", [(VM, "Ok(i64::from(a == b))", "Ok(i64::from(a != b))")]),
    ("vm", [(VM, "a.wrapping_rem(b)", "a.wrapping_rem_euclid(b)")]),
    ("vm", [(VM, "a.checked_div(b)", "a.checked_div_euclid(b)")]),
    ("vm", [(VM, "Ok(0) => -1,", "Ok(0) => 0,")]),
    ("vm", [(VM, "let [c, off] = self.top()?;\n                let taken = if instr == Jz { c == 0 } else { c != 0 };", "let [c, off] = self.top()?;\n                let taken = if instr == Jz { c != 0 } else { c == 0 };")]),
    ("vm", [(VM, "t >= self.program.len() as i64", "t > self.program.len() as i64")]),
    ("vm", [(VM, "if t < 0 || t >= self.program.len() as i64 {", "if t >= self.program.len() as i64 {")]),
    ("vm", [(VM, "let a = self.peek(2)?;\n                let next = self.target(1)?;\n                self.push(a)?;",
             "let a = self.peek(1)?;\n                let next = self.target(1)?;\n                self.push(a)?;")]),
    ("vm", [(VM, "unwrap_or(0);\n                self.pop(1);", "unwrap_or(1);\n                self.pop(1);")]),
    ("vm", [(VM, "self.stack.extend([b, a]);", "self.stack.extend([a, b]);")]),
    ("vm", [(VM, "self.stack.push(i64::from(a == 0));", "self.stack.push(i64::from(a != 0));")]),
    ("vm", [(VM, "if addr < 0 {", "if addr < -1 {")]),
    ("vm", [(VM, "let v = self.peek(2)?;\n                let addr = self.address()?;", "let addr = self.address()?;\n                let v = self.peek(2)?;")]),
    ("vm", [(VM, "u8::try_from(v)", "u8::try_from(v & 255)")]),
    ("vm", [(VM, "self.memory.insert(addr, v);", "self.memory.insert(addr, v + 1);")]),
    ("vm", [(VM, "i64::from(n.index())", "i64::from(n.index()) + 1")]),
    ("vm", [(VM, "(self.pc as i64).saturating_add(offset)", "(self.pc as i64 + 1).saturating_add(offset)")]),

    ("core", [(SYM, "'\\u{2012}', // FIGURE DASH", "'\\u{2013}', // FIGURE DASH")]),
    ("core", [(SYM, "'\\u{2013}', // EN DASH", "'\\u{2012}', // EN DASH"), (SYM, "'\\u{2012}', // FIGURE DASH", "'\\u{2013}', // FIGURE DASH")]),
    ("core", [(INSTR, "(2, 0) => Add,", "(2, 0) => Sub,"), (INSTR, "(2, 1) => Sub,", "(2, 1) => Add,"), (INSTR, "Add => (2, 0),", "Add => (2, 1),"), (INSTR, "Sub => (2, 1),", "Sub => (2, 0),")]),
    ("core", [(INSTR, "(4, 3) => Halt,", "(4, 4) => Halt,"), (INSTR, "Halt => (4, 3),", "Halt => (4, 4),")]),
    ("core", [(SYM, "(index < 8).then_some", "(index < 9).then_some")]),

    ("parser", [(PARSER, "if !syms.len().is_multiple_of(2) {", "if false {")]),
    ("parser", [(PARSER, "if ch == '\\n' {", "if ch.is_whitespace() {")]),
    ("parser", [(PARSER, "offset: e.valid_up_to() }", "offset: 0 }")]),
    ("parser", [(PARSER, "Sym::from_char(ch).ok_or(ParseError::Foreign { index, ch })", "Sym::from_char(if ch == '\\u{FE58}' { '\\u{2014}' } else { ch }).ok_or(ParseError::Foreign { index, ch })")]),

    ("asm", [(CODEGEN, "push_magnitude(n / 7, out);", "push_magnitude(n / 7 + 1, out);")]),
    ("asm", [(CODEGEN, "out.extend([lit(7), Instr::Mul]);", "out.extend([lit(6), Instr::Mul]);")]),
    ("asm", [(CODEGEN, "out.push(Instr::Sub);", "out.push(Instr::Add);")]),
    ("asm", [(CODEGEN, "target - (start + slot as i64)", "target - start")]),
    ("asm", [(CODEGEN, "pad(slot - push_len(offset), &mut out);", "")]),
    ("asm", [(CODEGEN, "out.extend([lit(0), Instr::Add]);", "out.extend([lit(1), Instr::Add]);")]),
    ("asm", [(CODEGEN, "if need > slots[jump] {", "if need != slots[jump] {")]),
    ("asm", [(ASM_PARSER, 'self.emit(span, Statement::Instr(instr));\n            }\n            Some(instr @ (Instr::Jmp', 'self.emit(span, Statement::Instr(if instr == Instr::Load { Instr::Store } else { Instr::Load }));\n            }\n            Some(instr @ (Instr::Jmp')]),
    ("asm", [(ASM_PARSER, "if is_mnemonic(name) {", "if false {")]),
    ("asm", [(ASM_PARSER, "Some(located) if located.span.line == instruction.line => {", "Some(located) => {")]),
    ("asm", [(ASM_PARSER, "if self.constants.insert(name, value).is_some() {", "if false {")]),
    ("asm", [(ASM_PARSER, "n.unsigned_abs() > i64::MAX as u128", "false")]),
    ("asm", [(LEXER, "'n' => '\\n',", "'n' => '\\t',")]),
    ("asm", [(LEXER, "if c == ';' {\n                break;", "if c == ';' {\n                cursor.bump();\n                continue;")]),
    ("asm", [(LEXER, "i128::from(u32::from(c))", "i128::from(u32::from(c)) + 1")]),

    ("tools", [(VIEW, "RAINBOW[line % RAINBOW.len()]", "RAINBOW[0]")]),
    ("tools", [(VIEW, "syms.chunks(RAINBOW_WIDTH)", "syms.chunks(RAINBOW_WIDTH * 2)")]),
    ("tools", [(VIEW, "out.extend(chunk.iter().map(|s| s.to_char()));", "out.extend(chunk.iter().rev().map(|s| s.to_char()));")]),
    ("parser", [(DOCTOR, "if ch == '\\r' {", "if false {")]),
    ("parser", [(DOCTOR, "'\\u{FE58}' => \"SMALL EM DASH\",", "")]),
    ("parser", [(DOCTOR, "if bytes.starts_with(b\"\\xEF\\xBB\\xBF\") {", "if false {")]),
    ("parser", [(DOCTOR, "report.histogram[usize::from(s.index())] += 1;", "report.histogram[0] += 1;")]),
    ("parser", [(DOCTOR, "if Instr::decode(f, o).is_none() {", "if false {")]),
    ("tools", [(VIEW, "lcs[i][j + 1] >= lcs[i + 1][j]", "lcs[i][j + 1] > lcs[i + 1][j] + 99")]),
    ("tools", [(VIEW, "out += &line('+', None, Some(j), b[j]);", "out += &line('-', None, Some(j), b[j]);")]),
    ("tools", [(VIEW, '{i:>5}  {}   {f} {o}  {instr}', '{i:>5}  {}   {o} {f}  {instr}')]),
    ("core", [(INSTR, 'Sub => "pop b, pop a, push a - b",', 'Sub => "pop b, pop a, push b - a",')]),
    ("parser", [(DOCTOR, '| \'\\u{200B}\'..=\'\\u{200F}\'', '')]),

    ("cli", [(VERIFY, '("no verdict, step limit reached".to_string(), Verdict::NoVerdict)', '("no verdict, step limit reached".to_string(), Verdict::Halted)')]),
    ("cli", [(COMMANDS, "Verdict::NoVerdict => 3,", "Verdict::NoVerdict => 0,")]),
    ("cli", [(COMMANDS, "Verdict::Faulted => 1,", "Verdict::Faulted => 0,")]),
    ("cli", [(SYSTEM, "Err(e) if e.kind() == io::ErrorKind::BrokenPipe => Ok(false),", "Err(e) if e.kind() == io::ErrorKind::BrokenPipe => Err(e.to_string()),")]),
    ("cli", [(SYSTEM, 'writeln!(io::stderr(), "{line}").is_ok()', '{ eprintln!("{line}"); true }')]),
    ("cli", [(COMMANDS, "if !note(&format!(\"{:>8}  pc={:<5} {:<8} {:?}\", vm.steps, vm.pc, instr, vm.stack)) {\n                return Ok(0);\n            }", "note(&format!(\"{:>8}  pc={:<5} {:<8} {:?}\", vm.steps, vm.pc, instr, vm.stack));")]),
    ("cli", [(COMMANDS, "Ok(u8::from(!report.is_healthy()))", "Ok(u8::from(report.is_healthy()))")]),
    ("cli", [(SYSTEM, "Err(e) if e.kind() != io::ErrorKind::BrokenPipe => Err(e.to_string()),", "Err(e) => panic!(\"{e}\"),")]),
    ("cli", [(MAIN, 'system::note(USAGE.trim_end());\n            Ok(2)', 'system::note(USAGE.trim_end());\n            Ok(0)')]),
    ("cli", [(COMMANDS, 'fn run(file: &str, trace: bool, max_steps: Option<u64>) -> Result<u8, String> {\n    let program = load(file)?;\n    let limits = Limits { max_steps: max_steps.unwrap_or(u64::MAX), ..Limits::default() };', 'fn run(file: &str, trace: bool, max_steps: Option<u64>) -> Result<u8, String> {\n    let program = load(file)?;\n    let limits = Limits { max_steps: u64::MAX, ..Limits::default() };')]),
    ("cli", [(COMMANDS, "emit(format_program(&program).as_bytes())", 'emit(format!("{}\\n", format_program(&program)).as_bytes())')]),
    ("cli", [(COMMANDS, 'let syms = emd_parser::lex_bytes(&read(file)?).map_err(|e| format!("{file}: {e}"))?;', 'let syms: Vec<_> = read(file)?.iter().map(|_| emd_core::Sym::ALL[0]).collect();')]),
    ("cli", [(SYSTEM, "io::stdout().flush()?;\n", "")]),
    ("cli", [(MAIN, "self.max_steps.is_some() && !limited", "false")]),
    ("cli", [(MAIN, 'self.input.is_some() && !matches!(command, "debug" | "reduce")', "false")]),
    ("cli", [(MAIN, 'self.machine && command != "debug"', "false")]),
    # The source layout.
    ("parser", [(PARSER, "if column > LINE_MAX {", "if column > LINE_MAX + 1 {")]),
    ("parser", [(PARSER, "            column = 0;\n            continue;", "            continue;")]),
    ("parser", [(PARSER, "            line += 1;", "            line += 2;")]),
    ("core", [(LAYOUT, "if column == LINE_MAX {", "if column == LINE_MAX + 1 {")]),
    ("core", [(LAYOUT, "    if column > 0 {\n        out.push", "    if column > 1 {\n        out.push")]),
    ("parser", [(DOCTOR, "if length > emd_core::LINE_MAX {", "if length > emd_core::LINE_MAX + 1 {")]),
    ("parser", [(DOCTOR, "let dashes_and_others = text.chars().filter(|&c| c != '\\n').count();", "let dashes_and_others = text.chars().count();")]),
    ("tools", [(SOURCE, "None if c.is_whitespace() => {}", "None if c == ' ' => {}")]),
    # ROT, CALL, RET.
    ("core", [(INSTR, "(1, 4) => Rot,", "(1, 5) => Rot,")]),
    ("core", [(INSTR, "Call => (4, 4),", "Call => (4, 6),")]),
    ("vm", [(VM, "self.stack.extend([b, c, a]);", "self.stack.extend([c, b, a]);")]),
    ("vm", [(VM, "self.stack.push(self.pc as i64 + 1);", "self.stack.push(self.pc as i64);")]),
    ("vm", [(VM, ".filter(|&a| a < self.program.len())", ".filter(|&a| a <= self.program.len())")]),
    ("asm", [(ASM_PARSER, 'Instr::Jmp | Instr::Jz | Instr::Jnz | Instr::Call', 'Instr::Jmp | Instr::Jz | Instr::Jnz')]),
    ("asm", [(ERROR, '"^".repeat(length)', '"^".repeat(1)')]),
    ("asm", [(ERROR, ".take(column - 1)", ".take(column)")]),
    ("asm", [(ERROR, "if c.is_control() && c != '\\t' {", "if false {")]),
    ("asm", [(LEXER, "column: column + 1,", "column: column + 2,")]),
    ("asm", [(LEXER, "(self.column - column).max(1)", "1")]),
    ("asm", [(CODEGEN, "len += if n.is_multiple_of(7) { 2 } else { 4 };", "len += 4;")]),
    ("asm", [(ASM_PARSER, "self.emit(target_span, Statement::Jump(instr, target));", "self.emit(span, Statement::Jump(instr, target));")]),
    ("asm", [(LEXER, 'format!("unexpected character `{}`", c.escape_debug())', 'format!("unexpected character `{c}`")')]),
    # The debugger: going back must restore everything.
    ("analysis", [(DEBUG, "self.replay_to(self.vm.steps.saturating_sub(count));", "self.replay_to(self.vm.steps);")]),
    ("analysis", [(DEBUG, "        self.consumed = 0;\n", "")]),
    ("analysis", [(DEBUG, "        self.output.clear();\n", "")]),
    ("analysis", [(DEBUG, "if write.is_some() && self.running() {", "if write.is_some() && false {")]),
    ("analysis", [(DEBUG, "found = Some(self.vm.steps);", "found = found.or(Some(self.vm.steps));")]),
    # The analyzer: each of these makes it claim too much.
    ("analysis", [(TRANSFER, "Val::Known(set) => (set.contains(&0), set.iter().any(|&c| c != 0)),", "Val::Known(_) => (true, false),")]),
    ("analysis", [(TRANSFER, "if on_zero { (can_zero, can_other) } else { (can_other, can_zero) }", "if on_zero { (can_other, can_zero) } else { (can_zero, can_other) }")]),
    ("analysis", [(TRANSFER, "Rot => flow.fall(&[ops[1].clone(), ops[2].clone(), ops[0].clone()]),", "Rot => flow.fall(&[ops[0].clone(), ops[1].clone(), ops[2].clone()]),")]),
    ("analysis", [(TRANSFER, "Cell::plain(Val::one(pc as i64 + 1))", "Cell::plain(Val::one(pc as i64))")]),
    ("analysis", [(TRANSFER, "|v| (0..=255).contains(&v))", "|v| (0..=256).contains(&v))")]),
    ("analysis", [(ANALYSIS, "certain: certain && count == variants.len()", "certain")]),
    ("analysis", [(VALUE, "(Val::Known(a), Val::Known(b)) => Val::of(a.union(b).copied().collect()),", "(Val::Known(a), Val::Known(_)) => Val::Known(a.clone()),")]),
    ("analysis", [(STATE, "                self.by_depth.insert(frame.stack.len(), frame);\n", "")]),
    # Relations and memory: what makes it claim a value it should not.
    ("analysis", [(STATE, "self.narrow(sym, if zero { cmp.negated() } else { cmp }, b)", "self.narrow(sym, if zero { cmp } else { cmp.negated() }, b)")]),
    ("analysis", [(TRANSFER, "let zero = taken_way == on_zero;", "let zero = taken_way != on_zero;")]),
    ("analysis", [(STATE, "            if cell.rel.is_some_and(|r| r.sym() == sym) {\n                cell.rel = None;\n            }\n", "")]),
    ("analysis", [(TRANSFER, "off: off.checked_sub(k)?", "off: off.checked_add(k)?")]),
    ("analysis", [(TRANSFER, "(Lt, Some(k), _) => offset(b).and_then(|(sym, off)| test(sym, off, Cmp::Gt, k)),", "(Lt, Some(k), _) => offset(b).and_then(|(sym, off)| test(sym, off, Cmp::Lt, k)),")]),
    ("analysis", [(TRANSFER, "Some(Rel::Test { sym, off, cmp, k }) => Some(Rel::Test { sym, off, cmp: cmp.negated(), k }),", "Some(Rel::Test { sym, off, cmp, k }) => Some(Rel::Test { sym, off, cmp, k }),")]),
    ("analysis", [(TRANSFER, "            f.rest = f.rest.join(&value.val);\n", "")]),
    ("analysis", [(TRANSFER, "                *cell = cell.join(&written);\n", "")]),
    ("analysis", [(TRANSFER, "                f.mem.insert(a, old.join(&written));\n", "                f.mem.insert(a, written.clone());\n")]),
    ("analysis", [(STATE, "rel: if self.rel == other.rel { self.rel } else { None } }", "rel: self.rel }")]),
    ("analysis", [(TRANSFER, "            if let Some(cell) = between.as_mut().filter(|c| c.rel.is_some_and(|r| r.sym() == self.pc)) {\n                cell.rel = None;\n            }\n", "")]),
    ("analysis", [(VALUE, "Cmp::Lt => hi = hi.min(b.checked_sub(1)?),", "Cmp::Lt => hi = hi.min(b),")]),
    ("analysis", [(VALUE, "Cmp::Ge => lo = lo.max(b),", "Cmp::Ge => lo = lo.max(b.saturating_add(1)),")]),
    ("analysis", [(VALUE, "if lo == b {\n                    lo = lo.saturating_add(1);", "if lo <= b {\n                    lo = lo.saturating_add(1);")]),
    ("analysis", [(TRANSFER, "if al >= 0 { Val::range(0, top) } else { Val::range(-top, top) }", "Val::range(0, top)")]),
    ("analysis", [(TRANSFER, "for (_, cell) in f.mem.range_mut(lo.max(0)..=hi.max(0)) {", "for (_, cell) in f.mem.range_mut(lo.max(0)..=lo.max(0)) {")]),
    ("analysis", [(TRANSFER, "Lt if al >= bh => verdict(false),", "Lt if al >= bl => verdict(false),")]),
    ("analysis", [(TRANSFER, "(Gt, Some(k), _) => offset(b).and_then(|(sym, off)| test(sym, off, Cmp::Lt, k)),", "(Gt, Some(k), _) => offset(b).and_then(|(sym, off)| test(sym, off, Cmp::Gt, k)),")]),
    # The other tools.
    ("analysis", [(REDUCE, "if outcome(&candidate, input, max_steps).as_ref() == Some(&goal) {", "if candidate.len() < 2 || outcome(&candidate, input, max_steps).as_ref() == Some(&goal) {")]),
    ("analysis", [(PROFILE, "if vm.steps > steps {", "if true {")]),
    ("analysis", [(SLOP, "skipped_pairs: pairs.len() - program.len(),", "skipped_pairs: 0,")]),
    ("native", [(C, "st[sp - 2] == 0 ? st[sp - 1] : 1", "st[sp - 2] != 0 ? st[sp - 1] : 1")]),
    ("native", [(C, "b == -1 ? 0 : a % b", "a % b")]),
    ("native", [(C, "next = target(0, st[sp - 1]); sp--;", "next = target(pc, st[sp - 1]); sp--;")]),
    ("native", [(C, "st[sp - 1] = pc + 1;", "st[sp - 1] = pc;")]),
    ("native", [(C, 'if (putchar((int)st[--sp]) == EOF) fault("i/o error");', "putchar((int)st[--sp]);")]),
    ("native", [(C, ' if (c == EOF && ferror(stdin)) fault("i/o error");', "")]),
    ("native", [(C, "{ flush_out(); int c", "{ int c")]),
    ("native", [(C, 'Halt => "flush_out(); return 0;"', 'Halt => "return 0;"')]),
    ("wasm", [(WASM, "if self.0.len() + buf.len() > MAX_OUTPUT {", "if false {")]),
]


def run_tests(command, cwd, env, timeout=TIMEOUT):
    """The exit code, or None on a timeout. Kills the whole tree: cargo leaves test binaries."""
    process = subprocess.Popen(command, cwd=cwd, env=env, text=True, start_new_session=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        _, stderr = process.communicate(timeout=timeout)
        return process.returncode, stderr
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()
        return None, ""


def main():
    env = {**os.environ, "EMD_REQUIRE_LEAN": "1", "EMD_REQUIRE_ROCQ": "1"}
    groups = sys.argv[1:] or list(TESTS)
    chosen = [m for m in MUTANTS if m[0] in groups]
    survived = []
    with tempfile.TemporaryDirectory(prefix="emd-mutants-") as tmp:
        work = pathlib.Path(tmp) / "repo"
        shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns("target", ".git", "__pycache__"))
        # On a red baseline every mutant would count as killed.
        baseline = ["cargo", "test", "--no-fail-fast", "-q"]
        for crate in sorted({crate for group, _ in chosen for crate in TESTS[group]}):
            baseline += ["-p", crate]
        baseline += ["--", "--skip", "the_analysis_is_the_proved_mirror"]
        code, stderr = run_tests(baseline, work, env, timeout=3000)
        if code != 0:
            sys.exit(f"tests fail before any mutation (exit {code}):\n{stderr[-2000:]}")
        for number, (group, edits) in enumerate(chosen):
            originals = {}
            for file, old, new in edits:
                path = work / file
                originals.setdefault(path, path.read_text(encoding="utf-8"))
                text = path.read_text(encoding="utf-8")
                if text.count(old) != 1:
                    sys.exit(f"mutant {number}: {old!r} occurs {text.count(old)} times in {file}")
                path.write_text(text.replace(old, new), encoding="utf-8")
            command = ["cargo", "test", "--no-fail-fast", "-q"]
            for crate in TESTS[group]:
                command += ["-p", crate]
            # Takes longer than TIMEOUT, and a timeout would count as a kill.
            command += ["--", "--skip", "the_analysis_is_the_proved_mirror"]
            code, stderr = run_tests(command, work, env)
            if code is None:
                # Once more: a busy machine can time out too, and a timeout counts as a kill.
                code, stderr = run_tests(command, work, env)
            if code is None:
                verdict = "killed-by-timeout"
            elif "could not compile" in stderr:
                verdict = "INVALID"
            else:
                verdict = "killed" if code else "SURVIVED"
            print(f"{number:>3} {group:<7} {verdict:<18} {edits[0][2][:60]!r}", flush=True)
            if not verdict.startswith("killed"):
                survived.append((number, group, verdict, edits[0][2][:60]))
            for path, text in originals.items():
                path.write_text(text, encoding="utf-8")
    print(f"\n{len(chosen) - len(survived)}/{len(chosen)} killed")
    for item in survived:
        print("  not killed:", *item)
    sys.exit(1 if survived else 0)


if __name__ == "__main__":
    main()

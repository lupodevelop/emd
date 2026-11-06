#!/usr/bin/env python3
"""Measures the Kani specification: injects a bug in the VM and expects its harness to fail.

usage: kani-bugs.py

Works on a temporary copy, never on the repository. A harness that passes on a broken VM would
mean the specification does not constrain that behavior. A CBMC run that fails without a failed
property counts as no verdict, not as a detection.
"""

import pathlib
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
VM = "crates/emd-vm/src/lib.rs"

# (harness, old, new). `old` must occur exactly once, or the run stops.
BUGS = [
    ("rot::depth3", "self.stack.extend([b, c, a]);", "self.stack.extend([c, a, b]);"),
    ("call::depth1", "self.stack.push(self.pc as i64 + 1);", "self.stack.push(self.pc as i64);"),
    ("ret::depth1", ".filter(|&a| a < self.program.len())", ".filter(|&a| a <= self.program.len())"),
    ("not::depth1", "self.stack.push(i64::from(a == 0));", "self.stack.push(i64::from(a != 0));"),
    ("store::depth2", "self.memory.insert(addr, v);", "self.memory.insert(addr, addr);"),
    ("read::depth0", "Ok(0) => -1,", "Ok(0) => 0,"),
    ("write::depth1", "u8::try_from(v).map_err(|_| Fault::InvalidByte(v))?", "v as u8"),
    ("rem::depth2", "_ => Ok(a.wrapping_rem(b)),", "_ => Ok(a.wrapping_rem(b).wrapping_abs()),"),
    # A fault must leave the state as it was.
    ("drop_top::depth1", "self.peek(1)?;\n                let next = self.target(1)?;\n                self.pop(1);\n                next\n            }\n            Swap",
     "self.peek(1)?;\n                self.pop(1);\n                let next = self.target(1)?;\n                next\n            }\n            Swap"),
]


def main():
    missed = []
    with tempfile.TemporaryDirectory(prefix="emd-kani-bugs-") as tmp:
        work = pathlib.Path(tmp) / "repo"
        work.mkdir()
        shutil.copytree(ROOT / "crates", work / "crates", ignore=shutil.ignore_patterns("target"))
        shutil.copy(ROOT / "Cargo.toml", work)
        shutil.copy(ROOT / "Cargo.lock", work)
        path = work / VM
        original = path.read_text(encoding="utf-8")
        for harness, old, new in BUGS:
            if original.count(old) != 1:
                sys.exit(f"{harness}: {old!r} occurs {original.count(old)} times")
            path.write_text(original.replace(old, new), encoding="utf-8")
            run = subprocess.run(["cargo", "kani", "-p", "emd-vm", "--harness", f"verification::{harness}"],
                                 cwd=work, text=True, capture_output=True, check=False)
            found = run.returncode != 0 and "Status: FAILURE" in run.stdout
            print(f"{harness:<18} {'found' if found else 'MISSED'}  {new.splitlines()[0][:60]}", flush=True)
            if not found:
                missed.append(harness)
        path.write_text(original, encoding="utf-8")
    print(f"\n{len(BUGS) - len(missed)}/{len(BUGS)} found")
    sys.exit(1 if missed else 0)


if __name__ == "__main__":
    main()

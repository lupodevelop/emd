#!/usr/bin/env python3
"""Lists the axioms behind every theorem in both provers, and fails on anything unexpected.

usage: axioms.py        (after `lake build` and formal/rocq/build.sh)
"""

import pathlib
import re
import subprocess
import sys
import tempfile
from collections import Counter

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEAN = [("Emd.lean", "Emd."), ("Emd/Universal.lean", "Emd."), ("Emd/Lowering.lean", "Emd."),
        ("Emd/Properties.lean", "Emd."), ("Emd/Turing.lean", "Emd.Turing."), ("Emd/Source.lean", "Emd."),
        ("Emd/Bounded.lean", "Emd."), ("Emd/Analyzer.lean", "Emd.Analyzer.")]
ROCQ = ["Emd", "Props", "Source", "Turing"]
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def lean(tmp):
    lines = ["import " + file[:-5].replace("/", ".") for file, _ in LEAN]
    for file, namespace in LEAN:
        for name in re.findall(r"^theorem (\S+)", (ROOT / "formal/lean" / file).read_text(encoding="utf-8"), re.M):
            lines.append(f"#print axioms {name.removeprefix('_root_.') if name.startswith('_root_.') else namespace + name}")
    source = tmp / "Ax.lean"
    source.write_text("\n".join(lines) + "\n", encoding="utf-8")
    out = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT / "formal/lean", text=True, capture_output=True, check=False)
    text = out.stdout + out.stderr
    answered = len(re.findall(r"depends on axioms|does not depend on any axioms", text))
    used = Counter(a.strip() for group in re.findall(r"depends on axioms: \[([^]]*)\]", text) for a in group.split(","))
    print(f"Lean: {answered} of {len(lines) - len(LEAN)} theorems, {dict(used)}, {text.count('does not depend')} with none")
    return answered == len(lines) - len(LEAN) and "error" not in text and set(used) <= ALLOWED


def rocq(tmp):
    lines = ["From EmdFormal Require Import " + " ".join(ROCQ) + "."]
    for module in ROCQ:
        for name in re.findall(r"^(?:Theorem|Lemma) (\S+)", (ROOT / f"formal/rocq/{module}.v").read_text(encoding="utf-8"), re.M):
            lines.append(f"Print Assumptions {module}.{name}.")
    source = tmp / "Ax.v"
    source.write_text("\n".join(lines) + "\n", encoding="utf-8")
    out = subprocess.run(["rocq", "compile", "-R", str(ROOT / "formal/rocq"), "EmdFormal", str(source)],
                         text=True, capture_output=True, check=False)
    closed = (out.stdout + out.stderr).count("Closed under the global context")
    print(f"Rocq: {closed} of {len(lines) - 1} closed under the global context")
    return closed == len(lines) - 1


def main():
    with tempfile.TemporaryDirectory(prefix="emd-axioms-") as tmp:
        good = [lean(pathlib.Path(tmp)), rocq(pathlib.Path(tmp))]
    sys.exit(0 if all(good) else 1)


if __name__ == "__main__":
    main()

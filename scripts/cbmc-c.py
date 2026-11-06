#!/usr/bin/env python3
"""CBMC on the C that `emd c` writes: no undefined behavior, for every stack value.

Each instruction is compiled alone, followed by HALT, and run from a stack of 0 to 3 values
that CBMC leaves free over all of int64_t, with free input. A few pairs cover memory that
already holds a cell, starting from a table of 2 slots so that the second STORE grows it. Unsigned arithmetic wraps by definition, and the hash relies on it,
so only behavior C leaves undefined is checked. CBMC checks every path to the end, loops included, so a success is
a proof for that program, not a bounded search.

    python3 scripts/cbmc-c.py          # needs `emd` (or EMD_BIN) and Kani's cbmc
    python3 scripts/cbmc-c.py JMP RET  # only these programs
"""
import glob
import os
import subprocess
import sys
import tempfile

EMD = os.environ.get("EMD_BIN", "emd")
CBMC = os.environ.get("CBMC") or (sorted(glob.glob(os.path.expanduser("~/.kani/kani-*/bin/cbmc"))) or ["cbmc"])[-1]
CHECKS = [
    "--bounds-check", "--pointer-check", "--div-by-zero-check", "--signed-overflow-check",
    "--undefined-shift-check", "--pointer-overflow-check",
    "--unwind", "70", "--unwinding-assertions", "--object-bits", "16",
]
SINGLE = [f"PUSH {n}" for n in range(8)] + [
    "DUP", "DROP", "SWAP", "OVER", "ROT", "ADD", "SUB", "MUL", "DIV", "MOD", "LOAD", "STORE",
    "JMP", "JZ", "JNZ", "CALL", "RET", "READ", "WRITE", "EQ", "LT", "GT", "NOT",
]
PAIRS = ["STORE STORE", "STORE LOAD", "READ WRITE"]

# The generated program's main runs from a stack CBMC chooses.
HARNESS = """
#define main emd_main
#include "program.c"
#undef main
int64_t nondet_int64(void);
size_t nondet_size(void);
int main(void) {
  size_t depth = nondet_size();
  __CPROVER_assume(depth <= 3);
  st_cap = 4;
  st = malloc(st_cap * sizeof *st);
  __CPROVER_assume(st != NULL);  /* the starting stack; the program's own allocations stay checked */
  for (size_t i = 0; i < depth; i++) st[i] = nondet_int64();
  sp = depth;
  SEED
  return emd_main();
}
"""


def check(text, work):
    asm, emd, c, harness = (os.path.join(work, n) for n in ("p.asm", "p.emd", "program.c", "harness.c"))
    with open(asm, "w") as f:
        f.write(text + " HALT\n")
    with open(emd, "wb") as f:
        f.write(subprocess.run([EMD, "asm", asm], capture_output=True, check=True).stdout)
    with open(c, "wb") as f:
        f.write(subprocess.run([EMD, "c", emd], capture_output=True, check=True).stdout)
    with open(harness, "w") as f:
        # Pairs start from a 2-slot table: the second STORE then grows and rehashes it, the code
        # a 64-slot start reaches only after 32 cells, too many paths for CBMC.
        seed = "cell_cap = 2; cells = calloc(2, sizeof *cells); __CPROVER_assume(cells != NULL);"
        f.write(HARNESS.replace("SEED", seed if " " in text else ""))
    done = subprocess.run([CBMC, harness, *CHECKS], capture_output=True, text=True, cwd=work)
    return "VERIFICATION SUCCESSFUL" in done.stdout, done.stdout + done.stderr


def main():
    failed = 0
    with tempfile.TemporaryDirectory() as work:
        chosen = [t for t in SINGLE + PAIRS if not sys.argv[1:] or t in sys.argv[1:]]
        for text in chosen:
            ok, out = check(text, work)
            print(f"{'ok  ' if ok else 'FAIL'} {text}", flush=True)
            if not ok:
                failed += 1
                print("\n".join(l for l in out.splitlines() if "FAILURE" in l or "error" in l.lower() or "too many" in l)[:2000])
    total = len(chosen)
    print(f"\n{total - failed}/{total} programs free of undefined behavior")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

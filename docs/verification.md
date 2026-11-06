# Verification

Formal guarantees apply to the Lean and Rocq models. The Rust implementation is
checked with bounded model checking, differential tests and conformance tests.

## Four kinds of evidence

From strongest to weakest:

- **Proved**: a machine-checked theorem about a model, for all inputs. It says nothing directly about the Rust.
- **Bounded**: Kani checks the real Rust, and CBMC the generated C, for all inputs within stated limits.
- **Compared**: the real Rust runs against another implementation on many cases.
- **Tested**: the real Rust runs on chosen cases with known answers.

| Part | Proved | Kani or CBMC | Compared |
| --- | --- | --- | --- |
| Alphabet and encoding | Lean and Rocq | Kani 3/3, every value | In every comparison below |
| Decoder and layout | Lean and Rocq | Kani 1/1, on `decode` only | 648 sources in 3 decoders |
| Semantics | Lean and Rocq | Through every VM step | Both models against the Rust |
| Universality | Lean and Rocq | A property of the language, no code | Shown by proof |
| VM | A 64-bit model, Lean only | Kani 127/127, one step at a time | 39237 runs against both models |
| Compiler | A copy of its core, Lean only | Kani 5/5: integer synthesis for every accepted literal, jump layout up to 4 items | 1207 programs against that copy, 5148 against a source interpreter |
| Analyzer | A copy of its core, Lean only | No harness | All 33825 programs of up to 3 instructions on 4 inputs; 1607 programs against the model, 9000 against the VM |
| Compiler in emd | No proof | Runs on the VM, which Kani checks | 10408 texts against the Rust compiler, itself included; also run in the Lean and Rocq interpreters |
| C backend | No model of C | CBMC 34/34: no undefined behavior in any instruction | Against the VM, under UBSan |
| Debugger and other tools | No proof | No harness | Tests only |

In total: 413 Lean theorems and 146 Rocq theorems, helper lemmas included, 136 Kani harnesses and 34 CBMC programs.

## Proved

Neither model contains `sorry`, `admit`, `Admitted`, a declared axiom or `native_decide`. `scripts/axioms.py` asks both provers about every theorem. Lean reports only `propext`, `Quot.sound` and `Classical.choice`, its standard axioms. Rocq reports "Closed under the global context" for all of them.

Proved in both Lean and Rocq:

- **Encoding.** Decoding undoes encoding, and two programs never share a source.
- **Layout.** A line break changes nothing, wherever it falls. A long line, a carriage return or any foreign character rejects the whole source.
- **Runs.** The same program and input always give the same result. A run can't both halt and fault. Each instruction has its stated effect on the stack. A `CALL` to a `RET` comes back.
- **Universality.** A compiled Turing machine halts exactly when the machine does, never faults and leaves the final tape in memory. It uses 11 of the 32 instructions. Eleven is enough, but nobody proved it's the minimum.

Proved in Lean only:

- **The 64-bit machine.** A model written from the Rust, with its limits and its order of checks. It does what the unbounded model does, except for its own overflow and limit faults, which fire only when they should.
- **The compiler.** A copy of `generate` from `crates/emd-asm/src/codegen.rs`. Compiled code halts, faults or runs forever exactly when the source does, with the same stack, memory and output. This excludes raw jumps and any `RET` that leaves its statement.
- **The analyzer.** A copy of its core. A result that passes `checkResult` describes every state a run can reach, so a fault the model can raise is always reported. The search that finds the result isn't proved, only its answer.

Theorem names are in [`formal/`](https://github.com/lupodevelop/emd/tree/main/formal).

## Kani and CBMC

Kani checks the real Rust for every input within the limits below, and nothing beyond them.

- `emd-core`, 3/3: all symbols, all pairs and all `char` values encode and decode back.
- `emd-parser`, 1/1: `decode` on any code point doesn't panic and keeps its symbols.
- `emd-vm`, 127/127: one step does exactly what a written specification says, faults included.

The VM harnesses cover every instruction with up to 3 values of any `i64` on the stack, a program of 1 or 2 instructions, and at most 1 input byte. Some are narrower, because a wider run doesn't finish:

- `DIV` and `MOD` take `i16` values, plus `i64::MIN` and `i64::MAX` divided by -2 to 3.
- The determinism harness takes `i8` values for `MUL`, `DIV` and `MOD`.
- Memory is empty, except for one existing cell in two `LOAD` harnesses. `STORE` over an existing cell isn't covered.
- Input and output never fail, so `Fault::Io` isn't reached.

To check the specification isn't empty, `scripts/kani-bugs.py` puts 9 bugs in a copy of the VM. Kani has to catch each one.

`emd-asm`, 5/5, on how the compiler builds integers and lays out jumps:

- Every value below 8 is one literal.
- For every magnitude from 8 to `i64::MAX`, the instructions after those for `n / 7` leave exactly `n`, with no overflow on the way. With the case above, this covers every value by induction on its digits in base 7. The parser rejects `i64::MIN`.
- A negative value is 0, its magnitude, then `SUB`, which can't overflow.
- `push_len` follows the same recurrence, for values below 2^24. On all of `i64` the solver doesn't finish; unit tests check every power of 7 instead.
- Up to 4 items of up to 20 instructions with 2 jumps: every jump slot holds its offset and the addresses add up.

One harness over the whole of `push_int` doesn't finish in 40 minutes, hence the split. That the code really is "the instructions for `n / 7`, then one digit" is read from `push_magnitude`. Tests back it: the same bytes as the Lean model around every power of 7, and VM runs on 404000 values.

`scripts/cbmc-c.py` runs CBMC on the C that `emd c` writes. Each of the other 31 instructions is compiled alone, followed by `HALT`, then run from a stack of 0 to 3 values of any `int64_t`, with any input. CBMC finds no out-of-bounds access, bad pointer, division by zero, signed overflow or bad shift on any path. Three pairs, `STORE STORE`, `STORE LOAD` and `READ WRITE`, start from a memory table of 2 slots so the second store grows it; from the real 64 slots there are too many paths. Long programs rest on the comparison with the VM.

## Compared

There were no disagreements in any comparison below.

- **VM against both models.** 2371 sampled cases and all 36866 programs of up to three instructions, each with a budget of 5000 steps. None of them reach 64-bit overflow or a resource limit, which only the Lean machine and Kani cover. 4 sampled cases go beyond what the models can take and aren't compared.
- **Three decoders.** Rust, Lean and Rocq read 648 raw sources: every line break position, invalid UTF-8, look-alikes and damaged layouts. All three accept the same 458 and reject the same 190.
- **Compiler against its proved copy.** The same bytes on the examples and 1200 random programs.
- **Compiler against the source.** An interpreter of the source language and the VM running the compiled code give the same result on 5148 random programs. 20000 random texts compile or report an error, and never panic.
- **The compiler in emd against the Rust one.** `compiler/asm.emd` runs on the VM. On the examples, on its own source, on 400 random programs and on 10000 random texts, valid or not, it gives the same bytes, or an error on the same line.
- **Analyzer against its proved copy.** The same answers on the examples and 1600 random programs.
- **Analyzer against the VM.** On 9000 random programs, and on every program of up to 3 instructions (33825) with 4 inputs, every state a run reaches lies inside what the analyzer claimed, and every fault was reported.
- **C backend against the VM.** The examples and 150 random programs, with the undefined behavior sanitizer on. A failing stdin or stdout faults in both.

## Tests, fuzzing and planted bugs

180 Rust tests, including exact runs of every example. They cover 99.83% of lines and every function, excluding the test files. By crate: `emd-analyze`, `emd-c`, `emd-cli`, `emd-core`, `emd-tools` and `emd-wasm` 100%, `emd-vm` 99.52%, `emd-asm` 99.48%, `emd-parser` 99.27%. Random tests use fixed seeds, so a failure repeats.

Four fuzz targets ran 120 seconds each on the final code: `parse_bytes` 47343268 executions, `compile` 4112298, `vm` 1417280, `doctor` 638641. No crash in the product.

`scripts/mutants.py` plants 138 hand-written bugs, one at a time. The tests catch all 138, three of them by timeout because the bug makes a program hang. The list is hand-picked, so this says the tests catch these bugs, not all bugs. `cargo-mutants` was not run.

The analyzer proves every property it checks on all seven examples, for any input. For `brainfuck` that includes any Brainfuck program.

## Not verified

- **The Rust against the models.** No proof connects them. The 64-bit machine and the copies of the compiler and analyzer were read from the Rust. The two copies are tied to it only by the comparisons above, and must be edited along with it.
- **The rest of the compiler.** The lexer, the parser, `CONST`, label resolution and error positions are outside the theorems, and so is 64-bit overflow in compiled code. Nothing proves the layout loop ends in general, only that its answer is right if it does; Kani sees it end for up to 4 items.
- **The rest of the analyzer.** Nothing claims it reports every overflow. Resource limits and termination aren't checked, and the `certain` flag isn't proved.
- **Lean and Rocq against each other.** No proof relates them, and the 64-bit machine, compiler and analyzer are in Lean only. Both models come from the same author and the same specification, so a mistake in the specification would pass both.
- **`parse` under Kani.** Parsing arbitrary byte input is covered by tests, decoder comparisons and fuzzing, not by bounded verification.
- **The tools.** The debugger, the C backend beyond single instructions, the reducer, profiler, `doctor` and Neovim plugin rest on tests. `emd verify` only decodes and does a bounded run, so it proves nothing about a program it doesn't see finish.
- **The browser runtime.** The website uses the Rust parser and VM compiled to WebAssembly. It has no separate formal proof.
- **What all this trusts.** The Lean and Rocq kernels, the Lean compiler, Rocq extraction and OCaml, the hand-written readers in `RefMain.lean` and `main.ml`, Kani with CBMC, and `rustc`.

## Run it

```
scripts/verify.sh
python3 scripts/mutants.py vm
python3 scripts/axioms.py
cargo kani -p emd-vm --harness verification::add::depth2
```


The full verification script needs Rust through `rustup` (stable and nightly),
the `wasm32-unknown-unknown` target on stable, `cargo-fuzz`, Kani, Python 3,
Neovim, Lean 4.35.0 through `elan`, Rocq 9.3 with OCaml and `ocamlfind`,
and a C compiler with UBSan. The CBMC checks use the binary bundled with Kani.

# Formal models

Lean: `lean/Emd.lean`. Rocq: `rocq/Emd.v`.
[Verification scope](../docs/verification.md).

```
(cd formal/lean && lake build)     # the Lean proofs and the interpreters built from them
formal/rocq/build.sh               # the Rocq proofs and the interpreter extracted from them
python3 scripts/axioms.py          # asks both provers what each theorem depends on
```

Lean's version is in `lean/lean-toolchain`. Rocq is 9.3, with OCaml and `ocamlfind`.

## Theorems by topic

**Encoding and determinism**

- Lean: `ofCodePoint_codePoint`, `decode_encode`, `encode_decode`, `decodeProgram_encodeProgram`, `encodeProgram_injective`, `step_det`, `example1_halts_with_3`
- Rocq: `of_code_point_code_point`, `decode_encode`, `encode_decode`, `decode_program_encode_program`, `encode_program_injective`, `step_det`, `example1_halts_with_3`

**Whole runs and step invariants**

- Lean: `encodeProgram_decodeProgram`, `assigned_count`, `codePoint_injective`, `run_halt_unique`, `run_fault_unique`, `run_halt_fault_exclusive`, `run_observable`, `step_pc_lt`, `step_output_prefix`, `step_input_suffix`, `step_mem_frame`, `step_store_mem`, `stack_effect`, `call_ret_returns`
- Rocq: `encode_program_decode_program`, `assigned_count`, `code_point_injective`, `run_halt_unique`, `run_fault_unique`, `run_halt_fault_exclusive`, `run_observable`, `step_pc_lt`, `step_output_prefix`, `step_input_suffix`, `step_mem_frame`, `step_store_mem`, `stack_effect`, `call_ret_returns`

**Layout**

- Lean: `line_break_irrelevant`, `decodeSource_insert`, `trailing_newline_irrelevant`, `overlong_rejected`, `foreign_rejected`, `carriage_return_rejected`, `decodeSource_format`, `decodeSource_one_line`
- Rocq: `line_break_irrelevant`, `decode_source_insert`, `trailing_newline_irrelevant`, `overlong_rejected`, `foreign_rejected`, `carriage_return_rejected`, `decode_source_format`, `decode_source_one_line`

**Turing universality**

- Lean: `simulates_halting`, `halts_iff`, `halts_iff_init`, `halts_iff_blank`, `compiled_never_faults`, `final_tape_of_machine_halts`, `machine_halts_of_final`, `compile_uses`
- Rocq: `simulates_halting`, `halts_iff`, `halts_iff_init`, `halts_iff_blank`, `compiled_never_faults`, `final_tape_of_machine_halts`, `machine_halts_of_final`, `compile_uses`

**Counter machines** (`lean/Emd/Universal.lean`)

- Lean: `sim_step`, `diverges_of_not_halts`

**The 64-bit machine** (`lean/Emd/Bounded.lean`)

- Lean: `bexec_ref`, `bstep_ref`, `bexec_overflow`, `bexec_stackLimit`, `bexec_memoryLimit`, `bstep_inv`, `brun_inv`, `bstep_complete`, `brun_complete`, `brun_ref`, `brun_limit_prefix`, `bounded_init`

**The compiler** (`lean/Emd/Lowering.lean`)

- Lean: `pushInt_correct`, `padding_correct`, `lowered_call`, `lower_correct`, `layoutLoop_ok`, `layoutLoop_erase`, `lower_fault`, `lower_run_fault`, `lower_diverges`, `src_trichotomy`, `lower_halts_source`, `lower_faults_source`, `lower_halts_iff`, `lower_faults_iff`, `lower_diverges_iff`, `generate_correct`

**The analyzer** (`lean/Emd/Analyzer.lean`)

- Lean: `transfer_next`, `transfer_fault`, `transfer_halts`, `check_step`, `check_invariant`, `reachable_covered`, `fault_reported`, `no_halt_reported`

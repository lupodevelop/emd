#!/bin/sh
# Build proof models and run Rust, scorer, editor, fuzzing, Kani, CBMC and mutation checks.
# Stops at the first failure; browser, terminal and coverage checks are separate.
set -eu
cd "$(dirname "$0")/.."

(cd formal/lean && lake build)
formal/rocq/build.sh
python3 scripts/axioms.py
cargo fmt --all --check
cargo clippy --workspace --all-targets -- -D warnings
EMD_REQUIRE_LEAN=1 EMD_REQUIRE_ROCQ=1 cargo test --workspace
(cd benchmarks/llm && python3 selftest.py)
EMD_BIN="$PWD/target/debug/emd" nvim --headless -n -u NONE -i NONE --cmd "set rtp^=editors/nvim" -c "luafile editors/nvim/test/main.lua"
EMD_BIN="$PWD/target/debug/emd" nvim --headless -n -u NONE -i NONE --cmd "set rtp^=editors/nvim" -c "luafile editors/nvim/test/studio_buffer.lua"
scripts/build-wasm.sh
fuzz/run.sh 60
cargo kani -p emd-core
cargo kani -p emd-parser
cargo kani -p emd-vm
cargo kani -p emd-asm
python3 scripts/kani-bugs.py
EMD_BIN="$PWD/target/debug/emd" python3 scripts/cbmc-c.py
python3 scripts/mutants.py

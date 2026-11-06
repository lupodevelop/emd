#!/bin/sh
# Fuzzes every target for the given seconds each, on the nightly toolchain, starting
# from the examples. usage: fuzz/run.sh [seconds]
set -eu
cd "$(dirname "$0")/.."
seconds="${1:-60}"
PATH="$(dirname "$(rustup which --toolchain nightly rustc)"):$HOME/.cargo/bin:$PATH"
export PATH
for target in parse_bytes doctor compile vm; do
  mkdir -p "fuzz/corpus/$target"
done
cp examples/*.emd fuzz/corpus/parse_bytes/
cp examples/*.emd fuzz/corpus/doctor/
cp examples/*.asm fuzz/corpus/compile/
for target in parse_bytes doctor compile vm; do
  cargo fuzz run "$target" -- -max_total_time="$seconds" -print_final_stats=1 -timeout=20
done

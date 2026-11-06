#!/bin/sh
# Builds the real parser and VM for the website. Needs: rustup target add wasm32-unknown-unknown
set -eu
cd "$(dirname "$0")/.."
# rustup's toolchain: a system rustc, such as Homebrew's, has no std for this target.
RUSTC="$(rustup which rustc)" "$(rustup which cargo)" build --release -p emd-wasm --target wasm32-unknown-unknown --target-dir target/wasm \
  --config 'profile.release.opt-level="s"' --config 'profile.release.lto=true' \
  --config 'profile.release.strip=true' --config 'profile.release.panic="abort"'
cp target/wasm/wasm32-unknown-unknown/release/emd_wasm.wasm website/public/emd.wasm
wc -c website/public/emd.wasm

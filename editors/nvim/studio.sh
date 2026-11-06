#!/bin/sh
# Opens a .emd file in the studio, using your normal Neovim configuration.
# usage: studio.sh [--clean] [file.emd]
# --clean starts an isolated session for troubleshooting.
clean=0
if [ "${1:-}" = "--clean" ]; then clean=1; shift; fi
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
file="${1:-$root/examples/fizzbuzz.emd}"
if [ -z "${EMD_BIN:-}" ]; then
  if command -v emd >/dev/null 2>&1; then EMD_BIN=emd; else EMD_BIN="$root/target/debug/emd"; fi
fi
export EMD_BIN
if [ "$clean" = 1 ]; then
  exec nvim -n -u NONE -i NONE --cmd "set rtp^=$here" \
    --cmd "filetype plugin on" --cmd "syntax on" --cmd "set mouse=a termguicolors laststatus=3 noshowmode" \
    --cmd "runtime ftdetect/emd.lua" --cmd "runtime plugin/emd.lua" \
    -c "EmdStudio" "$file"
fi
exec nvim --cmd "set rtp^=$here" --cmd "runtime ftdetect/emd.lua" \
  -c "if exists(':EmdStudio') != 2 | set rtp^=$here | runtime plugin/emd.lua | endif" \
  -c "EmdStudio" "$file"

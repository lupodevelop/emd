#!/bin/sh
# Checks the proofs, then builds the extracted interpreter used by the tests.
set -eu
cd "$(dirname "$0")"
rocq compile -R . EmdFormal Emd.v
rocq compile -R . EmdFormal Props.v
rocq compile -R . EmdFormal Source.v
rocq compile -R . EmdFormal Turing.v
rocq compile -R . EmdFormal Extract.v
ocamlfind ocamlopt -w -a -o emdref-rocq emd_extracted.mli emd_extracted.ml main.ml

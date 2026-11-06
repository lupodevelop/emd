import Emd

/-!
`emdref`: the reference interpreter, extracted from the model without rewriting it.

    emdref <file.emd> [input-file] [fuel]

Prints `halt` with stack and output, `fault <name>`, or `running` with stack and
output if the fuel runs out. `crates/emd-vm/tests/differential.rs` compares this
output with the Rust VM.
-/

open Emd

def main (args : List String) : IO UInt32 := do
  let file :: rest := args
    | IO.eprintln "usage: emdref <file.emd> [input-file] [fuel]"; return 2
  let bytes ← IO.FS.readBinFile file
  let some src := String.fromUTF8? bytes
    | IO.eprintln "invalid UTF-8"; return 1
  let some program := decodeSource (src.toList.map Char.toNat)
    | IO.eprintln "undecodable"; return 1
  let input ← match (rest[0]? : Option String) with
    | some inFile => (fun b => b.toList.map UInt8.toNat) <$> IO.FS.readBinFile inFile
    | none => pure ([] : List Nat)
  let fuel := (rest[1]? >>= String.toNat?).getD 1000000
  match run program fuel (State.init input) with
  | .halt s => IO.println s!"halt\nstack {s.stack}\noutput {s.output}"
  | .fault f => IO.println s!"fault {repr f}"
  | .next s => IO.println s!"running\nstack {s.stack}\noutput {s.output}"
  return 0

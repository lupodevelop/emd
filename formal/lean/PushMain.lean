import Emd.Lowering

/-! `emdpush <int>`: UTF-8 emd source of the mirror of `push_int`, no newline, to compare with the Rust. -/

open Emd

def main (args : List String) : IO UInt32 := do
  let [arg] := args
    | IO.eprintln "usage: emdpush <int>"; return 2
  let some n := arg.toInt?
    | IO.eprintln "not an integer"; return 2
  IO.print (String.ofList ((encodeProgram (pushInt n)).map fun s => Char.ofNat s.codePoint))
  return 0

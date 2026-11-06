import Emd.Lowering

/-! `emdlower`: reads statements on stdin, one per line, and prints the UTF-8 emd source of the
lowered program, no newline, to compare with `generate` in the Rust.

    label NAME
    instr ADD            any mnemonic; `instr PUSH 3`, and raw `instr JMP` too
    push -12             any integer
    jump JZ NAME         JMP, JZ, JNZ or CALL to a label

Exit codes: 0 success, 1 undefined or repeated label, 2 bad input, 3 layout not stable in the fuel. -/

open Emd

def plainOf : String → Option Instr
  | "DUP" => some .dup
  | "DROP" => some .drop
  | "SWAP" => some .swap
  | "OVER" => some .over
  | "ROT" => some .rot
  | "ADD" => some .add
  | "SUB" => some .sub
  | "MUL" => some .mul
  | "DIV" => some .div
  | "MOD" => some .mod
  | "LOAD" => some .load
  | "STORE" => some .store
  | "JMP" => some .jmp
  | "JZ" => some .jz
  | "JNZ" => some .jnz
  | "HALT" => some .halt
  | "CALL" => some .call
  | "RET" => some .ret
  | "READ" => some .read
  | "WRITE" => some .write
  | "EQ" => some .eq
  | "LT" => some .lt
  | "GT" => some .gt
  | "NOT" => some .not
  | _ => none

def kindOf : String → Option JumpKind
  | "JMP" => some .jmp
  | "JZ" => some .jz
  | "JNZ" => some .jnz
  | "CALL" => some .call
  | _ => none

/-- A statement as written; jumps name their label. -/
inductive Raw where
  | label (name : String)
  | stmt (s : Stmt)
  | jump (j : JumpKind) (name : String)

def parseLine (line : String) : Option Raw :=
  match (line.splitOn " ").filter (· ≠ "") with
  | ["label", name] => some (.label name)
  | ["instr", "PUSH", n] => do
    let k ← n.toNat?
    if h : k < 8 then some (.stmt (.plain (.push ⟨k, h⟩))) else none
  | ["instr", name] => do
    let x ← plainOf name
    some (.stmt (.plain x))
  | ["push", n] => do
    let v ← n.toInt?
    some (.stmt (.pushI v))
  | ["jump", kind, name] => do
    let j ← kindOf kind
    some (.jump j name)
  | _ => none

/-- A label names the index of the next statement, past the end included. -/
def labelsOf (raws : List Raw) : Option (List (String × Nat)) :=
  go raws 0 []
where
  go : List Raw → Nat → List (String × Nat) → Option (List (String × Nat))
    | [], _, acc => some acc
    | .label name :: rest, i, acc =>
      if (acc.lookup name).isSome then none else go rest i ((name, i) :: acc)
    | _ :: rest, i, acc => go rest (i + 1) acc

def resolve (labels : List (String × Nat)) : List Raw → Option (List Stmt)
  | [] => some []
  | .label _ :: rest => resolve labels rest
  | .stmt s :: rest => do
    let r ← resolve labels rest
    some (s :: r)
  | .jump j name :: rest => do
    let t ← labels.lookup name
    let r ← resolve labels rest
    some (.jump j t 0 :: r)

partial def readLines (h : IO.FS.Stream) (acc : Array String) : IO (Array String) := do
  let line ← h.getLine
  if line.isEmpty then return acc else readLines h (acc.push line)

def main : IO UInt32 := do
  let lines ← readLines (← IO.getStdin) #[]
  let cleaned := lines.toList.map (fun l => (l.toList.filter (· ≠ '\n')) |> String.ofList)
    |>.filter (· ≠ "")
  let some raws := cleaned.mapM parseLine
    | IO.eprintln "bad statement"; return 2
  let some labels := labelsOf raws
    | IO.eprintln "repeated label"; return 1
  let some src := resolve labels raws
    | IO.eprintln "undefined label"; return 1
  let some p := layoutLoop 100000 src
    | IO.eprintln "layout not stable"; return 3
  IO.print (String.ofList ((encodeProgram (lower p)).map fun s => Char.ofNat s.codePoint))
  return 0

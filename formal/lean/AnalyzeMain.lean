import Emd.Analyzer

/-! `emdanalyze <file.emd>`: the mirror of `analyze` in `crates/emd-analyze/src/`, to compare
with the Rust on random programs. The loop and the widening here are not proved: the result goes
through `checkResult`, which is, and the first line says whether it passed.

    certified 1
    halt 1
    reached 0 1 2
    issue 3 DivisionByZero 0

`certified` is 1 if the result passed the proved check. `halt` is `halt_reachable`. `reached` lists
the program points with any state, in order. One `issue <pc> <Kind> <certain>` per issue, by pc and
then in the order of the Rust's `Kind`, whose names these are. Exit code 1 on a source that does not
decode. -/

open Emd Emd.Analyzer

namespace Emd.Analyzer

instance : Inhabited Stacks := ⟨.empty⟩

instance : Inhabited Instr := ⟨.halt⟩

def Frame.join (a b : Frame) : Frame :=
  let cellIn (f : Frame) (k : Int) : Cell := (memGet f.mem k).getD (.plain f.rest)
  let keys := a.mem.map (·.1) ++ b.mem.map (·.1)
  { stack := List.zipWith Cell.join a.stack b.stack
    mem := keys.foldl (fun m k => memSet k ((cellIn a k).join (cellIn b k)) m) []
    rest := a.rest.join b.rest }

def isKnown : Val → Bool
  | .known _ => true
  | _ => false

def widenCell (all : Bool) (cell : Cell) (before : Val) : Cell :=
  if cell.val ≠ before ∧ (all || !isKnown cell.val) = true then
    .plain (cell.val.widenedFrom before)
  else cell

def Frame.widenFrom (self old : Frame) (all : Bool) : Frame :=
  let tail := self.stack.drop old.stack.length
  { stack := List.zipWith (fun c o => widenCell all c o.val) self.stack old.stack ++ tail
    mem := self.mem.map fun e => (e.1, widenCell all e.2 (old.cellVal e.1))
    rest := if self.rest ≠ old.rest ∧ (all || !isKnown self.rest) = true
      then self.rest.widenedFrom old.rest else self.rest }

def insertDepth (k : Nat) (f : Frame) : List (Nat × Frame) → List (Nat × Frame)
  | [] => [(k, f)]
  | e :: l => if k < e.1 then (k, f) :: e :: l else e :: insertDepth k f l

def replaceDepth (k : Nat) (f : Frame) : List (Nat × Frame) → List (Nat × Frame)
  | [] => []
  | e :: l => if e.1 = k then (k, f) :: l else e :: replaceDepth k f l

/-- `Stacks::add`: the new stacks, and whether anything changed. -/
def Stacks.add (s : Stacks) (incoming : Option Frame) (widen : Bool) : Stacks × Bool :=
  match incoming with
  | none => ({ s with unknown := true }, !s.unknown)
  | some frame =>
    let depth := frame.stack.length
    match s.byDepth.lookup depth with
    | some old =>
      let merged := (old.join frame).widenFrom old widen
      ({ s with byDepth := replaceDepth depth merged s.byDepth }, old ≠ merged)
    | none =>
      if s.byDepth.length ≥ maxDepths then ({ s with unknown := true }, !s.unknown)
      else ({ s with byDepth := insertDepth depth frame s.byDepth }, true)

def insertWork (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: l => if x < y then x :: y :: l else if x = y then y :: l else y :: insertWork x l

structure Loop where
  stacks : Array Stacks
  visits : Array Nat
  work : List Nat
  steps : Nat

def visitEdge (st : Loop) (e : Nat × Option Frame) : Loop :=
  let target := e.1
  let v := st.visits[target]! + 1
  let widen := v > widenVisits || st.steps > widenSteps
  let r := (st.stacks[target]!).add e.2 widen
  { st with
    visits := st.visits.set! target v
    stacks := st.stacks.set! target r.1
    work := if r.2 then insertWork target st.work else st.work }

partial def runLoop (P : List Instr) (st : Loop) : Loop :=
  match st.work with
  | [] => st
  | pc :: rest =>
    let i := P[pc]!
    let st1 := (st.stacks[pc]!).variants.foldl (fun (acc : Loop) variant =>
      let step := transfer P pc i variant
      let wildNext : List (Nat × Option Frame) :=
        if step.wild then (List.range P.length).map fun t => (t, none) else []
      let acc1 := { acc with steps := acc.steps + 1 }
      (step.next ++ wildNext).foldl visitEdge acc1) { st with work := rest }
    runLoop P st1

def kindRank : Kind → Nat
  | .stackUnderflow => 0
  | .pcOutOfRange => 1
  | .divisionByZero => 2
  | .negativeAddress => 3
  | .invalidByte => 4
  | .overflow => 5
  | .unknownJump => 6

def kindName : Kind → String
  | .stackUnderflow => "StackUnderflow"
  | .pcOutOfRange => "PcOutOfRange"
  | .divisionByZero => "DivisionByZero"
  | .negativeAddress => "NegativeAddress"
  | .invalidByte => "InvalidByte"
  | .overflow => "Overflow"
  | .unknownJump => "UnknownJump"

def allKinds : List Kind :=
  [.stackUnderflow, .pcOutOfRange, .divisionByZero, .negativeAddress, .invalidByte, .overflow,
    .unknownJump]

/-- An issue is certain only if every way of reaching the instruction raises it for sure. -/
def issueLines (P : List Instr) (R : List Stacks) : List String :=
  (List.range P.length).flatMap fun pc =>
    let vars := (recorded R pc).variants
    let steps := vars.map fun v => transfer P pc P[pc]! v
    allKinds.filterMap fun k =>
      let with' := steps.filter fun s => s.issues.any fun e => e.1 == k
      if with'.isEmpty then none
      else
        let everyCertain := with'.all fun s => (s.issues.filter fun e => e.1 == k).all (·.2)
        let certain := everyCertain && with'.length == vars.length
        some s!"issue {pc} {kindName k} {if certain then 1 else 0}"

end Emd.Analyzer

def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: emdanalyze <file.emd>"; return 2
  let bytes ← IO.FS.readBinFile file
  let some src := String.fromUTF8? bytes
    | IO.eprintln "invalid UTF-8"; return 1
  let some P := decodeSource (src.toList.map Char.toNat)
    | IO.eprintln "undecodable"; return 1
  if P.isEmpty then
    IO.println "certified 1\nhalt 0\nreached\nissue 0 PcOutOfRange 1"
    return 0
  let first := Stacks.empty.add (some Frame.start) false
  let start : Loop :=
    { stacks := (Array.replicate P.length Stacks.empty).set! 0 first.1
      visits := Array.replicate P.length 0
      work := [0]
      steps := 0 }
  let R := (runLoop P start).stacks.toList
  IO.println s!"certified {if checkResult P R then 1 else 0}"
  IO.println s!"halt {if haltsReported P R then 1 else 0}"
  let reached := (List.range P.length).filter fun pc => !(recorded R pc).variants.isEmpty
  IO.println ("reached" ++ String.join (reached.map fun pc => s!" {pc}"))
  for line in issueLines P R do
    IO.println line
  return 0

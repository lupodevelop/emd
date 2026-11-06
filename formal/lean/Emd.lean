/-!
# emd: the reference model

Syntax, encoding, state and execution step of the emd machine.

The semantics is a function (`step`), so determinism holds by construction and
`step_det` states it on the derived relation `Step`. Integers are unbounded. The
Rust implementation (`crates/emd-vm`) adds 64-bit integers and resource limits,
declared as faults of their own.

Stack convention: the head of the list is the top. `b` is the top, `a` the value
below; `sub` computes `a - b`.
-/

namespace Emd

/-- A symbol: index 0..7 in the alphabet, ordered by code point. -/
abbrev Sym := Fin 8

/-- The code point of a symbol. -/
def Sym.codePoint (s : Sym) : Nat :=
  match s.val with
  | 0 => 0x2D
  | 1 => 0x2010
  | 2 => 0x2011
  | 3 => 0x2012
  | 4 => 0x2013
  | 5 => 0x2014
  | 6 => 0x2015
  | _ => 0x2212

/-- The symbol of a code point; `none` outside the alphabet. -/
def Sym.ofCodePoint : Nat → Option Sym
  | 0x2D => some 0
  | 0x2010 => some 1
  | 0x2011 => some 2
  | 0x2012 => some 3
  | 0x2013 => some 4
  | 0x2014 => some 5
  | 0x2015 => some 6
  | 0x2212 => some 7
  | _ => none

theorem ofCodePoint_codePoint (s : Sym) : Sym.ofCodePoint s.codePoint = some s := by
  revert s
  decide

inductive Instr where
  | push (n : Sym)
  | dup | drop | swap | over | rot
  | add | sub | mul | div | mod
  | load | store
  | jmp | jz | jnz | halt | call | ret
  | read | write
  | eq | lt | gt | not
  deriving DecidableEq, Repr

/-- The pair (family, operation) of an instruction. -/
def encode : Instr → Sym × Sym
  | .push n => (0, n)
  | .dup => (1, 0)
  | .drop => (1, 1)
  | .swap => (1, 2)
  | .over => (1, 3)
  | .rot => (1, 4)
  | .add => (2, 0)
  | .sub => (2, 1)
  | .mul => (2, 2)
  | .div => (2, 3)
  | .mod => (2, 4)
  | .load => (3, 0)
  | .store => (3, 1)
  | .jmp => (4, 0)
  | .jz => (4, 1)
  | .jnz => (4, 2)
  | .halt => (4, 3)
  | .call => (4, 4)
  | .ret => (4, 5)
  | .read => (5, 0)
  | .write => (5, 1)
  | .eq => (6, 0)
  | .lt => (6, 1)
  | .gt => (6, 2)
  | .not => (6, 3)

/-- The instruction of a pair; `none` if the pair is unassigned. -/
def decode (p : Sym × Sym) : Option Instr :=
  match p.1.val, p.2.val with
  | 0, _ => some (.push p.2)
  | 1, 0 => some .dup
  | 1, 1 => some .drop
  | 1, 2 => some .swap
  | 1, 3 => some .over
  | 1, 4 => some .rot
  | 2, 0 => some .add
  | 2, 1 => some .sub
  | 2, 2 => some .mul
  | 2, 3 => some .div
  | 2, 4 => some .mod
  | 3, 0 => some .load
  | 3, 1 => some .store
  | 4, 0 => some .jmp
  | 4, 1 => some .jz
  | 4, 2 => some .jnz
  | 4, 3 => some .halt
  | 4, 4 => some .call
  | 4, 5 => some .ret
  | 5, 0 => some .read
  | 5, 1 => some .write
  | 6, 0 => some .eq
  | 6, 1 => some .lt
  | 6, 2 => some .gt
  | 6, 3 => some .not
  | _, _ => none

def encodeProgram : List Instr → List Sym
  | [] => []
  | i :: is => (encode i).1 :: (encode i).2 :: encodeProgram is

def decodeProgram : List Sym → Option (List Instr)
  | [] => some []
  | [_] => none
  | f :: o :: rest => do
    let i ← decode (f, o)
    let is ← decodeProgram rest
    pure (i :: is)

theorem decode_encode (i : Instr) : decode (encode i) = some i := by
  cases i <;> rfl

theorem encode_decode_bool (f o : Sym) :
    ((decode (f, o)).all fun i => decide (encode i = (f, o))) = true := by
  revert f o
  decide

/-- On assigned pairs, `encode` inverts `decode`. -/
theorem encode_decode (f o : Sym) (i : Instr) (h : decode (f, o) = some i) :
    encode i = (f, o) := by
  have := encode_decode_bool f o
  rw [h] at this
  simpa using this

theorem decodeProgram_encodeProgram (P : List Instr) :
    decodeProgram (encodeProgram P) = some P := by
  induction P with
  | nil => rfl
  | cons i is ih =>
    have h : decode ((encode i).1, (encode i).2) = some i := decode_encode i
    simp [encodeProgram, decodeProgram, h, ih]

/-- Two programs with the same source are the same program. -/
theorem encodeProgram_injective {P Q : List Instr}
    (h : encodeProgram P = encodeProgram Q) : P = Q := by
  have := decodeProgram_encodeProgram P
  rw [h, decodeProgram_encodeProgram] at this
  exact (Option.some.inj this).symm

/-! ## Source text

A source is lines separated by U+000A, each at most 32 code points. Every U+000A is removed
before decoding, so a break may fall anywhere, even inside a pair, and at the end. -/

def maxLine : Nat := 32

/-- `n` code points so far on the current line; every line stays within `maxLine`. -/
def linesFit : Nat → List Nat → Bool
  | _, [] => true
  | n, c :: cs => if c = 10 then linesFit 0 cs else decide (n < maxLine) && linesFit (n + 1) cs

/-- Symbols of a source, line breaks removed; `none` on any other foreign code point. -/
def toSyms : List Nat → Option (List Sym)
  | [] => some []
  | c :: cs =>
    if c = 10 then toSyms cs
    else do
      let s ← Sym.ofCodePoint c
      let r ← toSyms cs
      pure (s :: r)

def decodeSource (cps : List Nat) : Option (List Instr) :=
  if linesFit 0 cps then (toSyms cps).bind decodeProgram else none

/-! ## Semantics -/

structure State where
  pc : Nat
  stack : List Int
  mem : Nat → Int
  input : List Nat
  output : List Nat

def State.init (input : List Nat) : State := ⟨0, [], fun _ => 0, input, []⟩

inductive Fault where
  | stackUnderflow
  | divisionByZero
  | negativeAddress
  | pcOutOfRange
  | invalidByte
  deriving DecidableEq, Repr

inductive Outcome where
  | next (s : State)
  | halt (s : State)
  | fault (f : Fault)

/-- Sets `pc` to `target`; outside `0 ≤ target < |P|` is a fault.
`target = |P|` is one too: a program ends only with `halt`. -/
def jumpTo (P : List Instr) (s : State) (target : Int) : Outcome :=
  if 0 ≤ target ∧ target < P.length then .next { s with pc := target.toNat }
  else .fault .pcOutOfRange

def advance (P : List Instr) (s : State) : Outcome :=
  jumpTo P s ((s.pc : Int) + 1)

def binary (P : List Instr) (s : State) (f : Int → Int → Int) : Outcome :=
  match s.stack with
  | b :: a :: r => advance P { s with stack := f a b :: r }
  | _ => .fault .stackUnderflow

def divLike (P : List Instr) (s : State) (f : Int → Int → Int) : Outcome :=
  match s.stack with
  | b :: a :: r =>
    if b = 0 then .fault .divisionByZero else advance P { s with stack := f a b :: r }
  | _ => .fault .stackUnderflow

def b2i (p : Prop) [Decidable p] : Int := if p then 1 else 0

/-- The effect of an instruction on the state. `div` and `mod` truncate toward zero. -/
def exec (P : List Instr) (s : State) : Instr → Outcome
  | .push n => advance P { s with stack := (n.val : Int) :: s.stack }
  | .dup => match s.stack with
    | a :: r => advance P { s with stack := a :: a :: r }
    | _ => .fault .stackUnderflow
  | .drop => match s.stack with
    | _ :: r => advance P { s with stack := r }
    | _ => .fault .stackUnderflow
  | .swap => match s.stack with
    | b :: a :: r => advance P { s with stack := a :: b :: r }
    | _ => .fault .stackUnderflow
  | .over => match s.stack with
    | b :: a :: r => advance P { s with stack := a :: b :: a :: r }
    | _ => .fault .stackUnderflow
  | .rot => match s.stack with
    | c :: b :: a :: r => advance P { s with stack := a :: c :: b :: r }
    | _ => .fault .stackUnderflow
  | .add => binary P s (· + ·)
  | .sub => binary P s (· - ·)
  | .mul => binary P s (· * ·)
  | .div => divLike P s Int.tdiv
  | .mod => divLike P s Int.tmod
  | .load => match s.stack with
    | a :: r =>
      if a < 0 then .fault .negativeAddress
      else advance P { s with stack := s.mem a.toNat :: r }
    | _ => .fault .stackUnderflow
  | .store => match s.stack with
    | a :: v :: r =>
      if a < 0 then .fault .negativeAddress
      else advance P { s with stack := r, mem := fun i => if i = a.toNat then v else s.mem i }
    | _ => .fault .stackUnderflow
  | .jmp => match s.stack with
    | off :: r => jumpTo P { s with stack := r } ((s.pc : Int) + off)
    | _ => .fault .stackUnderflow
  | .jz => match s.stack with
    | off :: c :: r =>
      if c = 0 then jumpTo P { s with stack := r } ((s.pc : Int) + off)
      else advance P { s with stack := r }
    | _ => .fault .stackUnderflow
  | .jnz => match s.stack with
    | off :: c :: r =>
      if c ≠ 0 then jumpTo P { s with stack := r } ((s.pc : Int) + off)
      else advance P { s with stack := r }
    | _ => .fault .stackUnderflow
  | .halt => .halt s
  | .call => match s.stack with
    | off :: r => jumpTo P { s with stack := ((s.pc : Int) + 1) :: r } ((s.pc : Int) + off)
    | _ => .fault .stackUnderflow
  | .ret => match s.stack with
    | a :: r => jumpTo P { s with stack := r } a
    | _ => .fault .stackUnderflow
  | .read => match s.input with
    | b :: rest => advance P { s with stack := (b : Int) :: s.stack, input := rest }
    | [] => advance P { s with stack := -1 :: s.stack }
  | .write => match s.stack with
    | v :: r =>
      if 0 ≤ v ∧ v ≤ 255 then advance P { s with stack := r, output := s.output ++ [v.toNat] }
      else .fault .invalidByte
    | _ => .fault .stackUnderflow
  | .eq => binary P s fun a b => b2i (a = b)
  | .lt => binary P s fun a b => b2i (a < b)
  | .gt => binary P s fun a b => b2i (a > b)
  | .not => match s.stack with
    | a :: r => advance P { s with stack := b2i (a = 0) :: r }
    | _ => .fault .stackUnderflow

/-- One step: runs `P[pc]`, a fault if `pc` is outside the program. -/
def step (P : List Instr) (s : State) : Outcome :=
  match P[s.pc]? with
  | some i => exec P s i
  | none => .fault .pcOutOfRange

/-- The transition relation derived from `step`. -/
def Step (P : List Instr) (s s' : State) : Prop := step P s = .next s'

theorem step_det {P : List Instr} {s s₁ s₂ : State}
    (h₁ : Step P s s₁) (h₂ : Step P s s₂) : s₁ = s₂ := by
  unfold Step at h₁ h₂
  rw [h₁] at h₂
  exact Outcome.next.inj h₂

/-- Execution with fuel: `next` after `n` steps means "not finished yet". -/
def run (P : List Instr) : Nat → State → Outcome
  | 0, s => .next s
  | n + 1, s =>
    match step P s with
    | .next s' => run P n s'
    | o => o

/-- The example program of the specification: `1 + 2`, then `halt`. -/
def example1 : List Instr := [.push 1, .push 2, .add, .halt]

theorem example1_halts_with_3 :
    ∃ s, run example1 10 (State.init []) = .halt s ∧ s.stack = [3] :=
  ⟨_, rfl, rfl⟩

end Emd

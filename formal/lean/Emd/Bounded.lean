import Emd.Properties

/-! # The bounded machine: what `crates/emd-vm` does, as a model.

`bstep` is written from the Rust, in the Rust's order of checks: 64-bit values with an `overflow`
fault, and limits on steps, stack and memory cells. It does not call `step`, so the refinement
theorems below compare two definitions. Integers stay `Int`: `InI64` says which ones fit. This is
still a model of the Rust, not the Rust. -/

namespace Emd

def i64Min : Int := -9223372036854775808

def i64Max : Int := 9223372036854775807

def InI64 (v : Int) : Prop := i64Min ≤ v ∧ v ≤ i64Max

instance (v : Int) : Decidable (InI64 v) := by
  unfold InI64
  infer_instance

structure Limits where
  maxSteps : Nat
  maxStack : Nat
  maxCells : Nat

/-- The model's faults, and the ones only the implementation has. -/
inductive BFault where
  | model (f : Fault)
  | overflow
  | stepLimit
  | stackLimit
  | memoryLimit

/-- A state, the steps taken, and the cells written: the keys of the Rust `BTreeMap`. -/
structure BState where
  core : State
  steps : Nat
  cells : List Nat

inductive BOutcome where
  | next (b : BState)
  | halt (b : BState)
  | fault (f : BFault)

/-- `target` in the Rust: `pc + off`, saturating at the top of `i64`. -/
def btarget (P : List Instr) (pc : Nat) (off : Int) : Option Nat :=
  let t := min ((pc : Int) + off) i64Max
  if t < 0 ∨ t ≥ (P.length : Int) then none else some t.toNat

def goWith (P : List Instr) (b : BState) (off : Int) (k : Nat → BState) : BOutcome :=
  match btarget P b.core.pc off with
  | none => .fault (.model .pcOutOfRange)
  | some nx => .next (k nx)

/-- The target first, then room for one more value: the order of `push` in the Rust. -/
def goRoom (P : List Instr) (L : Limits) (b : BState) (off : Int) (k : Nat → BState) : BOutcome :=
  match btarget P b.core.pc off with
  | none => .fault (.model .pcOutOfRange)
  | some nx =>
    if L.maxStack ≤ b.core.stack.length then .fault .stackLimit else .next (k nx)

def BState.upd (b : BState) (nx : Nat) (st : List Int) : BState :=
  { b with core := { b.core with pc := nx, stack := st } }

/-- `checked_add` and friends: the overflow check comes before the target. -/
def bArith (P : List Instr) (b : BState) (f : Int → Int → Int) : BOutcome :=
  match b.core.stack with
  | y :: x :: r =>
    if InI64 (f x y) then goWith P b 1 fun nx => b.upd nx (f x y :: r) else .fault .overflow
  | _ => .fault (.model .stackUnderflow)

def bCompare (P : List Instr) (b : BState) (f : Int → Int → Int) : BOutcome :=
  match b.core.stack with
  | y :: x :: r => goWith P b 1 fun nx => b.upd nx (f x y :: r)
  | _ => .fault (.model .stackUnderflow)

def bexec (P : List Instr) (L : Limits) (b : BState) : Instr → BOutcome
  | .push n => goRoom P L b 1 fun nx => b.upd nx ((n.val : Int) :: b.core.stack)
  | .dup => match b.core.stack with
    | a :: r => goRoom P L b 1 fun nx => b.upd nx (a :: a :: r)
    | _ => .fault (.model .stackUnderflow)
  | .drop => match b.core.stack with
    | _ :: r => goWith P b 1 fun nx => b.upd nx r
    | _ => .fault (.model .stackUnderflow)
  | .swap => match b.core.stack with
    | y :: x :: r => goWith P b 1 fun nx => b.upd nx (x :: y :: r)
    | _ => .fault (.model .stackUnderflow)
  | .over => match b.core.stack with
    | y :: x :: r => goRoom P L b 1 fun nx => b.upd nx (x :: y :: x :: r)
    | _ => .fault (.model .stackUnderflow)
  | .rot => match b.core.stack with
    | z :: y :: x :: r => goWith P b 1 fun nx => b.upd nx (x :: z :: y :: r)
    | _ => .fault (.model .stackUnderflow)
  | .add => bArith P b (· + ·)
  | .sub => bArith P b (· - ·)
  | .mul => bArith P b (· * ·)
  | .div => match b.core.stack with
    | y :: x :: r =>
      if y = 0 then .fault (.model .divisionByZero)
      else if InI64 (Int.tdiv x y) then goWith P b 1 fun nx => b.upd nx (Int.tdiv x y :: r)
      else .fault .overflow
    | _ => .fault (.model .stackUnderflow)
  | .mod => match b.core.stack with
    | y :: x :: r =>
      if y = 0 then .fault (.model .divisionByZero)
      else goWith P b 1 fun nx => b.upd nx (Int.tmod x y :: r)
    | _ => .fault (.model .stackUnderflow)
  | .load => match b.core.stack with
    | a :: r =>
      if a < 0 then .fault (.model .negativeAddress)
      else goWith P b 1 fun nx => b.upd nx (b.core.mem a.toNat :: r)
    | _ => .fault (.model .stackUnderflow)
  | .store => match b.core.stack with
    | a :: v :: r =>
      if a < 0 then .fault (.model .negativeAddress)
      else if a.toNat ∉ b.cells ∧ L.maxCells ≤ b.cells.length then .fault .memoryLimit
      else goWith P b 1 fun nx =>
        { b with
          core := { b.core with pc := nx, stack := r,
                                mem := fun i => if i = a.toNat then v else b.core.mem i }
          cells := if a.toNat ∈ b.cells then b.cells else a.toNat :: b.cells }
    | _ => .fault (.model .stackUnderflow)
  | .jmp => match b.core.stack with
    | off :: r => goWith P b off fun nx => b.upd nx r
    | _ => .fault (.model .stackUnderflow)
  | .jz => match b.core.stack with
    | off :: c :: r => goWith P b (if c = 0 then off else 1) fun nx => b.upd nx r
    | _ => .fault (.model .stackUnderflow)
  | .jnz => match b.core.stack with
    | off :: c :: r => goWith P b (if c ≠ 0 then off else 1) fun nx => b.upd nx r
    | _ => .fault (.model .stackUnderflow)
  | .halt => .halt b
  | .call => match b.core.stack with
    | off :: r => goWith P b off fun nx => b.upd nx (((b.core.pc : Int) + 1) :: r)
    | _ => .fault (.model .stackUnderflow)
  | .ret => match b.core.stack with
    | a :: r =>
      if 0 ≤ a ∧ a < (P.length : Int) then .next (b.upd a.toNat r)
      else .fault (.model .pcOutOfRange)
    | _ => .fault (.model .stackUnderflow)
  | .read =>
    if L.maxStack ≤ b.core.stack.length then .fault .stackLimit
    else match b.core.input with
      | x :: rest => goWith P b 1 fun nx =>
        { b with core := { b.core with pc := nx, stack := (x : Int) :: b.core.stack, input := rest } }
      | [] => goWith P b 1 fun nx => b.upd nx (-1 :: b.core.stack)
  | .write => match b.core.stack with
    | v :: r =>
      if 0 ≤ v ∧ v ≤ 255 then goWith P b 1 fun nx =>
        { b with core := { b.core with pc := nx, stack := r,
                                       output := b.core.output ++ [v.toNat] } }
      else .fault (.model .invalidByte)
    | _ => .fault (.model .stackUnderflow)
  | .eq => bCompare P b fun x y => b2i (x = y)
  | .lt => bCompare P b fun x y => b2i (x < y)
  | .gt => bCompare P b fun x y => b2i (x > y)
  | .not => match b.core.stack with
    | a :: r => goWith P b 1 fun nx => b.upd nx (b2i (a = 0) :: r)
    | _ => .fault (.model .stackUnderflow)

/-- `Vm::step`: the step limit, then the fetch, which counts as a step. -/
def bstep (P : List Instr) (L : Limits) (b : BState) : BOutcome :=
  if L.maxSteps ≤ b.steps then .fault .stepLimit
  else match P[b.core.pc]? with
    | none => .fault (.model .pcOutOfRange)
    | some i => bexec P L { b with steps := b.steps + 1 } i

def brun (P : List Instr) (L : Limits) : Nat → BState → BOutcome
  | 0, b => .next b
  | n + 1, b =>
    match bstep P L b with
    | .next b' => brun P L n b'
    | o => o

def BState.init (input : List Nat) : BState := ⟨State.init input, 0, []⟩

/-! ## Refinement of one step -/

/-- The bounded outcome agrees with the unbounded one, unless it is a fault of the implementation. -/
def Ref : BOutcome → Outcome → Prop
  | .next b', o => o = .next b'.core
  | .halt b', o => o = .halt b'.core
  | .fault (.model f), o => o = .fault f
  | .fault _, _ => True

-- Saturation changes nothing while the program is shorter than the top of `i64`.
theorem jumpTo_btarget {P : List Instr} (hP : (P.length : Int) ≤ i64Max) (t : State) (pc : Nat)
    (off : Int) :
    jumpTo P t ((pc : Int) + off) =
      match btarget P pc off with
      | none => .fault .pcOutOfRange
      | some nx => .next { t with pc := nx } := by
  have hmax : i64Max = 9223372036854775807 := rfl
  unfold jumpTo btarget
  by_cases hc : 0 ≤ (pc : Int) + off ∧ (pc : Int) + off < (P.length : Int)
  · have e : min ((pc : Int) + off) i64Max = (pc : Int) + off := by omega
    have hn : ¬ ((pc : Int) + off < 0 ∨ (pc : Int) + off ≥ (P.length : Int)) := by omega
    simp only [e]
    rw [ite_eq_left hc, ite_eq_right hn]
  · have hn : min ((pc : Int) + off) i64Max < 0 ∨ min ((pc : Int) + off) i64Max ≥ (P.length : Int) := by
      omega
    simp only
    rw [ite_eq_right hc, ite_eq_left hn]

-- From here on nothing needs to compute the target, and unfolding it walks a 64-bit literal.
attribute [irreducible] btarget

theorem goWith_ref {P : List Instr} (hP : (P.length : Int) ≤ i64Max) (b : BState) (off : Int)
    (k : Nat → BState) (t : State) (hk : ∀ nx, (k nx).core = { t with pc := nx }) :
    Ref (goWith P b off k) (jumpTo P t ((b.core.pc : Int) + off)) := by
  rw [jumpTo_btarget hP]
  unfold goWith
  cases btarget P b.core.pc off with
  | none => rfl
  | some nx => exact congrArg Outcome.next (hk nx).symm

theorem goRoom_ref {P : List Instr} (hP : (P.length : Int) ≤ i64Max) (L : Limits) (b : BState)
    (off : Int) (k : Nat → BState) (t : State) (hk : ∀ nx, (k nx).core = { t with pc := nx }) :
    Ref (goRoom P L b off k) (jumpTo P t ((b.core.pc : Int) + off)) := by
  rw [jumpTo_btarget hP]
  unfold goRoom
  cases btarget P b.core.pc off with
  | none => rfl
  | some nx =>
    simp only
    split
    · trivial
    · exact congrArg Outcome.next (hk nx).symm

theorem ret_ref_in {P : List Instr} {t : State} {a : Int} {k : BState}
    (hc : 0 ≤ a ∧ a < (P.length : Int)) (hk : k.core = { t with pc := a.toNat }) :
    Ref (.next k) (jumpTo P t a) := by
  unfold jumpTo
  rw [ite_eq_left hc]
  exact congrArg Outcome.next hk.symm

theorem ret_ref_out {P : List Instr} {t : State} {a : Int}
    (hc : ¬ (0 ≤ a ∧ a < (P.length : Int))) :
    Ref (.fault (.model .pcOutOfRange)) (jumpTo P t a) := by
  unfold jumpTo
  rw [ite_eq_right hc]
  rfl

/-- One instruction: `bexec` and `exec` agree, in the Rust's order of checks, all 28 of them. -/
theorem bexec_ref {P : List Instr} (hP : (P.length : Int) ≤ i64Max) (L : Limits) (b : BState)
    (i : Instr) : Ref (bexec P L b i) (exec P b.core i) := by
  obtain ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ := b
  have hgo : ∀ (off : Int) (k : Nat → BState) (t : State),
      (∀ nx, (k nx).core = { t with pc := nx }) →
      Ref (goWith P ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ off k) (jumpTo P t ((pc : Int) + off)) :=
    fun off k t hk => goWith_ref hP _ off k t hk
  have hroom : ∀ (off : Int) (k : Nat → BState) (t : State),
      (∀ nx, (k nx).core = { t with pc := nx }) →
      Ref (goRoom P L ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ off k) (jumpTo P t ((pc : Int) + off)) :=
    fun off k t hk => goRoom_ref hP L _ off k t hk
  rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
    simp only [bexec, exec, bArith, bCompare, binary, divLike, advance] <;>
    (repeat' split) <;>
    first
    | exact hgo _ _ _ (fun _ => rfl)
    | exact hroom _ _ _ (fun _ => rfl)
    | contradiction
    | trivial
    | (rename_i hc; exact ret_ref_in hc rfl)
    | (rename_i hc; exact ret_ref_out hc)
    | rfl
    | (simp only [*, ↓reduceIte]; exact hgo _ _ _ (fun _ => rfl))
    | (simp_all; done)

/-- One bounded step refines one model step: same next state, same halt, same model fault. -/
theorem bstep_ref {P : List Instr} (hP : (P.length : Int) ≤ i64Max) (L : Limits) (b : BState) :
    Ref (bstep P L b) (step P b.core) := by
  unfold bstep step
  split
  · trivial
  · cases hi : P[b.core.pc]? with
    | none => rfl
    | some i => exact bexec_ref hP L { b with steps := b.steps + 1 } i

/-! ## Why an implementation fault happens -/

theorem goWith_fault {P : List Instr} {b : BState} {off : Int} {k : Nat → BState} {f : BFault}
    (h : goWith P b off k = .fault f) : f = .model .pcOutOfRange := by
  unfold goWith at h
  cases hb : btarget P b.core.pc off with
  | none => simpa [hb] using h.symm
  | some nx => simp [hb] at h

theorem goRoom_fault {P : List Instr} {L : Limits} {b : BState} {off : Int} {k : Nat → BState}
    {f : BFault} (h : goRoom P L b off k = .fault f) :
    f = .model .pcOutOfRange ∨ (f = .stackLimit ∧ L.maxStack ≤ b.core.stack.length) := by
  unfold goRoom at h
  cases hb : btarget P b.core.pc off with
  | none =>
    left
    simpa [hb] using h.symm
  | some nx =>
    simp only [hb] at h
    split at h
    · rename_i hc
      cases h
      exact .inr ⟨rfl, hc⟩
    · cases h

/-- The stack limit fires only on a full stack. -/
theorem bexec_stackLimit {P : List Instr} {L : Limits} {b : BState} {i : Instr}
    (h : bexec P L b i = .fault .stackLimit) : L.maxStack ≤ b.core.stack.length := by
  obtain ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ := b
  rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
    simp only [bexec, bArith, bCompare] at h <;>
    (repeat' split at h) <;>
    first
    | (cases h; done)
    | (rename_i hc; exact hc)
    | exact ((goRoom_fault h).resolve_left fun e => by cases e).2
    | (have := goWith_fault h; cases this; done)
    | (simp_all; done)

/-- The memory limit fires only on a new cell when the table is full. -/
theorem bexec_memoryLimit {P : List Instr} {L : Limits} {b : BState} {i : Instr}
    (h : bexec P L b i = .fault .memoryLimit) : L.maxCells ≤ b.cells.length := by
  obtain ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ := b
  rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
    simp only [bexec, bArith, bCompare] at h <;>
    (repeat' split at h) <;>
    first
    | (cases h; done)
    | (rename_i hc; exact hc.2)
    | (have := goWith_fault h; cases this; done)
    | (have := goRoom_fault h; simp at this; done)
    | (simp_all; done)

/-- Overflow fires only when the model's result does not fit in 64 bits. -/
theorem bexec_overflow {P : List Instr} {L : Limits} {b : BState} {i : Instr} {s' : State}
    (h : bexec P L b i = .fault .overflow) (hs : exec P b.core i = .next s') :
    ∃ v ∈ s'.stack, ¬ InI64 v := by
  obtain ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ := b
  rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
    simp only [bexec, bArith, bCompare, exec, binary, divLike, advance] at h hs <;>
    (repeat' split at h) <;>
    first
    | (cases h; done)
    | (have := goWith_fault h; cases this; done)
    | (have := goRoom_fault h; simp at this; done)
    | (repeat' split at hs
       all_goals first
         | (cases hs; done)
         | contradiction
         | (obtain ⟨rfl, _⟩ := jumpTo_next hs
            exact ⟨_, .head _, by assumption⟩))

/-! ## What a bounded step preserves -/

theorem goWith_next {P : List Instr} {b b' : BState} {off : Int} {k : Nat → BState}
    (h : goWith P b off k = .next b') : ∃ nx, b' = k nx := by
  unfold goWith at h
  cases hb : btarget P b.core.pc off with
  | none => simp [hb] at h
  | some nx =>
    simp only [hb] at h
    exact ⟨nx, (BOutcome.next.inj h).symm⟩

theorem goRoom_next {P : List Instr} {L : Limits} {b b' : BState} {off : Int} {k : Nat → BState}
    (h : goRoom P L b off k = .next b') :
    ∃ nx, b' = k nx ∧ b.core.stack.length < L.maxStack := by
  unfold goRoom at h
  cases hb : btarget P b.core.pc off with
  | none => simp [hb] at h
  | some nx =>
    simp only [hb] at h
    split at h
    · cases h
    · rename_i hc
      exact ⟨nx, (BOutcome.next.inj h).symm, by omega⟩

/-- Every value on the stack and in memory fits in 64 bits, and input is bytes. -/
def InRange (s : State) : Prop :=
  (∀ v ∈ s.stack, InI64 v) ∧ (∀ j, InI64 (s.mem j)) ∧ ∀ x ∈ s.input, x ≤ 255

/-- The limits hold and `cells` covers every cell that is not zero. -/
def Within (L : Limits) (b : BState) : Prop :=
  b.steps ≤ L.maxSteps ∧ b.core.stack.length ≤ L.maxStack ∧ b.cells.length ≤ L.maxCells ∧
    ∀ j, j ∉ b.cells → b.core.mem j = 0

theorem inI64_b2i (p : Prop) [Decidable p] : InI64 (b2i p) := by
  unfold InI64 b2i i64Min i64Max
  split <;> omega

theorem inI64_tmod {a : Int} (b : Int) (h : InI64 a) : InI64 (Int.tmod a b) := by
  have hn : (Int.tmod a b).natAbs ≤ a.natAbs := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_le _ _
  unfold InI64 i64Min i64Max at *
  by_cases ha : 0 ≤ a
  · have := Int.tmod_nonneg b ha
    omega
  · have h1 : 0 ≤ Int.tmod (-a) b := Int.tmod_nonneg b (by omega)
    have h2 : Int.tmod (-a) b = -Int.tmod a b := Int.neg_tmod a b
    omega

/-- A bounded step keeps every value in 64 bits: the invariant the Rust's types give for free. -/
theorem bexec_inRange {P : List Instr} {L : Limits} {b b' : BState} {i : Instr}
    (hP : (P.length : Int) ≤ i64Max) (hs : InRange b.core) (hpc : b.core.pc < P.length)
    (h : bexec P L b i = .next b') : InRange b'.core := by
  obtain ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ := b
  obtain ⟨h1, h2, h3⟩ := hs
  simp only at h1 h2 h3 hpc
  have hpc1 : InI64 ((pc : Int) + 1) := by
    unfold InI64 i64Min
    omega
  have hn : ∀ n : Sym, InI64 ((n.val : Nat) : Int) := by
    intro n
    have := n.isLt
    unfold InI64 i64Min i64Max
    omega
  have hm1 : InI64 (-1) := by
    unfold InI64 i64Min i64Max
    omega
  have hbyte : ∀ x : Nat, x ≤ 255 → InI64 (x : Int) := by
    intro x hx
    unfold InI64 i64Min i64Max
    omega
  rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, false_imp_iff, implies_true,
      and_true] at h1 h3 <;>
    simp only [bexec, bArith, bCompare] at h <;>
    (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; exact ⟨by simpa using h1, h2, by simpa using h3⟩)
    | (obtain ⟨nx, rfl⟩ := goWith_next h
       refine ⟨?_, ?_, ?_⟩
       · simp_all [BState.upd, inI64_b2i, inI64_tmod]
       · first
         | exact h2
         | (intro j; simp only []; split <;> simp_all)
       · simp_all [BState.upd])
    | (obtain ⟨nx, rfl, _⟩ := goRoom_next h
       refine ⟨?_, h2, ?_⟩
       · simp_all [BState.upd]
       · simp_all [BState.upd])
    | (cases h
       refine ⟨?_, h2, ?_⟩
       · simp_all [BState.upd]
       · simp_all [BState.upd])

/-- A bounded step never leaves the limits. -/
theorem bexec_within {P : List Instr} {L : Limits} {b b' : BState} {i : Instr}
    (hw : Within L b) (h : bexec P L b i = .next b') :
    b'.core.stack.length ≤ L.maxStack ∧ b'.cells.length ≤ L.maxCells ∧ b'.steps = b.steps ∧
      b'.cells.length ≤ b.cells.length + 1 ∧ ∀ j, j ∉ b'.cells → b'.core.mem j = 0 := by
  obtain ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ := b
  obtain ⟨_, hst, hc, hz⟩ := hw
  simp only at hst hc hz
  rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
    simp only [bexec, bArith, bCompare] at h <;>
    (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; simp_all; done)
    | (obtain ⟨nx, rfl, hr⟩ := goRoom_next h
       simp only [BState.upd, List.length_cons, List.length_nil] at hst hr ⊢
       exact ⟨by omega, by omega, by first | rfl | trivial, by omega, hz⟩)
    | (cases h
       simp only [BState.upd, List.length_cons, List.length_nil] at hst ⊢
       exact ⟨by omega, by omega, by first | rfl | trivial, by omega, hz⟩)
    | (obtain ⟨nx, rfl⟩ := goWith_next h
       simp only [BState.upd, List.length_cons, List.length_nil] at *
       exact ⟨by omega, by omega, by first | rfl | trivial, by omega, hz⟩)
    | (obtain ⟨nx, rfl⟩ := goWith_next h
       rename_i hneg hlim hin
       simp only [List.length_cons, List.length_nil] at hst ⊢
       refine ⟨by omega, ?_, by first | rfl | trivial, by omega, ?_⟩
       · first
         | exact hc
         | (have hlt : cells.length < L.maxCells := by
              by_cases hl : cells.length < L.maxCells
              · exact hl
              · exact absurd ⟨hin, by omega⟩ hlim
            omega)
       · intro j hj
         split
         · rename_i he
           subst he
           first
           | exact absurd hin hj
           | simp at hj
         · apply hz
           intro hk
           apply hj
           first
           | exact hk
           | simp [hk])

/-- One bounded step: all the invariants together. -/
theorem bstep_inv {P : List Instr} {L : Limits} {b b' : BState} (hP : (P.length : Int) ≤ i64Max)
    (hs : InRange b.core) (hw : Within L b) (h : bstep P L b = .next b') :
    InRange b'.core ∧ Within L b' ∧ b'.steps = b.steps + 1 ∧
      b'.cells.length ≤ b.cells.length + 1 := by
  unfold bstep at h
  split at h
  · cases h
  · rename_i hlim
    cases hi : P[b.core.pc]? with
    | none => simp [hi] at h
    | some i =>
      simp only [hi] at h
      have hpc : b.core.pc < P.length := by
        rcases List.getElem?_eq_some_iff.mp hi with ⟨hl, _⟩
        exact hl
      have hr := bexec_inRange (b := { b with steps := b.steps + 1 }) hP hs hpc h
      have hw' : Within L { b with steps := b.steps + 1 } :=
        ⟨by simp only; omega, hw.2.1, hw.2.2.1, hw.2.2.2⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := bexec_within hw' h
      simp only at h3 h4
      exact ⟨hr, ⟨by omega, h1, h2, h5⟩, h3, h4⟩

/-- `bexec` keeps the step counter. -/
theorem bexec_steps_counts {P : List Instr} {L : Limits} {b b' : BState} {i : Instr}
    (h : bexec P L b i = .next b') :
    b'.steps = b.steps ∧ b'.cells.length ≤ b.cells.length + 1 := by
  obtain ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ := b
  rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
    simp only [bexec, bArith, bCompare] at h <;>
    (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; exact ⟨rfl, Nat.le_succ _⟩)
    | (obtain ⟨nx, rfl⟩ := goWith_next h
       exact ⟨rfl, Nat.le_succ _⟩)
    | (obtain ⟨nx, rfl, _⟩ := goRoom_next h
       exact ⟨rfl, Nat.le_succ _⟩)
    | (obtain ⟨nx, rfl⟩ := goWith_next h
       exact ⟨rfl, Nat.le_refl _⟩)

theorem bstep_counts {P : List Instr} {L : Limits} {b b' : BState} (h : bstep P L b = .next b') :
    b'.steps = b.steps + 1 ∧ b'.cells.length ≤ b.cells.length + 1 := by
  unfold bstep at h
  split at h
  · cases h
  · cases hi : P[b.core.pc]? with
    | none => simp [hi] at h
    | some i =>
      simp only [hi] at h
      exact bexec_steps_counts h

/-- Under the limits and in range, the bounded step is the model's step. -/
theorem bstep_complete {P : List Instr} {L : Limits} {b : BState} {s' : State}
    (hP : (P.length : Int) ≤ i64Max) (hs : step P b.core = .next s')
    (hsteps : b.steps < L.maxSteps) (hst : b.core.stack.length < L.maxStack)
    (hc : b.cells.length < L.maxCells) (hv : ∀ v ∈ s'.stack, InI64 v) :
    ∃ b', bstep P L b = .next b' ∧ b'.core = s' := by
  have hr := bstep_ref hP L b
  rw [hs] at hr
  cases ho : bstep P L b with
  | next b' =>
    rw [ho] at hr
    exact ⟨b', rfl, (Outcome.next.inj hr).symm⟩
  | halt b' =>
    rw [ho] at hr
    cases hr
  | fault f =>
    exfalso
    rw [ho] at hr
    unfold bstep at ho
    rw [ite_eq_right (by omega)] at ho
    cases hi : P[b.core.pc]? with
    | none => simp [hi] at ho; subst ho; cases hr
    | some i =>
      simp only [hi] at ho
      simp only [step, hi] at hs
      cases f with
      | model f => cases hr
      | overflow =>
        obtain ⟨v, hin, hn⟩ := bexec_overflow (b := { b with steps := b.steps + 1 }) ho hs
        exact hn (hv v hin)
      | stepLimit =>
        obtain ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ := b
        rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
          simp only [bexec, bArith, bCompare] at ho <;>
          (repeat' split at ho) <;>
          first
          | (cases ho; done)
          | (have := goWith_fault ho; cases this; done)
          | (have := goRoom_fault ho; simp at this; done)
      | stackLimit =>
        have := bexec_stackLimit (b := { b with steps := b.steps + 1 }) ho
        simp only at this
        omega
      | memoryLimit =>
        have := bexec_memoryLimit (b := { b with steps := b.steps + 1 }) ho
        simp only at this
        omega

/-! ## Whole runs -/

/-- A whole bounded run refines the model's run at the same fuel. -/
theorem brun_ref {P : List Instr} (hP : (P.length : Int) ≤ i64Max) (L : Limits) (n : Nat)
    (b : BState) : Ref (brun P L n b) (run P n b.core) := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [brun, run]
    have hr := bstep_ref hP L b
    cases ho : bstep P L b with
    | next b' =>
      rw [ho] at hr
      have hr' : step P b.core = .next b'.core := hr
      simp only [hr']
      exact ih b'
    | halt b' =>
      rw [ho] at hr
      have hr' : step P b.core = .halt b'.core := hr
      simp only [hr']
      rfl
    | fault f =>
      rw [ho] at hr
      cases f with
      | model f =>
        have hr' : step P b.core = .fault f := hr
        simp only [hr']
        rfl
      | overflow => trivial
      | stepLimit => trivial
      | stackLimit => trivial
      | memoryLimit => trivial

/-- A fault of the implementation, not of the model. -/
def BFault.isLimit : BFault → Prop
  | .model _ => False
  | _ => True

/-- A run stopped by an implementation fault agrees with the model up to that step. -/
theorem brun_limit_prefix {P : List Instr} (hP : (P.length : Int) ≤ i64Max) {L : Limits} {n : Nat}
    {b : BState} {f : BFault} (h : brun P L n b = .fault f) (hf : f.isLimit) :
    ∃ k b', k < n ∧ brun P L k b = .next b' ∧ run P k b.core = .next b'.core ∧
      bstep P L b' = .fault f := by
  induction n generalizing b with
  | zero => cases h
  | succ n ih =>
    simp only [brun] at h
    cases ho : bstep P L b with
    | next b₁ =>
      rw [ho] at h
      obtain ⟨k, b', hk, h1, h2, h3⟩ := ih h
      have hr : step P b.core = .next b₁.core := by
        have := bstep_ref hP L b
        rwa [ho] at this
      refine ⟨k + 1, b', by omega, ?_, ?_, h3⟩
      · simp only [brun, ho]
        exact h1
      · simp only [run, hr]
        exact h2
    | halt b₁ =>
      rw [ho] at h
      cases h
    | fault g =>
      rw [ho] at h
      cases h
      exact ⟨0, b, by omega, rfl, rfl, ho⟩

/-- Values stay in 64 bits and the limits hold along any bounded run. -/
theorem brun_inv {P : List Instr} {L : Limits} (hP : (P.length : Int) ≤ i64Max) {n : Nat}
    {b b' : BState} (hs : InRange b.core) (hw : Within L b) (h : brun P L n b = .next b') :
    InRange b'.core ∧ Within L b' := by
  induction n generalizing b with
  | zero =>
    cases h
    exact ⟨hs, hw⟩
  | succ n ih =>
    simp only [brun] at h
    cases ho : bstep P L b with
    | next b₁ =>
      rw [ho] at h
      obtain ⟨h1, h2, _⟩ := bstep_inv hP hs hw ho
      exact ih h1 h2 h
    | halt b₁ =>
      rw [ho] at h
      cases h
    | fault g =>
      rw [ho] at h
      cases h

/-- While a model run stays under the limits and in 64 bits, the bounded run is the same run. -/
theorem brun_complete {P : List Instr} {L : Limits} (hP : (P.length : Int) ≤ i64Max) {n : Nat}
    {b : BState} (hsteps : b.steps + n ≤ L.maxSteps) (hcells : b.cells.length + n ≤ L.maxCells)
    (hst : ∀ k t, k < n → run P k b.core = .next t → t.stack.length < L.maxStack)
    (hv : ∀ k t, k ≤ n → run P k b.core = .next t → ∀ v ∈ t.stack, InI64 v) :
    (∀ s', run P n b.core = .next s' → ∃ b', brun P L n b = .next b' ∧ b'.core = s') ∧
    (∀ s', run P n b.core = .halt s' → ∃ b', brun P L n b = .halt b' ∧ b'.core = s') := by
  induction n generalizing b with
  | zero =>
    refine ⟨fun s' h => ⟨b, rfl, ?_⟩, fun s' h => (by cases h)⟩
    cases h
    rfl
  | succ n ih =>
    simp only [run]
    cases hs : step P b.core with
    | next s₁ =>
      have hv₁ : ∀ v ∈ s₁.stack, InI64 v :=
        hv 1 s₁ (by omega) (by simp only [run, hs])
      obtain ⟨b₁, hb₁, hcore⟩ := bstep_complete hP hs (by omega)
        (hst 0 _ (by omega) rfl) (by omega) hv₁
      obtain ⟨h1, h2⟩ := bstep_counts hb₁
      subst hcore
      have := ih (b := b₁) (by omega) (by omega)
        (fun k t hk ht => hst (k + 1) t (by omega) (by simp only [run, hs]; exact ht))
        (fun k t hk ht => hv (k + 1) t (by omega) (by simp only [run, hs]; exact ht))
      simp only [brun, hb₁]
      exact this
    | halt s₁ =>
      refine ⟨fun s' h => (by cases h), fun s' h => ?_⟩
      cases h
      have hr := bstep_ref hP L b
      unfold step at hs
      cases hi : P[b.core.pc]? with
      | none => simp [hi] at hs
      | some i =>
        rw [hi] at hs
        have hhalt : i = .halt := by
          obtain ⟨⟨pc, st, m, inp, out⟩, steps, cells⟩ := b
          rcases st with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩ <;> rcases inp with _ | ⟨d, inp⟩ <;> cases i <;>
            first
            | rfl
            | (simp only [exec, binary, divLike, advance, jumpTo] at hs
               repeat' split at hs
               all_goals cases hs)
        subst hhalt
        have e : s₁ = b.core := by
          simp only [exec] at hs
          exact (Outcome.halt.inj hs).symm
        refine ⟨{ b with steps := b.steps + 1 }, ?_, e.symm⟩
        simp only [brun, bstep]
        rw [ite_eq_right (by omega)]
        simp only [hi, bexec]
    | fault f => exact ⟨fun s' h => (by cases h), fun s' h => (by cases h)⟩

/-- Started from `init`: a run that halts or stays alive in the bounded machine is the model's run,
with every value in 64 bits, as long as the input is bytes. -/
theorem bounded_init {P : List Instr} {L : Limits} (hP : (P.length : Int) ≤ i64Max) {n : Nat}
    {input : List Nat} (hin : ∀ x ∈ input, x ≤ 255) {b' : BState}
    (h : brun P L n (BState.init input) = .next b') :
    run P n (State.init input) = .next b'.core ∧ InRange b'.core ∧ Within L b' := by
  have hr := brun_ref hP L n (BState.init input)
  rw [h] at hr
  refine ⟨hr, brun_inv hP ?_ ?_ h⟩
  · refine ⟨by simp [BState.init, State.init], fun _ => ?_, hin⟩
    simp only [BState.init, State.init, InI64, i64Min, i64Max]
    omega
  · exact ⟨Nat.zero_le _, by simp [BState.init, State.init], by simp [BState.init],
      fun _ _ => rfl⟩

end Emd

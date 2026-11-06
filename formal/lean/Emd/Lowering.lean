import Emd.Universal
import Emd.Properties

/-! # Lowering: a mirror of the blocks of `codegen.rs`; proofs are about the mirror, not the Rust. -/

namespace Emd

/-! ## The mirror -/

/-- Mirror of `push_magnitude`. -/
def pushMag (n : Nat) : List Instr :=
  if h : n < 8 then [.push ⟨n, h⟩]
  else
    pushMag (n / 7) ++ [.push 7, .mul] ++
      if h7 : n % 7 = 0 then [] else [.push ⟨n % 7, by omega⟩, .add]
decreasing_by omega

/-- Mirror of `push_int`. -/
def pushInt (value : Int) : List Instr :=
  if value < 0 then [.push 0] ++ pushMag value.natAbs ++ [.sub] else pushMag value.natAbs

/-- The `for` loop of `padding`. -/
def padPairs : Nat → List Instr
  | 0 => []
  | k + 1 => [.push 0, .add] ++ padPairs k

/-- Mirror of `padding`. -/
def padding (extra : Nat) : List Instr := padPairs (extra / 2)

/-- The shape of a lowered jump: the offset, its no-ops, then the jump. -/
def loweredJump (j : Instr) (off : Int) (e : Nat) : List Instr :=
  pushInt off ++ padding e ++ [j]

/-! ## Constants -/

theorem seq_nil (st : List Int) (m : Nat → Int) : Seq [] st m st m :=
  fun _ _ _ _ _ _ => rfl

theorem seq_pushMag (n : Nat) (st : List Int) (m : Nat → Int) :
    Seq (pushMag n) st m ((n : Int) :: st) m := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [pushMag]
    by_cases h : n < 8
    · rw [dite_eq_left h]
      exact seq_push n h st m
    · rw [dite_eq_right h]
      have q := (ih (n / 7) (by omega)).append
        ((seq_push 7 (by omega) _ m).append (seq_mul _ _ _ m))
      by_cases h7 : n % 7 = 0
      · rw [dite_eq_left h7, List.append_nil]
        have e : ((n / 7 : Nat) : Int) * ((7 : Nat) : Int) = (n : Int) := by omega
        rw [e] at q
        exact q
      · rw [dite_eq_right h7]
        have q2 := q.append ((seq_push (n % 7) (by omega) _ m).append (seq_add _ _ _ m))
        have e : ((n / 7 : Nat) : Int) * ((7 : Nat) : Int) + ((n % 7 : Nat) : Int) = (n : Int) := by
          omega
        rw [e] at q2
        exact q2

theorem seq_pushInt (n : Int) (st : List Int) (m : Nat → Int) :
    Seq (pushInt n) st m (n :: st) m := by
  rw [pushInt]
  by_cases h : n < 0
  · rw [ite_eq_left h]
    have q := ((seq_push 0 (by omega) st m).append (seq_pushMag n.natAbs _ m)).append
      (seq_sub _ _ _ m)
    have e : ((0 : Nat) : Int) - ((n.natAbs : Nat) : Int) = n := by omega
    rw [e] at q
    exact q
  · rw [ite_eq_right h]
    have q := seq_pushMag n.natAbs st m
    have e : ((n.natAbs : Nat) : Int) = n := by omega
    rw [e] at q
    exact q

-- `Seq` asks `At` plus a bound; this is the same fact for a literal `pre ++ l ++ post`.
theorem Seq.embed {l : List Instr} {st st' : List Int} {m m' : Nat → Int}
    (h : Seq l st m st' m') (pre post : List Instr) (hpost : post ≠ []) (i o : List Nat) :
    run (pre ++ l ++ post) l.length ⟨pre.length, st, m, i, o⟩ =
      .next ⟨pre.length + l.length, st', m', i, o⟩ := by
  have hp : 0 < post.length := List.length_pos_iff.mpr hpost
  exact h _ _ i o ⟨pre, post, by simp, rfl⟩ (by simp; omega)

/-- Item 1: in any embedding the block pushes `n`, leaving memory, input and output alone. -/
theorem pushInt_correct (n : Int) (pre post : List Instr) (hpost : post ≠ []) (st : List Int)
    (m : Nat → Int) (i o : List Nat) :
    run (pre ++ pushInt n ++ post) (pushInt n).length ⟨pre.length, st, m, i, o⟩ =
      .next ⟨pre.length + (pushInt n).length, n :: st, m, i, o⟩ :=
  (seq_pushInt n st m).embed pre post hpost i o

-- Slots start at 0 and grow to such a length, so `slot - need` is even and `padding` covers it.
theorem pushMag_length_odd (n : Nat) : (pushMag n).length % 2 = 1 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [pushMag]
    by_cases h : n < 8
    · simp [h]
    · have := ih (n / 7) (by omega)
      by_cases h7 : n % 7 = 0
      · simp [h, h7]
        omega
      · simp [h, h7]
        omega

theorem pushInt_length_odd (n : Int) : (pushInt n).length % 2 = 1 := by
  have := pushMag_length_odd n.natAbs
  rw [pushInt]
  by_cases h : n < 0
  · simp [h]
    omega
  · simp [h]
    omega

/-! ## Padding -/

theorem seq_padPairs (k : Nat) (v : Int) (st : List Int) (m : Nat → Int) :
    Seq (padPairs k) (v :: st) m (v :: st) m := by
  induction k with
  | zero => exact seq_nil _ m
  | succ k ih =>
    have q := (seq_push 0 (by omega) (v :: st) m).append (seq_add _ _ _ m)
    have e : v + ((0 : Nat) : Int) = v := by omega
    rw [e] at q
    exact q.append ih

-- True for odd `extra` too, but the block is then shorter: the hypothesis belongs to `padding_length`.
theorem seq_padding (extra : Nat) (v : Int) (st : List Int) (m : Nat → Int) :
    Seq (padding extra) (v :: st) m (v :: st) m :=
  seq_padPairs _ v st m

theorem padPairs_length (k : Nat) : (padPairs k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [padPairs, ih]; omega

theorem padding_length (extra : Nat) (hextra : extra % 2 = 0) : (padding extra).length = extra := by
  rw [padding, padPairs_length]
  omega

/-- Item 2: for even `extra`, the block keeps the stack and moves `pc` just after itself. -/
theorem padding_correct (extra : Nat) (hextra : extra % 2 = 0) (pre post : List Instr)
    (hpost : post ≠ []) (v : Int) (st : List Int) (m : Nat → Int) (i o : List Nat) :
    run (pre ++ padding extra ++ post) extra ⟨pre.length, v :: st, m, i, o⟩ =
      .next ⟨pre.length + extra, v :: st, m, i, o⟩ := by
  have q := (seq_padding extra v st m).embed pre post hpost i o
  rw [padding_length extra hextra] at q
  exact q

/-- `padding` skips `extra = 1` of necessity: no single instruction is such a no-op. -/
theorem no_single_noop (x : Instr) :
    ¬ ∀ (v : Int) (st : List Int) (m : Nat → Int), Seq [x] (v :: st) m (v :: st) m := by
  intro h
  have q := h 5 [] (fun _ => 1) [x, .halt] 0 [] [] ⟨[], [.halt], rfl, rfl⟩ (by simp)
  cases x <;>
    simp [run, step, exec, binary, divLike, advance, jumpTo, b2i] at q

/-! ## Lowered jumps -/

theorem loweredJump_length (j : Instr) (off : Int) (e : Nat) (he : e % 2 = 0) :
    (loweredJump j off e).length = (pushInt off).length + e + 1 := by
  simp [loweredJump, padding_length e he]
  omega

theorem seq_jnz_fall (off : Int) (r : List Int) (m : Nat → Int) :
    Seq [.jnz] (off :: 0 :: r) m r m := by
  refine seq_single fun P a i o h => ?_
  simp only [exec]
  rw [ite_eq_right (fun hc => hc rfl)]
  exact advance_ok h

theorem seq_slot (off : Int) (e : Nat) (st : List Int) (m : Nat → Int) :
    Seq (pushInt off ++ padding e) st m (off :: st) m :=
  (seq_pushInt off st m).append (seq_padding e off st m)

-- The fixed point's only duty: `off` must reach `target` from the jump's own index.
theorem jumpTo_target {P : List Instr} {s : State} {x : Int} {target : Nat}
    (hx : x = (target : Int)) (ht : target < P.length) :
    jumpTo P s x = .next { s with pc := target } := by
  subst hx
  have h0 : (0 : Int) ≤ (target : Int) := by omega
  have h1 : (target : Int) < (P.length : Int) := by omega
  simp only [jumpTo]
  rw [ite_eq_left ⟨h0, h1⟩, Int.toNat_natCast]

-- Reaches the jump instruction with the offset on top, whatever comes after the block.
theorem lowered_prefix {P : List Instr} {a : Nat} {j : Instr} {off : Int} {e : Nat} (he : e % 2 = 0)
    (hAt : At P a (loweredJump j off e)) (st : List Int) (m : Nat → Int) (i o : List Nat) :
    P[a + ((pushInt off).length + e)]? = some j ∧
    run P ((pushInt off).length + e) ⟨a, st, m, i, o⟩ =
      .next ⟨a + ((pushInt off).length + e), off :: st, m, i, o⟩ := by
  have hlen : (pushInt off ++ padding e).length = (pushInt off).length + e := by
    simp [padding_length e he]
  have hx : At P (a + (pushInt off ++ padding e).length) [j] := At.right hAt
  rw [hlen] at hx
  have hb : a + ((pushInt off).length + e) < P.length := by
    obtain ⟨pre, suf, h1, h2⟩ := hx
    subst h1
    simp
    omega
  have q := seq_slot off e st m P a i o hAt.left (by rw [hlen]; exact hb)
  rw [hlen] at q
  exact ⟨hx.head, q⟩

/-- Item 3, `jmp`: control reaches `target`, wherever it is, and the stack is untouched. -/
theorem lowered_jmp {P : List Instr} {a target : Nat} {off : Int} {e : Nat} (he : e % 2 = 0)
    (hAt : At P a (loweredJump .jmp off e)) (ht : target < P.length)
    (hoff : off = (target : Int) - ((a + (pushInt off).length + e : Nat) : Int))
    (st : List Int) (m : Nat → Int) (i o : List Nat) :
    run P (loweredJump .jmp off e).length ⟨a, st, m, i, o⟩ = .next ⟨target, st, m, i, o⟩ := by
  obtain ⟨hx, q⟩ := lowered_prefix he hAt st m i o
  rw [loweredJump_length _ _ _ he, run_add q]
  simp only [run, step, hx, exec]
  rw [jumpTo_target (by omega) ht]

/-- Item 3, `call`: control reaches `target` with the lowered address after the jump on the stack. -/
theorem lowered_call {P : List Instr} {a target : Nat} {off : Int} {e : Nat} (he : e % 2 = 0)
    (hAt : At P a (loweredJump .call off e)) (ht : target < P.length)
    (hoff : off = (target : Int) - ((a + (pushInt off).length + e : Nat) : Int))
    (st : List Int) (m : Nat → Int) (i o : List Nat) :
    run P (loweredJump .call off e).length ⟨a, st, m, i, o⟩ =
      .next ⟨target, ((a + (pushInt off).length + e + 1 : Nat) : Int) :: st, m, i, o⟩ := by
  obtain ⟨hx, q⟩ := lowered_prefix he hAt st m i o
  rw [loweredJump_length _ _ _ he, run_add q]
  simp only [run, step, hx, exec]
  rw [jumpTo_target (by omega) ht]
  have e1 : ((a + ((pushInt off).length + e) : Nat) : Int) + 1 =
      ((a + (pushInt off).length + e + 1 : Nat) : Int) := by omega
  simp only [e1]

/-- Item 3, `jz` taken: a zero condition goes to `target` and is consumed. -/
theorem lowered_jz_taken {P : List Instr} {a target : Nat} {off : Int} {e : Nat} (he : e % 2 = 0)
    (hAt : At P a (loweredJump .jz off e)) (ht : target < P.length)
    (hoff : off = (target : Int) - ((a + (pushInt off).length + e : Nat) : Int))
    (st : List Int) (m : Nat → Int) (i o : List Nat) :
    run P (loweredJump .jz off e).length ⟨a, 0 :: st, m, i, o⟩ = .next ⟨target, st, m, i, o⟩ := by
  obtain ⟨hx, q⟩ := lowered_prefix he hAt (0 :: st) m i o
  rw [loweredJump_length _ _ _ he, run_add q]
  simp only [run, step, hx, exec, ↓reduceIte]
  rw [jumpTo_target (by omega) ht]

/-- Item 3, `jz` not taken: a nonzero condition is consumed and control falls through. -/
theorem lowered_jz_fall {P : List Instr} {a : Nat} {off c : Int} {e : Nat}
    (hAt : At P a (loweredJump .jz off e)) (hc : c ≠ 0)
    (hb : a + (loweredJump .jz off e).length < P.length)
    (st : List Int) (m : Nat → Int) (i o : List Nat) :
    run P (loweredJump .jz off e).length ⟨a, c :: st, m, i, o⟩ =
      .next ⟨a + (loweredJump .jz off e).length, st, m, i, o⟩ :=
  ((seq_slot off e (c :: st) m).append (seq_jz_fall off c st m hc)) P a i o hAt hb

/-- Item 3, `jnz` taken: a nonzero condition goes to `target` and is consumed. -/
theorem lowered_jnz_taken {P : List Instr} {a target : Nat} {off c : Int} {e : Nat} (he : e % 2 = 0)
    (hAt : At P a (loweredJump .jnz off e)) (hc : c ≠ 0) (ht : target < P.length)
    (hoff : off = (target : Int) - ((a + (pushInt off).length + e : Nat) : Int))
    (st : List Int) (m : Nat → Int) (i o : List Nat) :
    run P (loweredJump .jnz off e).length ⟨a, c :: st, m, i, o⟩ = .next ⟨target, st, m, i, o⟩ := by
  obtain ⟨hx, q⟩ := lowered_prefix he hAt (c :: st) m i o
  rw [loweredJump_length _ _ _ he, run_add q]
  simp only [run, step, hx, exec]
  rw [ite_eq_left hc, jumpTo_target (by omega) ht]

/-- Item 3, `jnz` not taken: a zero condition is consumed and control falls through. -/
theorem lowered_jnz_fall {P : List Instr} {a : Nat} {off : Int} {e : Nat}
    (hAt : At P a (loweredJump .jnz off e))
    (hb : a + (loweredJump .jnz off e).length < P.length)
    (st : List Int) (m : Nat → Int) (i o : List Nat) :
    run P (loweredJump .jnz off e).length ⟨a, 0 :: st, m, i, o⟩ =
      .next ⟨a + (loweredJump .jnz off e).length, st, m, i, o⟩ :=
  ((seq_slot off e (0 :: st) m).append (seq_jnz_fall off st m)) P a i o hAt hb

-- The hypothesis on `off` can hold: a backward jump to 0 from a block at 0 with two no-ops.
example : (-5 : Int) = ((0 : Nat) : Int) - ((0 + (pushInt (-5)).length + 2 : Nat) : Int) := by
  simp [pushInt, pushMag]

/-! ## Item 4: a label-free statement language, with the slots given -/

inductive JumpKind where
  | jmp | jz | jnz | call
  deriving DecidableEq

def JumpKind.instr : JumpKind → Instr
  | .jmp => .jmp
  | .jz => .jz
  | .jnz => .jnz
  | .call => .call

/-- `Statement` without labels: `t` is a statement index and `slot` what the fixed point chose. -/
inductive Stmt where
  | plain (x : Instr)
  | pushI (n : Int)
  | jump (j : JumpKind) (t slot : Nat)
  deriving DecidableEq

def Stmt.len : Stmt → Nat
  | .plain _ => 1
  | .pushI n => (pushInt n).length
  | .jump _ _ slot => slot + 1

/-- The address of statement `i`, as the first loop of `generate` computes it. -/
def addrOf (prog : List Stmt) (i : Nat) : Nat := ((prog.take i).map Stmt.len).sum

/-- Mirror of `jump_offset`. -/
def jumpOffset (target start slot : Nat) : Int := (target : Int) - ((start + slot : Nat) : Int)

/-- One statement, as the last loop of `generate` emits it. -/
def lowerStmt (A : Nat → Nat) (i : Nat) : Stmt → List Instr
  | .plain x => [x]
  | .pushI n => pushInt n
  | .jump j t slot =>
    loweredJump j.instr (jumpOffset (A t) (A i) slot)
      (slot - (pushInt (jumpOffset (A t) (A i) slot)).length)

def lowerFrom (A : Nat → Nat) : Nat → List Stmt → List Instr
  | _, [] => []
  | i, s :: cs => lowerStmt A i s ++ lowerFrom A (i + 1) cs

def lower (prog : List Stmt) : List Instr := lowerFrom (addrOf prog) 0 prog

/-- What the fixed point guarantees for one statement. Raw jumps, with a computed offset, are left
out of `plain`; `ret` stays in, with `srcRet` as its source meaning. -/
def StmtOk (A : Nat → Nat) (i : Nat) : Stmt → Prop
  | .plain x => x ≠ .jmp ∧ x ≠ .jz ∧ x ≠ .jnz ∧ x ≠ .call
  | .pushI _ => True
  | .jump _ t slot =>
    (pushInt (jumpOffset (A t) (A i) slot)).length ≤ slot ∧
      (slot - (pushInt (jumpOffset (A t) (A i) slot)).length) % 2 = 0

def LayoutOk (prog : List Stmt) : Prop :=
  ∀ i s, prog[i]? = some s → StmtOk (addrOf prog) i s

-- `exec` reads a program only for its length here, so this gives the source machine its own range.
def srcRange (prog : List Stmt) : List Instr := List.replicate prog.length .halt

/-- The statement whose lowered address is `a`, if there is one. -/
def retTarget (prog : List Stmt) (a : Int) : Option Nat :=
  (List.range prog.length).find? fun j => (addrOf prog j : Int) = a

/-- Return addresses are lowered addresses on both sides, so the two stacks stay equal even if a
program computes with them: `call` pushes the lowered address of the next statement, and `ret`
goes to the statement at the lowered address it pops. An address inside a statement has no source
meaning: see `WildRet`. -/
def srcRet (prog : List Stmt) (c : State) : Outcome :=
  match c.stack with
  | a :: r =>
    match retTarget prog a with
    | some j => .next { c with pc := j, stack := r }
    | none => .fault .pcOutOfRange
  | [] => .fault .stackUnderflow

/-- The source machine: `pc` is a statement index and a jump goes to a statement. -/
def srcStep (prog : List Stmt) (c : State) : Outcome :=
  match prog[c.pc]? with
  | none => .fault .pcOutOfRange
  | some (.plain x) => if x = .ret then srcRet prog c else exec (srcRange prog) c x
  | some (.pushI n) => advance (srcRange prog) { c with stack := n :: c.stack }
  | some (.jump .jmp t _) => jumpTo (srcRange prog) c t
  | some (.jump .jz t _) =>
    match c.stack with
    | x :: r =>
      if x = 0 then jumpTo (srcRange prog) { c with stack := r } t
      else advance (srcRange prog) { c with stack := r }
    | [] => .fault .stackUnderflow
  | some (.jump .jnz t _) =>
    match c.stack with
    | x :: r =>
      if x ≠ 0 then jumpTo (srcRange prog) { c with stack := r } t
      else advance (srcRange prog) { c with stack := r }
    | [] => .fault .stackUnderflow
  | some (.jump .call t _) =>
    jumpTo (srcRange prog) { c with stack := (addrOf prog (c.pc + 1) : Int) :: c.stack } t

def srcRun (prog : List Stmt) : Nat → State → Outcome
  | 0, c => .next c
  | n + 1, c =>
    match srcStep prog c with
    | .next c' => srcRun prog n c'
    | o => o

/-- A source state seen on the target: only `pc` differs. -/
def toTarget (prog : List Stmt) (c : State) : State := { c with pc := addrOf prog c.pc }

theorem pushMag_length_pos (n : Nat) : 0 < (pushMag n).length := by
  rw [pushMag]
  by_cases h : n < 8
  · simp [h]
  · simp [h]
    omega

theorem pushInt_length_pos (n : Int) : 0 < (pushInt n).length := by
  rw [pushInt]
  have := pushMag_length_pos n.natAbs
  by_cases h : n < 0
  · simp [h]
  · simp [h]
    omega

theorem Stmt.len_pos (s : Stmt) : 0 < s.len := by
  cases s with
  | plain x => simp [Stmt.len]
  | pushI n => exact pushInt_length_pos n
  | jump j t slot => simp [Stmt.len]

theorem lowerStmt_length {A : Nat → Nat} {i : Nat} {s : Stmt} (h : StmtOk A i s) :
    (lowerStmt A i s).length = s.len := by
  cases s with
  | plain x => rfl
  | pushI n => rfl
  | jump j t slot =>
    obtain ⟨h1, h2⟩ := h
    simp only [lowerStmt, Stmt.len]
    rw [loweredJump_length _ _ _ h2]
    omega

theorem lowerFrom_at (A : Nat → Nat) (cs : List Stmt) (b j : Nat) (s : Stmt)
    (h : cs[j]? = some s) (ok : ∀ k s', cs[k]? = some s' → StmtOk A (b + k) s') :
    ∃ pre suf, lowerFrom A b cs = pre ++ (lowerStmt A (b + j) s ++ suf) ∧
      pre.length = ((cs.take j).map Stmt.len).sum := by
  induction cs generalizing b j with
  | nil => simp at h
  | cons x cs ih =>
    cases j with
    | zero =>
      have : x = s := by simpa using h
      subst this
      exact ⟨[], lowerFrom A (b + 1) cs, by simp [lowerFrom], by simp⟩
    | succ j =>
      have ok' : ∀ k s', cs[k]? = some s' → StmtOk A (b + 1 + k) s' := by
        intro k s' hk
        have := ok (k + 1) s' (by simpa using hk)
        rwa [show b + (k + 1) = b + 1 + k by omega] at this
      obtain ⟨pre, suf, e, hl⟩ := ih (b + 1) j (by simpa using h) ok'
      have hx : StmtOk A b x := ok 0 x (by simp)
      refine ⟨lowerStmt A b x ++ pre, suf, ?_, ?_⟩
      · simp only [lowerFrom, e, show b + (j + 1) = b + 1 + j by omega, List.append_assoc]
      · simp only [List.length_append, lowerStmt_length hx, hl, List.take_succ_cons, List.map_cons,
          List.sum_cons]

theorem lower_at {prog : List Stmt} (ok : LayoutOk prog) {j : Nat} {s : Stmt}
    (h : prog[j]? = some s) : At (lower prog) (addrOf prog j) (lowerStmt (addrOf prog) j s) := by
  obtain ⟨pre, suf, e, hl⟩ := lowerFrom_at (addrOf prog) prog 0 j s h
    (fun k s' hk => by rw [Nat.zero_add]; exact ok k s' hk)
  rw [Nat.zero_add] at e
  exact ⟨pre, suf, e, hl⟩

theorem addrOf_succ {prog : List Stmt} {j : Nat} {s : Stmt} (h : prog[j]? = some s) :
    addrOf prog (j + 1) = addrOf prog j + s.len := by
  simp [addrOf, List.take_add_one, h]

theorem addr_lt_of_lt {prog : List Stmt} (ok : LayoutOk prog) {j : Nat} (hj : j < prog.length) :
    addrOf prog j < (lower prog).length := by
  obtain ⟨s, hs⟩ : ∃ s, prog[j]? = some s := ⟨prog[j], List.getElem?_eq_getElem hj⟩
  obtain ⟨pre, suf, e, hl⟩ := lower_at ok hs
  have hp := Stmt.len_pos s
  have hq := lowerStmt_length (ok j s hs)
  rw [e]
  simp
  omega

theorem srcRange_length (prog : List Stmt) : (srcRange prog).length = prog.length := by
  simp [srcRange]

theorem retTarget_some {prog : List Stmt} {a : Int} {j : Nat} (h : retTarget prog a = some j) :
    j < prog.length ∧ (addrOf prog j : Int) = a := by
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simpa using And.intro h1 h2

theorem retTarget_none {prog : List Stmt} {a : Int} (h : retTarget prog a = none) {j : Nat}
    (hj : j < prog.length) : (addrOf prog j : Int) ≠ a := by
  have := List.find?_eq_none.mp h j (by simpa using hj)
  simpa using this

theorem advance_inv {D : List Instr} {t s' : State} (h : advance D t = .next s') :
    t.pc + 1 < D.length ∧ s' = { t with pc := t.pc + 1 } := by
  unfold advance jumpTo at h
  split at h
  · rename_i hc
    have e : ((t.pc : Int) + 1).toNat = t.pc + 1 := by omega
    rw [e] at h
    exact ⟨by omega, (Outcome.next.inj h).symm⟩
  · cases h

theorem jumpTo_inv {D : List Instr} {t s' : State} {x : Nat} (h : jumpTo D t x = .next s') :
    x < D.length ∧ s' = { t with pc := x } := by
  unfold jumpTo at h
  split at h
  · rename_i hc
    rw [Int.toNat_natCast] at h
    exact ⟨by omega, (Outcome.next.inj h).symm⟩
  · cases h

theorem plain_adv {D : List Instr} {t s' : State} (h : advance D t = .next s') :
    t.pc + 1 < D.length ∧ s'.pc = t.pc + 1 ∧ ∀ (P : List Instr) (a : Nat), a + 1 < P.length →
      advance P { t with pc := a } = .next { s' with pc := a + 1 } := by
  obtain ⟨h1, h2⟩ := advance_inv h
  subst h2
  exact ⟨h1, rfl, fun _ _ h => advance_ok h⟩

-- A non-jump reads the program only through the `advance` it ends with.
theorem exec_plain {D : List Instr} {x : Instr} {pc : Nat} {st : List Int} {m : Nat → Int}
    {i o : List Nat} {s' : State} (hx : x ≠ .jmp ∧ x ≠ .jz ∧ x ≠ .jnz ∧ x ≠ .call ∧ x ≠ .ret)
    (h : exec D ⟨pc, st, m, i, o⟩ x = .next s') :
    pc + 1 < D.length ∧ s'.pc = pc + 1 ∧ ∀ (P : List Instr) (a : Nat), a + 1 < P.length →
      exec P ⟨a, st, m, i, o⟩ x = .next { s' with pc := a + 1 } := by
  rcases st with _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩ <;> rcases i with _ | ⟨d, i⟩ <;> cases x <;>
    first
    | (exfalso; simp at hx; done)
    | (simp only [exec, binary, divLike] at h ⊢
       first
       | (cases h; done)
       | exact plain_adv h
       | (split at h <;> first
          | (cases h; done)
          | (rename_i hc; simp only [hc, ↓reduceIte]; exact plain_adv h)))

theorem exec_halt {D : List Instr} {x : Instr} {s s' : State}
    (h : exec D s x = .halt s') : x = .halt ∧ s' = s := by
  have adv : ∀ t, advance D t ≠ .halt s' := by
    intro t ht
    unfold advance jumpTo at ht
    split at ht <;> cases ht
  have jmp : ∀ t y, jumpTo D t y ≠ .halt s' := by
    intro t y ht
    unfold jumpTo at ht
    split at ht <;> cases ht
  obtain ⟨pc, st, m, i, o⟩ := s
  rcases st with _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩ <;> rcases i with _ | ⟨d, i⟩ <;> cases x <;>
    simp only [exec, binary, divLike] at h <;>
    first
    | (cases h; done)
    | (cases h; exact ⟨rfl, rfl⟩)
    | exact absurd h (adv _)
    | exact absurd h (jmp _ _)
    | (split at h <;> first
       | (cases h; done)
       | exact absurd h (adv _)
       | exact absurd h (jmp _ _))

/-- One source step is matched by at least one target step, in the same relation. -/
theorem lower_step {prog : List Stmt} (ok : LayoutOk prog) {c c' : State}
    (hs : srcStep prog c = .next c') :
    ∃ k, 0 < k ∧ run (lower prog) k (toTarget prog c) = .next (toTarget prog c') := by
  obtain ⟨pc, st, m, i, o⟩ := c
  unfold srcStep at hs
  simp only at hs
  cases hi : prog[pc]? with
  | none => simp [hi] at hs
  | some s =>
    have hat := lower_at ok hi
    have hsok := ok pc s hi
    have hnext := addrOf_succ hi
    have hin : ∀ {q}, q < prog.length → addrOf prog q < (lower prog).length :=
      addr_lt_of_lt ok
    have hR := srcRange_length prog
    rw [hi] at hs
    cases s with
    | plain x =>
      by_cases hret : x = .ret
      · subst hret
        simp only [↓reduceIte, srcRet] at hs
        rcases st with _ | ⟨a, r⟩
        · cases hs
        · simp only at hs
          cases hrt : retTarget prog a with
          | none => simp [hrt] at hs
          | some j =>
            simp only [hrt] at hs
            obtain ⟨hj, haj⟩ := retTarget_some hrt
            have ht := hin (q := j) hj
            have hc' := (Outcome.next.inj hs).symm
            subst hc'
            refine ⟨1, by omega, ?_⟩
            simp only [run, step, toTarget,
              (show (lower prog)[addrOf prog pc]? = some Instr.ret from hat.head), exec]
            rw [jumpTo_target haj.symm ht]
      simp only [hret, ↓reduceIte] at hs
      obtain ⟨hb, hpc, hex⟩ := exec_plain ⟨hsok.1, hsok.2.1, hsok.2.2.1, hsok.2.2.2, hret⟩ hs
      have hb' := hin (q := pc + 1) (by omega)
      have hl : addrOf prog (pc + 1) = addrOf prog pc + 1 := hnext
      refine ⟨1, by omega, ?_⟩
      have hstep : step (lower prog) ⟨addrOf prog pc, st, m, i, o⟩ =
          .next { c' with pc := addrOf prog pc + 1 } := by
        simp only [step, (show (lower prog)[addrOf prog pc]? = some x from hat.head)]
        exact hex _ _ (by omega)
      simp only [run, toTarget, hstep, hpc, hl]
    | pushI n =>
      obtain ⟨hb, hc'⟩ := advance_inv hs
      subst hc'
      have hb' := hin (q := pc + 1) (by simp only at hb; omega)
      have hl : addrOf prog (pc + 1) = addrOf prog pc + (pushInt n).length := hnext
      refine ⟨(pushInt n).length, pushInt_length_pos n, ?_⟩
      have q := seq_pushInt n st m (lower prog) _ i o hat (by simpa [lowerStmt, hl] using hb')
      simpa [toTarget, hl] using q
    | jump j t slot =>
      obtain ⟨hle, hne⟩ := hsok
      have hlen : (loweredJump j.instr (jumpOffset (addrOf prog t) (addrOf prog pc) slot)
          (slot - (pushInt (jumpOffset (addrOf prog t) (addrOf prog pc) slot)).length)).length =
          slot + 1 := by
        rw [loweredJump_length _ _ _ hne]
        omega
      have hl : addrOf prog (pc + 1) = addrOf prog pc + (slot + 1) := hnext
      have hoff : jumpOffset (addrOf prog t) (addrOf prog pc) slot = (addrOf prog t : Int) -
          ((addrOf prog pc + (pushInt (jumpOffset (addrOf prog t) (addrOf prog pc) slot)).length +
            (slot - (pushInt (jumpOffset (addrOf prog t) (addrOf prog pc) slot)).length) : Nat) :
            Int) := by
        have e : addrOf prog pc +
            (pushInt (jumpOffset (addrOf prog t) (addrOf prog pc) slot)).length +
            (slot - (pushInt (jumpOffset (addrOf prog t) (addrOf prog pc) slot)).length) =
            addrOf prog pc + slot := by omega
        rw [e]
        rfl
      cases j with
      | jmp =>
        obtain ⟨hb, hc'⟩ := jumpTo_inv hs
        subst hc'
        have ht := hin (q := t) (by omega)
        refine ⟨_, ?_, lowered_jmp hne hat ht hoff st m i o⟩
        rw [show JumpKind.jmp.instr = Instr.jmp from rfl] at hlen
        omega
      | jz =>
        rcases st with _ | ⟨x, r⟩
        · simp at hs
        · simp only at hs
          by_cases hx : x = 0
          · subst hx
            simp only [↓reduceIte] at hs
            obtain ⟨hb, hc'⟩ := jumpTo_inv hs
            subst hc'
            have ht := hin (q := t) (by omega)
            refine ⟨_, ?_, lowered_jz_taken hne hat ht hoff r m i o⟩
            rw [show JumpKind.jz.instr = Instr.jz from rfl] at hlen
            omega
          · rw [ite_eq_right hx] at hs
            obtain ⟨hb, hc'⟩ := advance_inv hs
            subst hc'
            have hb' := hin (q := pc + 1) (by simp only at hb; omega)
            rw [show JumpKind.jz.instr = Instr.jz from rfl] at hlen
            have q := lowered_jz_fall hat hx (by rw [hlen]; omega) r m i o
            rw [hlen] at q
            refine ⟨slot + 1, by omega, ?_⟩
            simpa [toTarget, hl] using q
      | jnz =>
        rcases st with _ | ⟨x, r⟩
        · simp at hs
        · simp only at hs
          by_cases hx : x = 0
          · subst hx
            simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hs
            obtain ⟨hb, hc'⟩ := advance_inv hs
            subst hc'
            have hb' := hin (q := pc + 1) (by simp only at hb; omega)
            rw [show JumpKind.jnz.instr = Instr.jnz from rfl] at hlen
            have q := lowered_jnz_fall hat (by rw [hlen]; omega) r m i o
            rw [hlen] at q
            refine ⟨slot + 1, by omega, ?_⟩
            simpa [toTarget, hl] using q
          · rw [ite_eq_left hx] at hs
            obtain ⟨hb, hc'⟩ := jumpTo_inv hs
            subst hc'
            have ht := hin (q := t) (by omega)
            refine ⟨_, ?_, lowered_jnz_taken hne hat hx ht hoff r m i o⟩
            rw [show JumpKind.jnz.instr = Instr.jnz from rfl] at hlen
            omega
      | call =>
        obtain ⟨hb, hc'⟩ := jumpTo_inv hs
        subst hc'
        have ht := hin (q := t) (by omega)
        have q := lowered_call hne hat ht hoff st m i o
        have e1 : addrOf prog pc +
            (pushInt (jumpOffset (addrOf prog t) (addrOf prog pc) slot)).length +
            (slot - (pushInt (jumpOffset (addrOf prog t) (addrOf prog pc) slot)).length) + 1 =
            addrOf prog (pc + 1) := by omega
        rw [e1] at q
        refine ⟨_, ?_, q⟩
        rw [show JumpKind.call.instr = Instr.call from rfl] at hlen
        omega

theorem lower_halt {prog : List Stmt} (ok : LayoutOk prog) {c c' : State}
    (hs : srcStep prog c = .halt c') :
    step (lower prog) (toTarget prog c) = .halt (toTarget prog c') := by
  have adv : ∀ {t}, advance (srcRange prog) t ≠ .halt c' := by
    intro t ht
    unfold advance jumpTo at ht
    split at ht <;> cases ht
  have jmp : ∀ {t y}, jumpTo (srcRange prog) t y ≠ .halt c' := by
    intro t y ht
    unfold jumpTo at ht
    split at ht <;> cases ht
  have ret : srcRet prog c ≠ .halt c' := by
    unfold srcRet
    split
    · split <;> simp
    · simp
  unfold srcStep at hs
  cases hi : prog[c.pc]? with
  | none => simp [hi] at hs
  | some s =>
    rw [hi] at hs
    cases s with
    | plain x =>
      by_cases hret : x = .ret
      · subst hret
        simp only [↓reduceIte] at hs
        exact absurd hs ret
      simp only [hret, ↓reduceIte] at hs
      obtain ⟨rfl, e⟩ := exec_halt hs
      rw [e]
      simp only [step, toTarget]
      rw [show (lower prog)[addrOf prog c.pc]? = some Instr.halt from (lower_at ok hi).head]
      rfl
    | pushI n => exact absurd hs adv
    | jump j t slot =>
      cases j with
      | jmp => exact absurd hs jmp
      | jz =>
        simp only at hs
        split at hs
        · split at hs
          · exact absurd hs jmp
          · exact absurd hs adv
        · cases hs
      | jnz =>
        simp only at hs
        split at hs
        · split at hs
          · exact absurd hs jmp
          · exact absurd hs adv
        · cases hs
      | call => exact absurd hs jmp

/-- Every source run that is alive or halted is matched on the target. -/
theorem lower_run {prog : List Stmt} (ok : LayoutOk prog) (n : Nat) {c c' : State} :
    (srcRun prog n c = .next c' →
      ∃ k, run (lower prog) k (toTarget prog c) = .next (toTarget prog c')) ∧
    (srcRun prog n c = .halt c' →
      ∃ k, run (lower prog) k (toTarget prog c) = .halt (toTarget prog c')) := by
  induction n generalizing c with
  | zero =>
    simp only [srcRun, Outcome.next.injEq, reduceCtorEq, false_implies, and_true]
    intro h
    subst h
    exact ⟨0, rfl⟩
  | succ n ih =>
    simp only [srcRun]
    cases hs : srcStep prog c with
    | next c₁ =>
      obtain ⟨k, _, h₁⟩ := lower_step ok hs
      constructor
      · intro h
        obtain ⟨k', h₂⟩ := ih.1 h
        exact ⟨k + k', by rw [run_add h₁]; exact h₂⟩
      · intro h
        obtain ⟨k', h₂⟩ := ih.2 h
        exact ⟨k + k', by rw [run_add h₁]; exact h₂⟩
    | halt c₁ =>
      refine ⟨fun h => (by cases h), fun h => ?_⟩
      cases h
      exact ⟨1, by simp only [run, lower_halt ok hs]⟩
    | fault f => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- Item 4: a source program that halts has a lowered program that halts the same way. -/
theorem lower_correct {prog : List Stmt} (ok : LayoutOk prog) (input : List Nat) (n : Nat)
    {c' : State} (h : srcRun prog n (State.init input) = .halt c') :
    ∃ k s, run (lower prog) k (State.init input) = .halt s ∧ s.pc = addrOf prog c'.pc ∧
      s.stack = c'.stack ∧ s.mem = c'.mem ∧ s.input = c'.input ∧ s.output = c'.output := by
  obtain ⟨k, hk⟩ := (lower_run ok n).2 h
  have e : toTarget prog (State.init input) = State.init input := by
    simp [toTarget, State.init, addrOf]
  rw [e] at hk
  exact ⟨k, _, hk, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Faults, divergence, the reverse direction -/

theorem addrOf_ge {prog : List Stmt} {j : Nat} (h : prog.length ≤ j) :
    addrOf prog j = addrOf prog prog.length := by
  simp [addrOf, List.take_of_length_le h]

theorem lowerFrom_length {A : Nat → Nat} (cs : List Stmt) (b : Nat)
    (ok : ∀ k s', cs[k]? = some s' → StmtOk A (b + k) s') :
    (lowerFrom A b cs).length = (cs.map Stmt.len).sum := by
  induction cs generalizing b with
  | nil => rfl
  | cons x cs ih =>
    have hx : StmtOk A b x := ok 0 x (by simp)
    have ok' : ∀ k s', cs[k]? = some s' → StmtOk A (b + 1 + k) s' := by
      intro k s' hk
      have := ok (k + 1) s' (by simpa using hk)
      rwa [show b + (k + 1) = b + 1 + k by omega] at this
    simp only [lowerFrom, List.length_append, lowerStmt_length hx, ih _ ok', List.map_cons,
      List.sum_cons]

/-- The lowered program ends at the address past the last statement. -/
theorem lower_length {prog : List Stmt} (ok : LayoutOk prog) :
    (lower prog).length = addrOf prog prog.length := by
  have := lowerFrom_length (A := addrOf prog) prog 0
    (fun k s' hk => by rw [Nat.zero_add]; exact ok k s' hk)
  simpa [lower, addrOf] using this

/-- A `ret` into the middle of a statement: the lowered program goes on from there, and the source
machine has no statement to go to. Every reverse theorem below excludes it. -/
def WildRet (prog : List Stmt) (c : State) : Prop :=
  prog[c.pc]? = some (.plain .ret) ∧ ∃ a r, c.stack = a :: r ∧ retTarget prog a = none ∧
    0 ≤ a ∧ a < ((lower prog).length : Int)

theorem jumpTo_fault_nat {D : List Instr} {t : State} {x : Nat} {f : Fault}
    (h : jumpTo D t x = .fault f) : D.length ≤ x ∧ f = .pcOutOfRange := by
  unfold jumpTo at h
  split at h
  · cases h
  · rename_i hc
    exact ⟨by omega, (Outcome.fault.inj h).symm⟩

theorem jumpTo_out {P : List Instr} {t : State} {x : Int} {T : Nat} (hx : x = (T : Int))
    (hT : P.length ≤ T) : jumpTo P t x = .fault .pcOutOfRange := by
  subst hx
  unfold jumpTo
  rw [ite_eq_right (by omega)]

theorem advance_fault_nat {D : List Instr} {t : State} {f : Fault} (h : advance D t = .fault f) :
    D.length ≤ t.pc + 1 ∧ f = .pcOutOfRange := by
  unfold advance jumpTo at h
  split at h
  · cases h
  · rename_i hc
    exact ⟨by omega, (Outcome.fault.inj h).symm⟩

theorem adv_fault {D P : List Instr} {pc a : Nat} {st : List Int} {m : Nat → Int} {i o : List Nat}
    {f : Fault} (h : advance D ⟨pc, st, m, i, o⟩ = .fault f)
    (hlen : pc + 1 < D.length ↔ a + 1 < P.length) :
    advance P ⟨a, st, m, i, o⟩ = .fault f := by
  obtain ⟨h1, rfl⟩ := advance_fault_nat h
  simp only at h1
  have h2 : ¬ a + 1 < P.length := fun hl => absurd (hlen.2 hl) (by omega)
  unfold advance jumpTo
  rw [ite_eq_right (by simp only; omega)]

-- A non-jump faults the same way on both programs: its only link to the program is `advance`.
theorem exec_plain_fault {D P : List Instr} {x : Instr} {pc a : Nat} {st : List Int}
    {m : Nat → Int} {i o : List Nat} {f : Fault}
    (hx : x ≠ .jmp ∧ x ≠ .jz ∧ x ≠ .jnz ∧ x ≠ .call ∧ x ≠ .ret)
    (hlen : pc + 1 < D.length ↔ a + 1 < P.length)
    (h : exec D ⟨pc, st, m, i, o⟩ x = .fault f) :
    exec P ⟨a, st, m, i, o⟩ x = .fault f := by
  rcases st with _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩ <;> rcases i with _ | ⟨d, i⟩ <;> cases x <;>
    first
    | (exfalso; simp at hx; done)
    | (simp only [exec, binary, divLike] at h ⊢
       first
       | (cases h; done)
       | exact h
       | exact adv_fault h hlen
       | (split at h <;> first
          | (cases h; done)
          | (rename_i hc; simp only [hc, ↓reduceIte]; first | exact h | exact adv_fault h hlen)))

theorem jumpTo_append_next {P : List Instr} {t s' : State} {x : Int}
    (h : jumpTo (P ++ [.halt]) t x = .next s') :
    if s'.pc = P.length then jumpTo P t x = .fault .pcOutOfRange else jumpTo P t x = .next s' := by
  obtain ⟨rfl, hlt⟩ := jumpTo_next h
  simp only [List.length_append, List.length_cons, List.length_nil] at hlt
  unfold jumpTo at h ⊢
  split at h
  · rename_i hc
    have hc2 := hc
    simp only [List.length_append, List.length_cons, List.length_nil] at hc2
    by_cases he : x.toNat = P.length
    · simp only [he, ↓reduceIte]
      rw [ite_eq_right (by omega)]
    · simp only [he, ↓reduceIte]
      rw [ite_eq_left (by omega)]
  · cases h

-- Growing a program by one `halt` only moves the end, and only `jumpTo` can see the end.
theorem exec_append_next {P : List Instr} {s s' : State} {x : Instr}
    (h : exec (P ++ [.halt]) s x = .next s') :
    if s'.pc = P.length then exec P s x = .fault .pcOutOfRange else exec P s x = .next s' := by
  obtain ⟨pc, st, m, i, o⟩ := s
  rcases st with _ | ⟨b, _ | ⟨c, _ | ⟨e, r⟩⟩⟩ <;> rcases i with _ | ⟨d, i⟩ <;> cases x <;>
    simp only [exec, binary, divLike, advance] at h ⊢ <;>
    first
    | (cases h; done)
    | exact jumpTo_append_next h
    | (split at h <;> first
       | (cases h; done)
       | (rename_i hc; rw [ite_eq_left hc]; exact jumpTo_append_next h)
       | (rename_i hc; rw [ite_eq_right hc]; exact jumpTo_append_next h))

/-- Code that runs to the end of a longer program falls off this one. -/
theorem run_falloff {P : List Instr} {n : Nat} {s s' : State}
    (h : run (P ++ [.halt]) n s = .next s') (hs' : s'.pc = P.length) (hn : 0 < n) :
    run P n s = .fault .pcOutOfRange := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    simp only [run] at h ⊢
    cases hst : step (P ++ [.halt]) s with
    | halt t => rw [hst] at h; cases h
    | fault f => rw [hst] at h; cases h
    | next t =>
      rw [hst] at h
      have hpc : s.pc < P.length ∨ s.pc = P.length := by
        have := step_pc_lt hst
        unfold step at hst
        cases hg : (P ++ [Instr.halt])[s.pc]? with
        | none => simp [hg] at hst
        | some y =>
          rcases List.getElem?_eq_some_iff.mp hg with ⟨hl, _⟩
          simp only [List.length_append, List.length_cons, List.length_nil] at hl
          omega
      rcases hpc with hlt | heq
      · have e : (P ++ [Instr.halt])[s.pc]? = P[s.pc]? := by
          rw [List.getElem?_append_left hlt]
        unfold step at hst ⊢
        rw [e] at hst
        cases hg : P[s.pc]? with
        | none => simp [hg] at hst
        | some y =>
          rw [hg] at hst
          simp only
          have hc := exec_append_next hst
          by_cases ht : t.pc = P.length
          · rw [if_pos ht] at hc
            rw [hc]
          · rw [if_neg ht] at hc
            rw [hc]
            cases n with
            | zero =>
              cases h
              exact absurd hs' ht
            | succ n => exact ih h (by omega)
      · exfalso
        unfold step at hst
        have e : (P ++ [Instr.halt])[s.pc]? = some .halt := by
          rw [heq]
          simp
        rw [e] at hst
        simp [exec] at hst

/-- A source fault is the same fault on the target, unless it is a wild `ret`. -/
theorem lower_fault {prog : List Stmt} (ok : LayoutOk prog) {c : State} {f : Fault}
    (hw : ¬ WildRet prog c) (hs : srcStep prog c = .fault f) :
    ∃ k, run (lower prog) k (toTarget prog c) = .fault f := by
  obtain ⟨pc, st, m, i, o⟩ := c
  have hLen := lower_length ok
  have hin : ∀ {q}, q < prog.length → addrOf prog q < (lower prog).length := addr_lt_of_lt ok
  have hT : ∀ {q}, prog.length ≤ q → addrOf prog q = (lower prog).length := by
    intro q hq
    rw [addrOf_ge hq, hLen]
  have hR := srcRange_length prog
  unfold srcStep at hs
  simp only at hs
  cases hi : prog[pc]? with
  | none =>
    rw [hi] at hs
    cases hs
    have hge : prog.length ≤ pc := List.getElem?_eq_none_iff.mp hi
    refine ⟨1, ?_⟩
    have hn : (lower prog)[addrOf prog pc]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      rw [hT hge]
      omega
    simp only [run, step, toTarget, hn]
  | some s =>
    rw [hi] at hs
    have hat := lower_at ok hi
    have hsok := ok pc s hi
    have hnext := addrOf_succ hi
    have hpc : pc < prog.length := by
      rcases List.getElem?_eq_some_iff.mp hi with ⟨h, _⟩
      exact h
    cases s with
    | plain x =>
      have hx : (lower prog)[addrOf prog pc]? = some x := hat.head
      by_cases hret : x = .ret
      · subst hret
        simp only [↓reduceIte, srcRet] at hs
        rcases st with _ | ⟨a, r⟩
        · cases hs
          exact ⟨1, by simp only [run, step, toTarget, hx, exec]⟩
        · simp only at hs
          cases hrt : retTarget prog a with
          | some j => simp [hrt] at hs
          | none =>
            simp only [hrt] at hs
            cases hs
            refine ⟨1, ?_⟩
            have hn : ¬ (0 ≤ a ∧ a < ((lower prog).length : Int)) := fun hc =>
              hw ⟨hi, a, r, rfl, hrt, hc.1, hc.2⟩
            simp only [run, step, toTarget, hx, exec, jumpTo]
            rw [ite_eq_right hn]
      · simp only [hret, ↓reduceIte] at hs
        have hl : addrOf prog (pc + 1) = addrOf prog pc + 1 := hnext
        have hlen : pc + 1 < (srcRange prog).length ↔ addrOf prog pc + 1 < (lower prog).length := by
          rw [hR, ← hl]
          constructor
          · exact fun h => hin h
          · intro h
            by_cases hc : pc + 1 < prog.length
            · exact hc
            · have := hT (q := pc + 1) (by omega)
              omega
        have := exec_plain_fault (P := lower prog) (a := addrOf prog pc)
          ⟨hsok.1, hsok.2.1, hsok.2.2.1, hsok.2.2.2, hret⟩ hlen hs
        exact ⟨1, by simp only [run, step, toTarget, hx, this]⟩
    | pushI n =>
      obtain ⟨h1, rfl⟩ := advance_fault_nat hs
      simp only at h1
      rw [hR] at h1
      have hend := hT (q := pc + 1) h1
      have hl : addrOf prog (pc + 1) = addrOf prog pc + (pushInt n).length := hnext
      have hAt' : At (lower prog ++ [.halt]) (addrOf prog pc) (pushInt n) := by
        obtain ⟨pre, suf, e, h2⟩ := hat
        exact ⟨pre, suf ++ [.halt], by simp [e, lowerStmt], h2⟩
      have q := seq_pushInt n st m (lower prog ++ [.halt]) _ i o hAt' (by simp; omega)
      exact ⟨_, run_falloff q (by simp only; omega) (pushInt_length_pos n)⟩
    | jump j t slot =>
      obtain ⟨hle, hne⟩ := hsok
      generalize hoffdef : jumpOffset (addrOf prog t) (addrOf prog pc) slot = off at hle hne
      have hat' : At (lower prog) (addrOf prog pc)
          (loweredJump j.instr off (slot - (pushInt off).length)) := by
        have := hat
        simp only [lowerStmt, hoffdef] at this
        exact this
      have hl : addrOf prog (pc + 1) = addrOf prog pc + (slot + 1) := hnext
      have hJ : addrOf prog pc + ((pushInt off).length + (slot - (pushInt off).length)) =
          addrOf prog pc + slot := by omega
      have hoff : ((addrOf prog pc + slot : Nat) : Int) + off = (addrOf prog t : Int) := by
        rw [← hoffdef]
        simp only [jumpOffset]
        omega
      have htgt : ∀ {y}, prog.length ≤ t → jumpTo (lower prog) y (((addrOf prog pc + slot : Nat) : Int) + off)
          = .fault .pcOutOfRange := fun h => jumpTo_out hoff (by rw [hT h]; omega)
      have hfall : ∀ {y : State}, prog.length ≤ pc + 1 → y.pc = addrOf prog pc + slot →
          advance (lower prog) y = .fault .pcOutOfRange := by
        intro y h hy
        have := hT h
        unfold advance
        exact jumpTo_out (T := addrOf prog pc + slot + 1) (by rw [hy]; omega) (by omega)
      have pre := fun (st' : List Int) => lowered_prefix hne hat' st' m i o
      have dest : ∀ (st' : List Int), ∃ L,
          (lower prog)[addrOf prog pc + slot]? = some j.instr ∧
          run (lower prog) L ⟨addrOf prog pc, st', m, i, o⟩ =
            .next ⟨addrOf prog pc + slot, off :: st', m, i, o⟩ := by
        intro st'
        obtain ⟨h1, h2⟩ := pre st'
        rw [hJ] at h1 h2
        exact ⟨_, h1, h2⟩
      have finish : ∀ (st' : List Int) (g : Fault),
          step (lower prog) ⟨addrOf prog pc + slot, off :: st', m, i, o⟩ = .fault g →
          ∃ L, run (lower prog) L ⟨addrOf prog pc, st', m, i, o⟩ = .fault g := by
        intro st' g hg
        obtain ⟨L, _, h2⟩ := dest st'
        exact ⟨L + 1, by rw [run_add h2]; simp only [run, hg]⟩
      cases j with
      | jmp =>
        obtain ⟨h1, rfl⟩ := jumpTo_fault_nat hs
        rw [hR] at h1
        obtain ⟨L, hx, _⟩ := dest st
        exact finish st _ (by
          simp only [step, hx, JumpKind.instr, exec]
          exact htgt h1)
      | call =>
        obtain ⟨h1, rfl⟩ := jumpTo_fault_nat hs
        rw [hR] at h1
        obtain ⟨L, hx, _⟩ := dest st
        exact finish st _ (by
          simp only [step, hx, JumpKind.instr, exec]
          exact htgt h1)
      | jz =>
        rcases st with _ | ⟨y, r⟩
        · cases hs
          obtain ⟨L, hx, _⟩ := dest []
          exact finish [] .stackUnderflow (by simp only [step, hx, JumpKind.instr, exec])
        · simp only at hs
          obtain ⟨L, hx, _⟩ := dest (y :: r)
          by_cases hy : y = 0
          · rw [ite_eq_left hy] at hs
            obtain ⟨h1, rfl⟩ := jumpTo_fault_nat hs
            rw [hR] at h1
            exact finish (y :: r) .pcOutOfRange (by
              simp only [step, hx, JumpKind.instr, exec]
              rw [ite_eq_left hy]
              exact htgt h1)
          · rw [ite_eq_right hy] at hs
            obtain ⟨h1, rfl⟩ := advance_fault_nat hs
            simp only at h1
            rw [hR] at h1
            exact finish (y :: r) .pcOutOfRange (by
              simp only [step, hx, JumpKind.instr, exec]
              rw [ite_eq_right hy]
              exact hfall h1 rfl)
      | jnz =>
        rcases st with _ | ⟨y, r⟩
        · cases hs
          obtain ⟨L, hx, _⟩ := dest []
          exact finish [] .stackUnderflow (by simp only [step, hx, JumpKind.instr, exec])
        · simp only at hs
          obtain ⟨L, hx, _⟩ := dest (y :: r)
          by_cases hy : y ≠ 0
          · rw [ite_eq_left hy] at hs
            obtain ⟨h1, rfl⟩ := jumpTo_fault_nat hs
            rw [hR] at h1
            exact finish (y :: r) .pcOutOfRange (by
              simp only [step, hx, JumpKind.instr, exec]
              rw [ite_eq_left hy]
              exact htgt h1)
          · rw [ite_eq_right hy] at hs
            obtain ⟨h1, rfl⟩ := advance_fault_nat hs
            simp only at h1
            rw [hR] at h1
            exact finish (y :: r) .pcOutOfRange (by
              simp only [step, hx, JumpKind.instr, exec]
              rw [ite_eq_right hy]
              exact hfall h1 rfl)

/-- No state a run can reach is a wild `ret`. Every program without `ret` qualifies. -/
def NoWild (prog : List Stmt) (input : List Nat) : Prop :=
  ∀ n c, srcRun prog n (State.init input) = .next c → ¬ WildRet prog c

theorem noWild_of_no_ret {prog : List Stmt} (h : .plain .ret ∉ prog) (input : List Nat) :
    NoWild prog input := by
  intro n c _ hw
  exact h (List.mem_of_getElem? hw.1)

theorem toTarget_init (prog : List Stmt) (input : List Nat) :
    toTarget prog (State.init input) = State.init input := by
  simp [toTarget, State.init, addrOf]

theorem lower_run_fault {prog : List Stmt} (ok : LayoutOk prog) {n : Nat} {c : State} {f : Fault}
    (hw : ∀ m d, srcRun prog m c = .next d → ¬ WildRet prog d)
    (h : srcRun prog n c = .fault f) :
    ∃ k, run (lower prog) k (toTarget prog c) = .fault f := by
  induction n generalizing c with
  | zero => cases h
  | succ n ih =>
    simp only [srcRun] at h
    cases hs : srcStep prog c with
    | next c₁ =>
      rw [hs] at h
      obtain ⟨k, _, h₁⟩ := lower_step ok hs
      obtain ⟨k', h₂⟩ := ih (c := c₁)
        (fun m d hd => hw (m + 1) d (by simp only [srcRun, hs]; exact hd)) h
      exact ⟨k + k', by rw [run_add h₁]; exact h₂⟩
    | halt c₁ =>
      rw [hs] at h
      cases h
    | fault g =>
      rw [hs] at h
      cases h
      exact lower_fault ok (hw 0 c rfl) hs

/-- A source run alive at every fuel keeps the target alive at every fuel. -/
theorem lower_diverges {prog : List Stmt} (ok : LayoutOk prog) {c : State}
    (h : ∀ n, ∃ c', srcRun prog n c = .next c') (fuel : Nat) :
    ∃ s, run (lower prog) fuel (toTarget prog c) = .next s := by
  induction fuel using Nat.strongRecOn generalizing c with
  | _ fuel ih =>
    obtain ⟨c₁, hc₁⟩ := h 1
    simp only [srcRun] at hc₁
    cases hs : srcStep prog c with
    | halt t => rw [hs] at hc₁; cases hc₁
    | fault f => rw [hs] at hc₁; cases hc₁
    | next c₂ =>
      obtain ⟨k, hk, hrun⟩ := lower_step ok hs
      by_cases hn : fuel ≤ k
      · exact run_prefix hrun hn
      · have htail : ∀ n, ∃ c', srcRun prog n c₂ = .next c' := by
          intro n
          obtain ⟨c', hc'⟩ := h (n + 1)
          simp only [srcRun, hs] at hc'
          exact ⟨c', hc'⟩
        obtain ⟨t, ht⟩ := ih (fuel - k) (by omega) htail
        have e : fuel = k + (fuel - k) := by omega
        exact ⟨t, by rw [e, run_add hrun]; exact ht⟩

/-- Every source run ends one of three ways. -/
theorem src_trichotomy (prog : List Stmt) (c : State) :
    (∃ n c', srcRun prog n c = .halt c') ∨ (∃ n f, srcRun prog n c = .fault f) ∨
      ∀ n, ∃ c', srcRun prog n c = .next c' := by
  by_cases h1 : ∃ n c', srcRun prog n c = .halt c'
  · exact .inl h1
  · by_cases h2 : ∃ n f, srcRun prog n c = .fault f
    · exact .inr (.inl h2)
    · refine .inr (.inr fun n => ?_)
      cases hr : srcRun prog n c with
      | next c' => exact ⟨c', rfl⟩
      | halt c' => exact absurd ⟨n, c', hr⟩ h1
      | fault f => exact absurd ⟨n, f, hr⟩ h2

/-- The reverse direction: a lowered program that halts comes from a source program that halts,
in the same state up to `pc`. -/
theorem lower_halts_source {prog : List Stmt} (ok : LayoutOk prog) {input : List Nat}
    (hw : NoWild prog input) {k : Nat} {s : State}
    (h : run (lower prog) k (State.init input) = .halt s) :
    ∃ n c', srcRun prog n (State.init input) = .halt c' ∧ s = toTarget prog c' := by
  rcases src_trichotomy prog (State.init input) with ⟨n, c', hs⟩ | ⟨n, f, hs⟩ | hd
  · obtain ⟨k', hk'⟩ := (lower_run ok n).2 hs
    rw [toTarget_init] at hk'
    exact ⟨n, c', hs, run_halt_unique h hk'⟩
  · obtain ⟨k', hk'⟩ := lower_run_fault ok hw hs
    rw [toTarget_init] at hk'
    exact absurd hk' (run_halt_fault_exclusive h)
  · obtain ⟨t, ht⟩ := lower_diverges ok hd k
    rw [toTarget_init, h] at ht
    cases ht

/-- A lowered program faults only when the source program faults, with the same fault. -/
theorem lower_faults_source {prog : List Stmt} (ok : LayoutOk prog) {input : List Nat}
    (hw : NoWild prog input) {k : Nat} {f : Fault}
    (h : run (lower prog) k (State.init input) = .fault f) :
    ∃ n, srcRun prog n (State.init input) = .fault f := by
  rcases src_trichotomy prog (State.init input) with ⟨n, c', hs⟩ | ⟨n, g, hs⟩ | hd
  · obtain ⟨k', hk'⟩ := (lower_run ok n).2 hs
    rw [toTarget_init] at hk'
    exact absurd h (run_halt_fault_exclusive hk')
  · obtain ⟨k', hk'⟩ := lower_run_fault ok hw hs
    rw [toTarget_init] at hk'
    rw [run_fault_unique h hk']
    exact ⟨n, hs⟩
  · obtain ⟨t, ht⟩ := lower_diverges ok hd k
    rw [toTarget_init, h] at ht
    cases ht

/-- Source and lowered program halt together. -/
theorem lower_halts_iff {prog : List Stmt} (ok : LayoutOk prog) {input : List Nat}
    (hw : NoWild prog input) :
    (∃ k s, run (lower prog) k (State.init input) = .halt s) ↔
      ∃ n c', srcRun prog n (State.init input) = .halt c' := by
  constructor
  · intro ⟨k, s, h⟩
    obtain ⟨n, c', hs, _⟩ := lower_halts_source ok hw h
    exact ⟨n, c', hs⟩
  · intro ⟨n, c', h⟩
    obtain ⟨k, s, hs, _⟩ := lower_correct ok input n h
    exact ⟨k, s, hs⟩

/-- Source and lowered program fault together, with the same fault. -/
theorem lower_faults_iff {prog : List Stmt} (ok : LayoutOk prog) {input : List Nat}
    (hw : NoWild prog input) (f : Fault) :
    (∃ k, run (lower prog) k (State.init input) = .fault f) ↔
      ∃ n, srcRun prog n (State.init input) = .fault f := by
  constructor
  · intro ⟨k, h⟩
    exact lower_faults_source ok hw h
  · intro ⟨n, h⟩
    obtain ⟨k, hk⟩ := lower_run_fault ok hw h
    rw [toTarget_init] at hk
    exact ⟨k, hk⟩

/-- Source and lowered program diverge together. -/
theorem lower_diverges_iff {prog : List Stmt} (ok : LayoutOk prog) {input : List Nat}
    (hw : NoWild prog input) :
    (∀ k, ∃ s, run (lower prog) k (State.init input) = .next s) ↔
      ∀ n, ∃ c', srcRun prog n (State.init input) = .next c' := by
  constructor
  · intro h n
    cases hr : srcRun prog n (State.init input) with
    | next c' => exact ⟨c', rfl⟩
    | halt c' =>
      obtain ⟨k, s, hs, _⟩ := lower_correct ok input n hr
      obtain ⟨t, ht⟩ := h k
      rw [hs] at ht
      cases ht
    | fault f =>
      obtain ⟨k, hk⟩ := lower_run_fault ok hw hr
      rw [toTarget_init] at hk
      obtain ⟨t, ht⟩ := h k
      rw [hk] at ht
      cases ht
  · intro h k
    have := lower_diverges ok h k
    rwa [toTarget_init] at this

/-! ## The fixed point of `generate` -/

/-- One pass of the second loop of `generate`, with the addresses of the first. -/
def growStmt (A : Nat → Nat) (i : Nat) : Stmt → Stmt
  | .jump j t slot =>
    if slot < (pushInt (jumpOffset (A t) (A i) slot)).length
    then .jump j t (pushInt (jumpOffset (A t) (A i) slot)).length
    else .jump j t slot
  | s => s

def growFrom (A : Nat → Nat) : Nat → List Stmt → List Stmt
  | _, [] => []
  | i, s :: cs => growStmt A i s :: growFrom A (i + 1) cs

def grow (prog : List Stmt) : List Stmt := growFrom (addrOf prog) 0 prog

/-- The `loop` of `generate`: stops when no slot grew. The fuel stands for the Rust's unbounded
`loop`: `none` says only that the fuel ran out. -/
def layoutLoop : Nat → List Stmt → Option (List Stmt)
  | 0, _ => none
  | n + 1, p => if grow p = p then some p else layoutLoop n (grow p)

/-- What `generate` starts from and keeps: no raw jumps, and each slot 0 or the odd length of a
`push_int`. -/
def StmtInv : Stmt → Prop
  | .plain x => x ≠ .jmp ∧ x ≠ .jz ∧ x ≠ .jnz ∧ x ≠ .call
  | .pushI _ => True
  | .jump _ _ slot => slot = 0 ∨ slot % 2 = 1

def LayoutInv (prog : List Stmt) : Prop := ∀ s ∈ prog, StmtInv s

theorem growFrom_get (A : Nat → Nat) (cs : List Stmt) (b k : Nat) :
    (growFrom A b cs)[k]? = cs[k]?.map (growStmt A (b + k)) := by
  induction cs generalizing b k with
  | nil => simp [growFrom]
  | cons x cs ih =>
    cases k with
    | zero => simp [growFrom]
    | succ k =>
      have := ih (b + 1) k
      rw [show b + 1 + k = b + (k + 1) by omega] at this
      simpa [growFrom] using this

theorem growStmt_inv {A : Nat → Nat} {i : Nat} {s : Stmt} (h : StmtInv s) :
    StmtInv (growStmt A i s) := by
  cases s with
  | plain x => exact h
  | pushI n => exact h
  | jump j t slot =>
    simp only [growStmt]
    split
    · exact .inr (pushInt_length_odd _)
    · exact h

theorem grow_inv {prog : List Stmt} (h : LayoutInv prog) : LayoutInv (grow prog) := by
  intro s hs
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hs
  rw [grow, growFrom_get] at hk
  cases hg : prog[k]? with
  | none => simp [hg] at hk
  | some s₀ =>
    simp only [hg, Option.map_some, Option.some.injEq] at hk
    subst hk
    exact growStmt_inv (h s₀ (List.mem_of_getElem? hg))

/-- A program no pass can grow, with the invariant, has a consistent layout. -/
theorem stable_layoutOk {prog : List Stmt} (hinv : LayoutInv prog) (hs : grow prog = prog) :
    LayoutOk prog := by
  intro i s hi
  have hg : (grow prog)[i]? = prog[i]?.map (growStmt (addrOf prog) (0 + i)) := growFrom_get ..
  rw [hs, hi, Nat.zero_add] at hg
  simp only [Option.map_some, Option.some.injEq] at hg
  have hsi := hinv s (List.mem_of_getElem? hi)
  cases s with
  | plain x => exact hsi
  | pushI n => trivial
  | jump j t slot =>
    simp only [growStmt] at hg
    have hodd := pushInt_length_odd (jumpOffset (addrOf prog t) (addrOf prog i) slot)
    split at hg
    · simp only [Stmt.jump.injEq, true_and] at hg
      omega
    · rename_i hle
      have hsi' : slot = 0 ∨ slot % 2 = 1 := hsi
      refine ⟨by omega, ?_⟩
      omega

/-- The fixed point establishes `LayoutOk`: any result of the loop has a consistent layout, so the
correctness theorems above no longer need it as an assumption. -/
theorem layoutLoop_ok {n : Nat} {p q : List Stmt} (h : layoutLoop n p = some q)
    (hinv : LayoutInv p) : LayoutOk q := by
  induction n generalizing p with
  | zero => cases h
  | succ n ih =>
    simp only [layoutLoop] at h
    split at h
    · rename_i hs
      cases h
      exact stable_layoutOk hinv hs
    · exact ih h (grow_inv hinv)

/-- A statement with its slot forgotten: what the programmer wrote. -/
def Stmt.erase : Stmt → Stmt
  | .jump j t _ => .jump j t 0
  | s => s

theorem growStmt_erase (A : Nat → Nat) (i : Nat) (s : Stmt) : (growStmt A i s).erase = s.erase := by
  cases s with
  | plain x => rfl
  | pushI n => rfl
  | jump j t slot =>
    simp only [growStmt]
    split <;> rfl

theorem growFrom_erase (A : Nat → Nat) (cs : List Stmt) (b : Nat) :
    (growFrom A b cs).map Stmt.erase = cs.map Stmt.erase := by
  induction cs generalizing b with
  | nil => rfl
  | cons x cs ih => simp [growFrom, growStmt_erase, ih]

/-- The loop only changes slots: the result is the same program as the source. -/
theorem layoutLoop_erase {n : Nat} {p q : List Stmt} (h : layoutLoop n p = some q) :
    q.map Stmt.erase = p.map Stmt.erase := by
  induction n generalizing p with
  | zero => cases h
  | succ n ih =>
    simp only [layoutLoop] at h
    split at h
    · cases h
      rfl
    · rw [ih h, grow, growFrom_erase]

/-- The whole compiler on the mirror: from a source with empty slots, any result of the loop
behaves as the source, in all three outcomes, unless a `ret` lands inside a statement. -/
theorem generate_correct {n : Nat} {src p : List Stmt} (h : layoutLoop n src = some p)
    (hinv : LayoutInv src) {input : List Nat} (hw : NoWild p input) :
    ((∃ k s, run (lower p) k (State.init input) = .halt s) ↔
      ∃ m c', srcRun p m (State.init input) = .halt c') ∧
    (∀ f, (∃ k, run (lower p) k (State.init input) = .fault f) ↔
      ∃ m, srcRun p m (State.init input) = .fault f) ∧
    ((∀ k, ∃ s, run (lower p) k (State.init input) = .next s) ↔
      ∀ m, ∃ c', srcRun p m (State.init input) = .next c') := by
  have ok := layoutLoop_ok h hinv
  exact ⟨lower_halts_iff ok hw, fun f => lower_faults_iff ok hw f, lower_diverges_iff ok hw⟩

-- `LayoutOk` can hold on a program with a jump: `JMP a; a: HALT` with a one-instruction slot.
example : LayoutOk [.jump .jmp 1 1, .plain .halt] := by
  intro i s h
  match i, h with
  | 0, h =>
    simp at h
    subst h
    simp [StmtOk, addrOf, jumpOffset, Stmt.len, pushInt, pushMag]
  | 1, h =>
    simp at h
    subst h
    simp [StmtOk]

end Emd

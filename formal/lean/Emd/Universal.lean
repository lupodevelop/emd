import Emd

/-! # emd simulates counter machines, keeping register `r` in memory cell `r`. -/

namespace Emd

namespace CM

inductive Instr where
  | inc (r : Nat)
  | decJz (r target : Nat)
  | halt
  deriving DecidableEq, Repr

abbrev Program := List Instr

structure Config where
  pc : Nat
  regs : Nat → Nat

def update (f : Nat → Nat) (r v : Nat) : Nat → Nat :=
  fun i => if i = r then v else f i

-- `none` means halted: a `halt` instruction, or a pc past the end, so every program is total.
def step (C : Program) (c : Config) : Option Config :=
  match C[c.pc]? with
  | some (.inc r) => some ⟨c.pc + 1, update c.regs r (c.regs r + 1)⟩
  | some (.decJz r t) =>
    if c.regs r = 0 then some ⟨t, c.regs⟩
    else some ⟨c.pc + 1, update c.regs r (c.regs r - 1)⟩
  | some .halt => none
  | none => none

def run (C : Program) : Nat → Config → Option Config
  | 0, c => some c
  | k + 1, c => (step C c).bind (run C k)

def Halts (C : Program) (c : Config) : Prop :=
  ∃ k c', run C k c = some c' ∧ step C c' = none

end CM

/-! ## Running emd code in pieces -/

theorem run_add {P : List Instr} {n m : Nat} {s s' : State} (h : run P n s = .next s') :
    run P (n + m) s = run P m s' := by
  induction n generalizing s with
  | zero =>
    simp only [run, Outcome.next.injEq] at h
    subst h
    simp
  | succ n ih =>
    rw [Nat.add_right_comm]
    simp only [run] at h ⊢
    cases hs : step P s with
    | next t =>
      rw [hs] at h
      exact ih h
    | halt t => rw [hs] at h; simp at h
    | fault f => rw [hs] at h; simp at h

-- A run alive after `k` steps was alive at every earlier fuel: needed for divergence.
theorem run_prefix {P : List Instr} {k n : Nat} {s s' : State} (h : run P k s = .next s')
    (hn : n ≤ k) : ∃ t, run P n s = .next t := by
  induction k generalizing n s with
  | zero =>
    have : n = 0 := by omega
    subst this
    exact ⟨_, h⟩
  | succ k ih =>
    cases n with
    | zero => exact ⟨s, rfl⟩
    | succ n =>
      simp only [run] at h ⊢
      cases hs : step P s with
      | next t =>
        rw [hs] at h
        exact ih h (by omega)
      | halt t => rw [hs] at h; simp at h
      | fault f => rw [hs] at h; simp at h

/-- `l` sits in `P` at index `a`. -/
def At (P : List Instr) (a : Nat) (l : List Instr) : Prop :=
  ∃ pre suf, P = pre ++ (l ++ suf) ∧ pre.length = a

theorem At.left {P : List Instr} {a : Nat} {l₁ l₂ : List Instr} (h : At P a (l₁ ++ l₂)) :
    At P a l₁ := by
  obtain ⟨pre, suf, e, hl⟩ := h
  exact ⟨pre, l₂ ++ suf, by simp [e], hl⟩

theorem At.right {P : List Instr} {a : Nat} {l₁ l₂ : List Instr} (h : At P a (l₁ ++ l₂)) :
    At P (a + l₁.length) l₂ := by
  obtain ⟨pre, suf, e, hl⟩ := h
  exact ⟨pre ++ l₁, suf, by simp [e], by simp [hl]⟩

theorem At.head {P : List Instr} {a : Nat} {x : Instr} {l : List Instr} (h : At P a (x :: l)) :
    P[a]? = some x := by
  obtain ⟨pre, suf, e, hl⟩ := h
  subst e hl
  simp

/-- Straight-line code: from the start of `l` it takes exactly `l.length` steps to its end. -/
def Seq (l : List Instr) (st : List Int) (m : Nat → Int) (st' : List Int) (m' : Nat → Int) : Prop :=
  ∀ (P : List Instr) (a : Nat) (i o : List Nat), At P a l → a + l.length < P.length →
    run P l.length ⟨a, st, m, i, o⟩ = .next ⟨a + l.length, st', m', i, o⟩

theorem Seq.append {l₁ l₂ : List Instr} {st st₁ st₂ : List Int} {m m₁ m₂ : Nat → Int}
    (h₁ : Seq l₁ st m st₁ m₁) (h₂ : Seq l₂ st₁ m₁ st₂ m₂) : Seq (l₁ ++ l₂) st m st₂ m₂ := by
  intro P a i o hAt hlen
  rw [List.length_append] at hlen ⊢
  have e₁ := h₁ P a i o hAt.left (by omega)
  have e₂ := h₂ P (a + l₁.length) i o hAt.right (by omega)
  rw [run_add e₁, e₂, Nat.add_assoc]

theorem advance_ok {P : List Instr} {a : Nat} {st : List Int} {m : Nat → Int} {i o : List Nat}
    (h : a + 1 < P.length) :
    advance P ⟨a, st, m, i, o⟩ = .next ⟨a + 1, st, m, i, o⟩ := by
  have h1 : (0 : Int) ≤ (a : Int) + 1 := by omega
  have h2 : (a : Int) + 1 < (P.length : Int) := by omega
  have h3 : ((a : Int) + 1).toNat = a + 1 := by omega
  show (if 0 ≤ (a : Int) + 1 ∧ (a : Int) + 1 < (P.length : Int)
    then Outcome.next ⟨((a : Int) + 1).toNat, st, m, i, o⟩ else .fault .pcOutOfRange) = _
  rw [ite_eq_left ⟨h1, h2⟩, h3]

theorem seq_single {x : Instr} {st st' : List Int} {m m' : Nat → Int}
    (h : ∀ (P : List Instr) (a : Nat) (i o : List Nat), a + 1 < P.length →
      exec P ⟨a, st, m, i, o⟩ x = .next ⟨a + 1, st', m', i, o⟩) : Seq [x] st m st' m' := by
  intro P a i o hAt hlen
  have hx : P[a]? = some x := hAt.head
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at hlen ⊢
  simp only [run, step, hx]
  rw [h P a i o hlen]

theorem seq_push (k : Nat) (hk : k < 8) (st : List Int) (m : Nat → Int) :
    Seq [.push ⟨k, hk⟩] st m ((k : Int) :: st) m :=
  seq_single fun _ _ _ _ h => advance_ok h

theorem seq_drop (v : Int) (st : List Int) (m : Nat → Int) : Seq [.drop] (v :: st) m st m :=
  seq_single fun _ _ _ _ h => advance_ok h

theorem seq_add (b a : Int) (r : List Int) (m : Nat → Int) :
    Seq [.add] (b :: a :: r) m ((a + b) :: r) m :=
  seq_single fun _ _ _ _ h => advance_ok h

theorem seq_sub (b a : Int) (r : List Int) (m : Nat → Int) :
    Seq [.sub] (b :: a :: r) m ((a - b) :: r) m :=
  seq_single fun _ _ _ _ h => advance_ok h

theorem seq_mul (b a : Int) (r : List Int) (m : Nat → Int) :
    Seq [.mul] (b :: a :: r) m ((a * b) :: r) m :=
  seq_single fun _ _ _ _ h => advance_ok h

theorem seq_load (n : Nat) (r : List Int) (m : Nat → Int) :
    Seq [.load] ((n : Int) :: r) m (m n :: r) m := by
  refine seq_single fun P a i o h => ?_
  simp only [exec, Int.toNat_natCast]
  rw [ite_eq_right (by omega)]
  exact advance_ok h

theorem seq_store (n : Nat) (v : Int) (r : List Int) (m : Nat → Int) :
    Seq [.store] ((n : Int) :: v :: r) m r (fun j => if j = n then v else m j) := by
  refine seq_single fun P a i o h => ?_
  simp only [exec, Int.toNat_natCast]
  rw [ite_eq_right (by omega)]
  exact advance_ok h

-- Not taken: `jz` is plain straight-line code, so the fall-through path composes with `Seq`.
theorem seq_jz_fall (off c : Int) (r : List Int) (m : Nat → Int) (hc : c ≠ 0) :
    Seq [.jz] (off :: c :: r) m r m := by
  refine seq_single fun P a i o h => ?_
  simp only [exec]
  rw [ite_eq_right hc]
  exact advance_ok h

-- Taken: the offset is `target - pc` by construction, so the jump lands on `target`.
theorem step_jz_taken {P : List Instr} {a target : Nat} {c : Int} {r : List Int} {m : Nat → Int}
    {i o : List Nat} (hx : P[a]? = some .jz) (ht : target < P.length) (hc : c = 0) :
    step P ⟨a, ((target : Int) - (a : Int)) :: c :: r, m, i, o⟩ = .next ⟨target, r, m, i, o⟩ := by
  have e : (a : Int) + ((target : Int) - (a : Int)) = target := by omega
  have h0 : (0 : Int) ≤ target := by omega
  have h1 : (target : Int) < (P.length : Int) := by omega
  simp only [step, hx, exec]
  rw [ite_eq_left hc]
  simp only [jumpTo, e]
  rw [ite_eq_left ⟨h0, h1⟩, Int.toNat_natCast]

/-! ## Fixed-width constants -/

-- The length is independent of `n`, which breaks the circularity between offsets and layout.
def pushW : Nat → Nat → List Instr
  | 0, _ => [.push ⟨0, by omega⟩]
  | w + 1, n =>
    pushW w (n / 2) ++ [.push ⟨2, by omega⟩] ++ [.mul] ++ [.push ⟨n % 2, by omega⟩] ++ [.add]

theorem pushW_length (w n : Nat) : (pushW w n).length = 4 * w + 1 := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [pushW, ih]; omega

theorem seq_pushW (st : List Int) (m : Nat → Int) (w n : Nat) (h : n < 2 ^ w) :
    Seq (pushW w n) st m ((n : Int) :: st) m := by
  induction w generalizing n with
  | zero =>
    have : n = 0 := by simpa using h
    subst this
    exact seq_push 0 (by omega) st m
  | succ w ih =>
    have hn : n / 2 < 2 ^ w := by
      rw [Nat.pow_succ] at h
      omega
    have e : (((n / 2 : Nat) : Int) * ((2 : Nat) : Int)) + ((n % 2 : Nat) : Int) = (n : Int) := by
      omega
    have q := (((((ih (n / 2) hn).append (seq_push 2 (by omega) _ m)).append
      (seq_mul _ _ _ m)).append (seq_push (n % 2) (by omega) _ m)).append (seq_add _ _ _ m))
    rw [e] at q
    exact q

/-! ## The compiler -/

def bsize (w : Nat) : Nat := 20 * w + 12

-- Pads an `inc` block to `bsize` so that a block's address is a plain product.
def pad (w : Nat) : List Instr :=
  pushW w 0 ++ [.drop] ++ pushW w 0 ++ [.drop] ++ pushW w 0 ++ [.drop]

def incBlock (w r : Nat) : List Instr :=
  pushW w r ++ [.load] ++ [.push ⟨1, by omega⟩] ++ [.add] ++ pushW w r ++ [.store] ++ pad w

-- Stops right before `jz`; `J` is the address of that `jz` and `T` the absolute target.
def decPre (w r T J : Nat) : List Instr :=
  pushW w r ++ [.load] ++ pushW w T ++ pushW w J ++ [.sub]

def decPost (w r : Nat) : List Instr :=
  pushW w r ++ [.load] ++ [.push ⟨1, by omega⟩] ++ [.sub] ++ pushW w r ++ [.store]

-- Targets past the end clamp to `N`, the trailing `halt`, matching `CM.step` halting there.
def block (w N i : Nat) : CM.Instr → List Instr
  | .inc r => incBlock w r
  | .decJz r t =>
    decPre w r (min t N * bsize w) (i * bsize w + (12 * w + 5)) ++ [.jz] ++ decPost w r
  | .halt => .halt :: List.replicate (20 * w + 11) .halt

def layout (w N : Nat) : Nat → CM.Program → List Instr
  | _, [] => []
  | i, ins :: cs => block w N i ins ++ layout w N (i + 1) cs

def regBound : CM.Program → Nat
  | [] => 0
  | .inc r :: C => r + regBound C
  | .decJz r _ :: C => r + regBound C
  | .halt :: C => regBound C

-- Wide enough for every register index and every code address of `C`: see `addr_lt`.
def width (C : CM.Program) : Nat := 2 * (C.length + regBound C) + 8

def compile (C : CM.Program) : List Instr :=
  layout (width C) C.length 0 C ++ [.halt]

theorem decPre_length (w r T J : Nat) : (decPre w r T J).length = 12 * w + 5 := by
  simp [decPre, pushW_length]; omega

theorem decPost_length (w r : Nat) : (decPost w r).length = 8 * w + 6 := by
  simp [decPost, pushW_length]; omega

theorem incBlock_length (w r : Nat) : (incBlock w r).length = bsize w := by
  simp [incBlock, pad, pushW_length, bsize]; omega

theorem block_length (w N i : Nat) (ins : CM.Instr) : (block w N i ins).length = bsize w := by
  cases ins with
  | inc r => exact incBlock_length w r
  | decJz r t => simp [block, decPre_length, decPost_length, bsize]; omega
  | halt => simp [block, bsize]

theorem layout_length (w N i : Nat) (cs : CM.Program) :
    (layout w N i cs).length = cs.length * bsize w := by
  induction cs generalizing i with
  | nil => simp [layout]
  | cons ins cs ih =>
    simp only [layout, List.length_append, block_length, ih, List.length_cons, Nat.add_mul]
    omega

theorem compile_length (C : CM.Program) :
    (compile C).length = C.length * bsize (width C) + 1 := by
  simp [compile, layout_length]

theorem layout_at (w N : Nat) (cs : CM.Program) (i j : Nat) (ins : CM.Instr)
    (h : cs[j]? = some ins) :
    ∃ pre suf, layout w N i cs = pre ++ (block w N (i + j) ins ++ suf) ∧
      pre.length = j * bsize w := by
  induction cs generalizing i j with
  | nil => simp at h
  | cons x cs ih =>
    cases j with
    | zero =>
      have : x = ins := by simpa using h
      subst this
      exact ⟨[], layout w N (i + 1) cs, by simp [layout], by simp⟩
    | succ j =>
      obtain ⟨pre, suf, e, hl⟩ := ih (i + 1) j (by simpa using h)
      refine ⟨block w N i x ++ pre, suf, ?_, ?_⟩
      · have : i + (j + 1) = i + 1 + j := by omega
        simp only [layout, e, this, List.append_assoc]
      · simp only [List.length_append, block_length, hl, Nat.add_mul]
        omega

theorem compile_at {C : CM.Program} {j : Nat} {ins : CM.Instr} (h : C[j]? = some ins) :
    At (compile C) (j * bsize (width C)) (block (width C) C.length j ins) := by
  obtain ⟨pre, suf, e, hl⟩ := layout_at (width C) C.length C 0 j ins h
  rw [Nat.zero_add] at e
  exact ⟨pre, suf ++ [.halt], by simp [compile, e], hl⟩

theorem compile_end (C : CM.Program) :
    (compile C)[C.length * bsize (width C)]? = some .halt := by
  have h : At (compile C) (C.length * bsize (width C)) [.halt] :=
    ⟨layout (width C) C.length 0 C, [], by simp [compile], layout_length ..⟩
  exact h.head

/-! ## Constants fit the width -/

theorem addr_lt (C : CM.Program) : C.length * bsize (width C) < 2 ^ width C := by
  have hN : C.length ≤ C.length + regBound C := by omega
  generalize hm : C.length + regBound C = m at hN
  have hw : width C = m + m + 8 := by simp only [width, hm]; omega
  have hp : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have hb : bsize (width C) ≤ 2 ^ m * 172 := by
    have : bsize (width C) ≤ (m + 1) * 172 := by simp only [bsize, hw]; omega
    exact Nat.le_trans this (Nat.mul_le_mul_right _ hp)
  have hpos : 0 < 2 ^ m * 2 ^ m := Nat.mul_pos (Nat.two_pow_pos m) (Nat.two_pow_pos m)
  calc C.length * bsize (width C)
      ≤ 2 ^ m * (2 ^ m * 172) := Nat.mul_le_mul (by omega) hb
    _ = (2 ^ m * 2 ^ m) * 172 := by rw [Nat.mul_assoc]
    _ < (2 ^ m * 2 ^ m) * 256 := Nat.mul_lt_mul_of_pos_left (by omega) hpos
    _ = 2 ^ width C := by rw [hw, Nat.pow_add, Nat.pow_add]

theorem reg_le_inc {C : CM.Program} {j r : Nat} (h : C[j]? = some (.inc r)) : r ≤ regBound C := by
  induction C generalizing j with
  | nil => simp at h
  | cons x C ih =>
    cases j with
    | zero =>
      have : x = .inc r := by simpa using h
      subst this
      simp [regBound]
    | succ j =>
      have := ih (j := j) (by simpa using h)
      cases x <;> simp only [regBound] <;> omega

theorem reg_le_dec {C : CM.Program} {j r t : Nat} (h : C[j]? = some (.decJz r t)) :
    r ≤ regBound C := by
  induction C generalizing j with
  | nil => simp at h
  | cons x C ih =>
    cases j with
    | zero =>
      have : x = .decJz r t := by simpa using h
      subst this
      simp [regBound]
    | succ j =>
      have := ih (j := j) (by simpa using h)
      cases x <;> simp only [regBound] <;> omega

theorem reg_lt {C : CM.Program} {r : Nat} (h : r ≤ regBound C) : r < 2 ^ width C := by
  have h1 : width C < 2 ^ width C := Nat.lt_two_pow_self
  have h2 : r ≤ width C := by simp only [width]; omega
  omega

/-! ## Block correctness -/

theorem seq_pad (w : Nat) (m : Nat → Int) : Seq (pad w) [] m [] m := by
  have z := seq_pushW [] m w 0 (Nat.two_pow_pos w)
  have d := seq_drop ((0 : Nat) : Int) [] m
  exact (((((z.append d).append z).append d).append z).append d)

theorem seq_inc (w r : Nat) (m : Nat → Int) (hr : r < 2 ^ w) :
    Seq (incBlock w r) [] m [] (fun j => if j = r then m r + 1 else m j) := by
  have q := (((((seq_pushW [] m w r hr).append (seq_load r [] m)).append
    (seq_push 1 (by omega) _ m)).append (seq_add _ _ _ m)).append (seq_pushW _ m w r hr)).append
    (seq_store r _ _ m)
  exact q.append (seq_pad w _)

theorem seq_decPre (w r T J : Nat) (m : Nat → Int) (hr : r < 2 ^ w) (hT : T < 2 ^ w)
    (hJ : J < 2 ^ w) :
    Seq (decPre w r T J) [] m [(T : Int) - (J : Int), m r] m :=
  ((((seq_pushW [] m w r hr).append (seq_load r [] m)).append (seq_pushW _ m w T hT)).append
    (seq_pushW _ m w J hJ)).append (seq_sub _ _ _ m)

theorem seq_decPost (w r : Nat) (m : Nat → Int) (hr : r < 2 ^ w) :
    Seq (decPost w r) [] m [] (fun j => if j = r then m r - 1 else m j) :=
  (((((seq_pushW [] m w r hr).append (seq_load r [] m)).append
    (seq_push 1 (by omega) _ m)).append (seq_sub _ _ _ m)).append (seq_pushW _ m w r hr)).append
    (seq_store r _ _ m)

/-! ## Simulation -/

/-- The simulation relation: pc at the block start (clamped), empty stack, registers in memory. -/
def Rel (C : CM.Program) (c : CM.Config) (s : State) : Prop :=
  s.pc = min c.pc C.length * bsize (width C) ∧ s.stack = [] ∧ ∀ r, s.mem r = (c.regs r : Int)

/-- One counter-machine step is matched by at least one emd step, which gives divergence. -/
theorem sim_step {C : CM.Program} {c c' : CM.Config} {s : State} (hr : Rel C c s)
    (hs : CM.step C c = some c') :
    ∃ k s', 0 < k ∧ run (compile C) k s = .next s' ∧ Rel C c' s' := by
  obtain ⟨pc, st, m, i, o⟩ := s
  obtain ⟨hpc, hst, hm⟩ := hr
  simp only at hpc hst hm
  subst hst
  unfold CM.step at hs
  have hAddr := addr_lt C
  have hBpos : 0 < bsize (width C) := by simp [bsize]
  cases hi : C[c.pc]? with
  | none => simp [hi] at hs
  | some ins =>
    have hlt : c.pc < C.length := by
      rcases List.getElem?_eq_some_iff.mp hi with ⟨h, _⟩
      exact h
    rw [Nat.min_eq_left (by omega)] at hpc
    subst hpc
    have hat := compile_at hi
    have hLen := compile_length C
    have hNext : (c.pc + 1) * bsize (width C) ≤ C.length * bsize (width C) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at hNext
    cases ins with
    | halt => simp [hi] at hs
    | inc r =>
      simp only [hi, Option.some.injEq] at hs
      subst hs
      have hr' := reg_lt (reg_le_inc hi)
      have q := seq_inc (width C) r m hr' (compile C) _ i o hat
        (by rw [incBlock_length]; omega)
      refine ⟨_, _, by rw [incBlock_length]; omega, q, ?_, rfl, ?_⟩
      · show c.pc * bsize (width C) + (incBlock (width C) r).length = _
        rw [incBlock_length, Nat.min_eq_left (by simp only []; omega), Nat.add_mul, Nat.one_mul]
      · intro a
        show (if a = r then m r + 1 else m a) = _
        simp only [CM.update]
        by_cases ha : a = r
        · subst ha
          simp [hm]
        · simp [ha, hm]
    | decJz r t =>
      have hr' := reg_lt (reg_le_dec hi)
      generalize hT : min t C.length * bsize (width C) = T at hat
      have hTle : T ≤ C.length * bsize (width C) := by
        rw [← hT]
        exact Nat.mul_le_mul_right _ (by omega)
      generalize hJ : c.pc * bsize (width C) + (12 * width C + 5) = J at hat
      have hB : bsize (width C) = 20 * width C + 12 := rfl
      have hJlt : J + 1 < C.length * bsize (width C) + 1 := by omega
      have hBlock : (decPre (width C) r T J ++ [.jz] ++ decPost (width C) r) =
          block (width C) C.length c.pc (.decJz r t) := by
        simp only [block, hT, hJ]
      rw [← hBlock] at hat
      have hpre := seq_decPre (width C) r T J m hr' (by omega) (by omega)
        (compile C) _ i o hat.left.left (by rw [decPre_length]; omega)
      rw [decPre_length, hJ] at hpre
      by_cases hz : c.regs r = 0
      · simp only [hi, hz, ite_true, Option.some.injEq] at hs
        subst hs
        have hjz : (compile C)[J]? = some .jz := by
          have := hat.left.right
          rw [decPre_length, hJ] at this
          exact this.head
        have hmz : m r = 0 := by simp [hm, hz]
        have hstep := step_jz_taken (r := []) (m := m) (i := i) (o := o) hjz
          (target := T) (by omega) hmz
        have htot : run (compile C) (12 * width C + 5 + 1) ⟨c.pc * bsize (width C), [], m, i, o⟩ =
            .next ⟨T, [], m, i, o⟩ := by
          rw [run_add hpre]
          simp only [run, hstep]
        refine ⟨_, _, by omega, htot, ?_, rfl, hm⟩
        simp only [hT]
      · simp only [hi, hz, ite_false, Option.some.injEq] at hs
        subst hs
        have hmn : m r ≠ 0 := by simp [hm, hz]
        have q := (((seq_decPre (width C) r T J m hr' (by omega) (by omega)).append (seq_jz_fall _ _ _ m hmn)).append
          (seq_decPost (width C) r m hr')) (compile C) _ i o hat
          (by
            simp only [List.length_append, decPre_length, decPost_length, List.length_cons,
              List.length_nil]
            rw [hLen]
            omega)
        refine ⟨_, _, ?_, q, ?_, rfl, ?_⟩
        · simp [decPre_length]; omega
        · show c.pc * bsize (width C) + _ = _
          simp only [List.length_append, decPre_length, decPost_length, List.length_cons,
            List.length_nil]
          rw [Nat.min_eq_left (by omega), Nat.add_mul, Nat.one_mul]
          omega
        · intro a
          show (if a = r then m r - 1 else m a) = _
          simp only [CM.update]
          by_cases ha : a = r
          · subst ha
            have : (((c.regs a - 1 : Nat)) : Int) = (c.regs a : Int) - 1 := by omega
            simp [hm, this]
          · simp [ha, hm]

theorem sim_halt {C : CM.Program} {c : CM.Config} {s : State} (hr : Rel C c s)
    (hs : CM.step C c = none) : step (compile C) s = .halt s := by
  obtain ⟨hpc, _, _⟩ := hr
  have hx : (compile C)[s.pc]? = some .halt := by
    unfold CM.step at hs
    cases hi : C[c.pc]? with
    | none =>
      have : C.length ≤ c.pc := List.getElem?_eq_none_iff.mp hi
      rw [hpc, Nat.min_eq_right this]
      exact compile_end C
    | some ins =>
      have hlt : c.pc < C.length := by
        rcases List.getElem?_eq_some_iff.mp hi with ⟨h, _⟩
        exact h
      rw [hpc, Nat.min_eq_left (by omega)]
      cases ins with
      | halt => exact (compile_at hi).head
      | inc r => simp [hi] at hs
      | decJz r t =>
        simp only [hi] at hs
        split at hs <;> simp at hs
  simp only [step, hx, exec]

theorem sim_run {C : CM.Program} (k : Nat) {c c' : CM.Config} {s : State} (hr : Rel C c s)
    (h : CM.run C k c = some c') :
    ∃ fuel s', run (compile C) fuel s = .next s' ∧ Rel C c' s' := by
  induction k generalizing c s with
  | zero =>
    simp only [CM.run, Option.some.injEq] at h
    subst h
    exact ⟨0, s, rfl, hr⟩
  | succ k ih =>
    simp only [CM.run] at h
    cases hs : CM.step C c with
    | none => simp [hs] at h
    | some c₁ =>
      rw [hs] at h
      obtain ⟨n, s₁, _, h₁, hr₁⟩ := sim_step hr hs
      obtain ⟨fuel, s', h₂, hr'⟩ := ih hr₁ h
      exact ⟨n + fuel, s', by rw [run_add h₁]; exact h₂, hr'⟩

theorem sim_halts {C : CM.Program} {k : Nat} {c c' : CM.Config} {s : State} (hr : Rel C c s)
    (h : CM.run C k c = some c') (hh : CM.step C c' = none) :
    ∃ fuel s', run (compile C) fuel s = .halt s' ∧ s'.stack = [] ∧
      ∀ r, s'.mem r = (c'.regs r : Int) := by
  obtain ⟨fuel, s', h₁, hr'⟩ := sim_run k hr h
  refine ⟨fuel + 1, s', ?_, hr'.2.1, hr'.2.2⟩
  rw [run_add h₁]
  simp only [run, sim_halt hr' hh]

theorem not_halts_step {C : CM.Program} {c : CM.Config} (h : ¬ CM.Halts C c) :
    ∃ c', CM.step C c = some c' ∧ ¬ CM.Halts C c' := by
  cases hs : CM.step C c with
  | none => exact absurd ⟨0, c, rfl, hs⟩ h
  | some c' =>
    refine ⟨c', rfl, fun ⟨k, c'', h₁, h₂⟩ => h ⟨k + 1, c'', ?_, h₂⟩⟩
    simp only [CM.run, hs]
    exact h₁

theorem sim_diverges {C : CM.Program} (n : Nat) {c : CM.Config} {s : State} (hr : Rel C c s)
    (h : ¬ CM.Halts C c) : ∃ t, run (compile C) n s = .next t := by
  induction n using Nat.strongRecOn generalizing c s with
  | _ n ih =>
    obtain ⟨c', hs, hc'⟩ := not_halts_step h
    obtain ⟨k, s', hk, hrun, hr'⟩ := sim_step hr hs
    by_cases hn : n ≤ k
    · exact run_prefix hrun hn
    · obtain ⟨t, ht⟩ := ih (n - k) (by omega) hr' hc'
      have e : n = k + (n - k) := by omega
      exact ⟨t, by rw [e, run_add hrun]; exact ht⟩

/-! ## Main theorems -/

/-- The emd start state for registers `regs`: memory cell `r` holds register `r`. -/
def initState (regs : Nat → Nat) (input : List Nat) : State :=
  ⟨0, [], fun r => (regs r : Int), input, []⟩

theorem rel_init (C : CM.Program) (regs : Nat → Nat) (input : List Nat) :
    Rel C ⟨0, regs⟩ (initState regs input) :=
  ⟨by simp [initState], rfl, fun _ => rfl⟩

-- All-zero registers are the literal `State.init`; a CM prefix of `inc`s can load any input.
theorem initState_zero (input : List Nat) : initState (fun _ => 0) input = State.init input := by
  simp [initState, State.init]

/-- Halting direction: a halting counter machine yields a halting emd run with the same registers. -/
theorem simulates_halting (C : CM.Program) (regs : Nat → Nat) (input : List Nat) (k : Nat)
    (c' : CM.Config) (h : CM.run C k ⟨0, regs⟩ = some c') (hh : CM.step C c' = none) :
    ∃ fuel s, run (compile C) fuel (initState regs input) = .halt s ∧ s.stack = [] ∧
      ∀ r, s.mem r = (c'.regs r : Int) :=
  sim_halts (rel_init C regs input) h hh

/-- Divergence direction: at every fuel the emd run is alive, neither halted nor faulted. -/
theorem diverges_of_not_halts (C : CM.Program) (regs : Nat → Nat) (input : List Nat)
    (h : ¬ CM.Halts C ⟨0, regs⟩) (fuel : Nat) :
    ∃ s, run (compile C) fuel (initState regs input) = .next s :=
  sim_diverges fuel (rel_init C regs input) h

/-- The compiled program halts exactly when the counter machine does. -/
theorem halts_iff (C : CM.Program) (regs : Nat → Nat) (input : List Nat) :
    (∃ fuel s, run (compile C) fuel (initState regs input) = .halt s) ↔ CM.Halts C ⟨0, regs⟩ := by
  constructor
  · intro ⟨fuel, s, hs⟩
    apply Classical.byContradiction
    intro h
    obtain ⟨t, ht⟩ := diverges_of_not_halts C regs input h fuel
    rw [hs] at ht
    simp at ht
  · intro ⟨k, c', h, hh⟩
    obtain ⟨fuel, s, hs, _⟩ := simulates_halting C regs input k c' h hh
    exact ⟨fuel, s, hs⟩

/-- `halts_iff` from the literal `State.init` and all-zero registers. -/
theorem halts_iff_init (C : CM.Program) (input : List Nat) :
    (∃ fuel s, run (compile C) fuel (State.init input) = .halt s) ↔
      CM.Halts C ⟨0, fun _ => 0⟩ := by
  rw [← initState_zero]
  exact halts_iff C _ input

-- #print axioms simulates_halting
-- #print axioms diverges_of_not_halts
-- #print axioms halts_iff
-- #print axioms halts_iff_init

end Emd

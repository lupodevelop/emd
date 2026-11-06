import Emd.Universal
import Emd.Properties

/-! # emd simulates Turing machines directly, so universality needs no textbook reduction.

The tape lives in memory, one cell per position, and the head in cell 0. Position `h` goes to
cell `h + 2h² + 1`, an injective map from the integers to the positive naturals that takes no
branch to compute. Each state has a dispatcher that reads the symbol and jumps to its rule with
a relative offset computed at run time. The compiler avoids `dup` and `jmp`, so a small fragment
of the instruction set is already universal: see `compile_uses`. -/

namespace Emd

namespace TM

inductive Dir where
  | left
  | right

def Dir.shift : Dir → Int → Int
  | .left, h => h - 1
  | .right, h => h + 1

structure Rule where
  write : Nat
  move : Dir
  next : Nat

/-- `T[q][a]` is the rule for state `q` reading `a`. A state or symbol outside the table halts. -/
abbrev Machine := List (List Rule)

structure Config where
  state : Nat
  head : Int
  tape : Int → Nat

def apply (c : Config) (r : Rule) : Config :=
  ⟨r.next, r.move.shift c.head, fun h => if h = c.head then r.write else c.tape h⟩

def rule (T : Machine) (c : Config) : Option Rule :=
  T[c.state]?.bind fun row => row[c.tape c.head]?

def step (T : Machine) (c : Config) : Option Config := (rule T c).map (apply c)

def run (T : Machine) : Nat → Config → Option Config
  | 0, c => some c
  | k + 1, c => (step T c).bind (run T k)

def Halts (T : Machine) (c : Config) : Prop :=
  ∃ k c', run T k c = some c' ∧ step T c' = none

/-- A word on positions `0, 1, ...`, blank (0) everywhere else. -/
def wordTape (word : List Nat) : Int → Nat :=
  fun h => if 0 ≤ h then word.getD h.toNat 0 else 0

end TM

namespace Turing

/-! ## Tape addresses -/

def cell (h : Int) : Nat := (h + h * h * 2 + 1).toNat

theorem cell_value_pos (h : Int) : 1 ≤ h + h * h * 2 + 1 := by
  by_cases hh : 0 ≤ h
  · have := Int.mul_nonneg hh hh
    omega
  · have h1 : 0 ≤ (-h) * (-(h + 1)) := Int.mul_nonneg (by omega) (by omega)
    have h2 : (-h) * (-(h + 1)) = h * h + h := by
      rw [Int.neg_mul_neg, Int.mul_add, Int.mul_one]
    omega

theorem cell_cast (h : Int) : ((cell h : Nat) : Int) = h + h * h * 2 + 1 := by
  have := cell_value_pos h
  simp only [cell]
  omega

theorem cell_ne_zero (h : Int) : cell h ≠ 0 := by
  have := cell_value_pos h
  simp only [cell]
  omega

theorem cell_inj {a b : Int} (h : cell a = cell b) : a = b := by
  have e : ((cell a : Nat) : Int) = ((cell b : Nat) : Int) := by rw [h]
  rw [cell_cast, cell_cast] at e
  have hz : (a - b) * (1 + 2 * (a + b)) = 0 := by grind
  rcases Int.mul_eq_zero.mp hz with h1 | h1 <;> omega

/-! ## The code -/

def headCode (w : Nat) : List Instr := pushW w 0 ++ [.load]

-- Reads the head three times instead of duplicating it, so the fragment needs no `dup`.
def addrCode (w : Nat) : List Instr :=
  headCode w ++ headCode w ++ headCode w ++ [.mul] ++ [.push ⟨2, by omega⟩] ++ [.mul] ++ [.add] ++
    [.push ⟨1, by omega⟩] ++ [.add]

def bD (w : Nat) : Nat := 48 * w + 40

def bR (w : Nat) : Nat := 32 * w + 25

def bS (w K : Nat) : Nat := bD w + K * bR w

def readSym (w : Nat) : List Instr := addrCode w ++ [.load]

-- Leaves `Th - Jg`, the comparison and the symbol: the `jz` after it leaves when out of range.
def guard (w K Th Jg : Nat) : List Instr :=
  readSym w ++ pushW w K ++ [.lt] ++ pushW w Th ++ pushW w Jg ++ [.sub]

-- Rule `a` starts at `Rb + a * bR w`; `J` is the address of the `jz` that follows.
def select (w Rb J : Nat) : List Instr :=
  pushW w (bR w) ++ [.mul] ++ pushW w Rb ++ [.add] ++ pushW w J ++ [.sub]

-- The 0 pushed first stays under everything: the last `jz` is an unconditional jump.
def dispatch (w K Th E : Nat) : List Instr :=
  [.push ⟨0, by omega⟩] ++ readSym w ++ guard w K Th (E + (36 * w + 32)) ++ [.jz] ++
    select w (E + bD w) (E + (48 * w + 39)) ++ [.jz]

def writeCode (w v : Nat) : List Instr :=
  pushW w v ++ addrCode w ++ [.store]

def moveOp : TM.Dir → Instr
  | .left => .sub
  | .right => .add

def moveCode (w : Nat) (d : TM.Dir) : List Instr :=
  pushW w 0 ++ [.load] ++ [.push ⟨1, by omega⟩] ++ [moveOp d] ++ pushW w 0 ++ [.store]

def ruleBlock (w : Nat) (r : TM.Rule) (tgt start : Nat) : List Instr :=
  writeCode w r.write ++ moveCode w r.move ++ [.push ⟨0, by omega⟩] ++ pushW w tgt ++
    pushW w (start + (32 * w + 24)) ++ [.sub] ++ [.jz]

-- A symbol the row does not cover gets a block of `halt`, so every rule has an address.
def rules (w : Nat) (tgt : Nat → Nat) : Nat → Nat → List TM.Rule → List Instr
  | 0, _, _ => []
  | K + 1, start, [] => List.replicate (bR w) .halt ++ rules w tgt K (start + bR w) []
  | K + 1, start, r :: rs => ruleBlock w r (tgt r.next) start ++ rules w tgt K (start + bR w) rs

def region (w K : Nat) (tgt : Nat → Nat) (Th E : Nat) (row : List TM.Rule) : List Instr :=
  dispatch w K Th E ++ rules w tgt K (E + bD w) row

def layout (w K : Nat) (tgt : Nat → Nat) (Th : Nat) : Nat → TM.Machine → List Instr
  | _, [] => []
  | E, row :: rows => region w K tgt Th E row ++ layout w K tgt Th (E + bS w K) rows

/-- Writes the input word onto the tape before the machine starts. -/
def prologue (w : Nat) : Nat → List Nat → List Instr
  | _, [] => []
  | i, x :: xs => pushW w x ++ pushW w (cell (i : Int)) ++ [.store] ++ prologue w (i + 1) xs

def maxRow : TM.Machine → Nat
  | [] => 0
  | row :: rows => max row.length (maxRow rows)

def rowSum : List TM.Rule → Nat
  | [] => 0
  | r :: rs => r.write + rowSum rs

def symBound : TM.Machine → Nat
  | [] => 0
  | row :: rows => rowSum row + symBound rows

def wordSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + wordSum xs

def size (T : TM.Machine) (word : List Nat) : Nat :=
  T.length + maxRow T + symBound T + word.length + wordSum word

/-- Wide enough for every constant of the program: see `fits`. -/
def W (T : TM.Machine) (word : List Nat) : Nat := 3 * size T word + 12

def Bs (T : TM.Machine) (word : List Nat) : Nat := word.length * (8 * W T word + 3)

def Ss (T : TM.Machine) (word : List Nat) : Nat := bS (W T word) (maxRow T)

def Thh (T : TM.Machine) (word : List Nat) : Nat := Bs T word + T.length * Ss T word

-- Targets past the table clamp to the trailing `halt`, matching a state outside the table.
def Tgt (T : TM.Machine) (word : List Nat) (q : Nat) : Nat :=
  Bs T word + min q T.length * Ss T word

def compile (T : TM.Machine) (word : List Nat) : List Instr :=
  prologue (W T word) 0 word ++
    layout (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word) T ++ [.halt]

/-! ## Lengths -/

theorem addrCode_length (w : Nat) : (addrCode w).length = 12 * w + 12 := by
  simp [addrCode, headCode, pushW_length] <;> omega

theorem readSym_length (w : Nat) : (readSym w).length = 12 * w + 13 := by
  simp [readSym, addrCode_length]

theorem guard_length (w K Th Jg : Nat) : (guard w K Th Jg).length = 24 * w + 18 := by
  simp [guard, readSym_length, pushW_length] <;> omega

theorem select_length (w Rb J : Nat) : (select w Rb J).length = 12 * w + 6 := by
  simp [select, pushW_length] <;> omega

theorem dispatch_length (w K Th E : Nat) : (dispatch w K Th E).length = bD w := by
  simp [dispatch, readSym_length, guard_length, select_length, bD] <;> omega

theorem writeCode_length (w v : Nat) : (writeCode w v).length = 16 * w + 14 := by
  simp [writeCode, addrCode_length, pushW_length] <;> omega

theorem moveCode_length (w : Nat) (d : TM.Dir) : (moveCode w d).length = 8 * w + 6 := by
  simp [moveCode, pushW_length] <;> omega

theorem ruleBlock_length (w : Nat) (r : TM.Rule) (tgt start : Nat) :
    (ruleBlock w r tgt start).length = bR w := by
  simp [ruleBlock, writeCode_length, moveCode_length, pushW_length, bR] <;> omega

theorem rules_length (w : Nat) (tgt : Nat → Nat) (K start : Nat) (row : List TM.Rule) :
    (rules w tgt K start row).length = K * bR w := by
  induction K generalizing start row with
  | zero => simp [rules]
  | succ K ih =>
    cases row with
    | nil => simp only [rules, List.length_append, List.length_replicate, ih, Nat.add_mul]; omega
    | cons r rs =>
      simp only [rules, List.length_append, ruleBlock_length, ih, Nat.add_mul]; omega

theorem region_length (w K : Nat) (tgt : Nat → Nat) (Th E : Nat) (row : List TM.Rule) :
    (region w K tgt Th E row).length = bS w K := by
  simp [region, dispatch_length, rules_length, bS]

theorem layout_length (w K : Nat) (tgt : Nat → Nat) (Th E : Nat) (T : TM.Machine) :
    (layout w K tgt Th E T).length = T.length * bS w K := by
  induction T generalizing E with
  | nil => simp [layout]
  | cons row rows ih =>
    simp only [layout, List.length_append, region_length, ih, List.length_cons, Nat.add_mul]
    omega

theorem prologue_length (w i : Nat) (xs : List Nat) :
    (prologue w i xs).length = xs.length * (8 * w + 3) := by
  induction xs generalizing i with
  | nil => simp [prologue]
  | cons x xs ih =>
    simp only [prologue, List.length_append, pushW_length, ih, List.length_cons, Nat.add_mul]
    simp <;> omega

theorem compile_length (T : TM.Machine) (word : List Nat) :
    (compile T word).length = Thh T word + 1 := by
  simp [compile, prologue_length, layout_length, Thh, Bs, Ss] <;> omega

/-! ## Positions in the program -/

theorem _root_.Emd.At.comp {P l l' : List Instr} {a b : Nat} (h₁ : At P a l) (h₂ : At l b l') :
    At P (a + b) l' := by
  obtain ⟨pre, suf, e, hl⟩ := h₁
  obtain ⟨pre', suf', e', hl'⟩ := h₂
  exact ⟨pre ++ pre', suf' ++ suf, by simp [e, e'], by simp [hl, hl']⟩

theorem rules_at_some (w : Nat) (tgt : Nat → Nat) (K start : Nat) (row : List TM.Rule) (j : Nat)
    (r : TM.Rule) (hj : j < K) (h : row[j]? = some r) :
    At (rules w tgt K start row) (j * bR w) (ruleBlock w r (tgt r.next) (start + j * bR w)) := by
  induction K generalizing start row j with
  | zero => omega
  | succ K ih =>
    cases row with
    | nil => simp at h
    | cons x xs =>
      cases j with
      | zero =>
        have : x = r := by simpa using h
        subst this
        exact ⟨[], rules w tgt K (start + bR w) xs, by simp [rules], by simp⟩
      | succ j =>
        obtain ⟨pre, suf, e, hl⟩ := ih (start + bR w) xs j (by omega) (by simpa using h)
        have es : start + (j + 1) * bR w = start + bR w + j * bR w := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        rw [es]
        refine ⟨ruleBlock w x (tgt x.next) start ++ pre, suf, ?_, ?_⟩
        · simp only [rules, e, List.append_assoc]
        · simp only [List.length_append, ruleBlock_length, hl, Nat.add_mul]
          omega

theorem rules_at_none (w : Nat) (tgt : Nat → Nat) (K start : Nat) (row : List TM.Rule) (j : Nat)
    (hj : j < K) (h : row[j]? = none) : At (rules w tgt K start row) (j * bR w) [.halt] := by
  induction K generalizing start row j with
  | zero => omega
  | succ K ih =>
    cases j with
    | zero =>
      cases row with
      | nil =>
        refine ⟨[], List.replicate (32 * w + 24) .halt ++ rules w tgt K (start + bR w) [], ?_, ?_⟩
        · simp [rules, bR, List.replicate_succ]
        · simp
      | cons x xs => simp at h
    | succ j =>
      have hrec : ∀ (head : List Instr) (rs : List TM.Rule), head.length = bR w → rs[j]? = none →
          At (head ++ rules w tgt K (start + bR w) rs) ((j + 1) * bR w) [.halt] := by
        intro head rs hhead hrs
        obtain ⟨pre, suf, e, hl⟩ := ih (start + bR w) rs j (by omega) hrs
        refine ⟨head ++ pre, suf, by simp [e], ?_⟩
        simp only [List.length_append, hhead, hl, Nat.add_mul]
        omega
      cases row with
      | nil => exact hrec _ [] (by simp) (by simp)
      | cons x xs => exact hrec _ xs (ruleBlock_length ..) (by simpa using h)

theorem layout_at (w K : Nat) (tgt : Nat → Nat) (Th : Nat) (T : TM.Machine) (E q : Nat)
    (row : List TM.Rule) (h : T[q]? = some row) :
    At (layout w K tgt Th E T) (q * bS w K) (region w K tgt Th (E + q * bS w K) row) := by
  induction T generalizing E q with
  | nil => simp at h
  | cons x xs ih =>
    cases q with
    | zero =>
      have : x = row := by simpa using h
      subst this
      exact ⟨[], layout w K tgt Th (E + bS w K) xs, by simp [layout], by simp⟩
    | succ q =>
      obtain ⟨pre, suf, e, hl⟩ := ih (E + bS w K) q (by simpa using h)
      have es : E + (q + 1) * bS w K = E + bS w K + q * bS w K := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [es]
      refine ⟨region w K tgt Th E x ++ pre, suf, ?_, ?_⟩
      · simp only [layout, e, List.append_assoc]
      · simp only [List.length_append, region_length, hl, Nat.add_mul]
        omega

theorem compile_region {T : TM.Machine} (word : List Nat) {q : Nat} {row : List TM.Rule}
    (h : T[q]? = some row) :
    At (compile T word) (Bs T word + q * Ss T word)
      (region (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word + q * Ss T word) row) := by
  have hl : At (compile T word) (Bs T word)
      (layout (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word) T) :=
    ⟨prologue (W T word) 0 word, [.halt], by simp [compile], by simp [prologue_length, Bs]⟩
  exact hl.comp (layout_at _ _ _ _ T _ q row h)

theorem compile_end (T : TM.Machine) (word : List Nat) :
    (compile T word)[Thh T word]? = some .halt := by
  have h : At (compile T word) (Thh T word) [.halt] := by
    refine ⟨prologue (W T word) 0 word ++
      layout (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word) T, [], rfl, ?_⟩
    simp [prologue_length, layout_length, Thh, Bs, Ss]
  exact h.head

/-! ## Constants fit the width -/

theorem fits_aux (L n K s : Nat) (hL : L ≤ s) (hn : n ≤ s) (hK : K ≤ s) :
    L * (8 * (3 * s + 12) + 3) + n * bS (3 * s + 12) K < 2 ^ (3 * s + 12) := by
  have ha : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  generalize hx : 2 ^ s = x at ha
  generalize hA : s + 1 = a at ha
  have hp : 2 ^ (3 * s + 12) = x * x * x * 4096 := by
    have : 3 * s + 12 = s + s + s + 12 := by omega
    rw [this, Nat.pow_add, Nat.pow_add, Nat.pow_add, hx]
  have h1 : L * (8 * (3 * s + 12) + 3) ≤ a * (770 * a) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : K * bR (3 * s + 12) ≤ a * (770 * a) := Nat.mul_le_mul (by omega) (by simp only [bR]; omega)
  have h3 : bS (3 * s + 12) K ≤ 770 * a + a * (770 * a) := by
    simp only [bS, bD]
    omega
  have h4 : n * bS (3 * s + 12) K ≤ a * (770 * a + a * (770 * a)) :=
    Nat.mul_le_mul (by omega) h3
  have h5 : 0 < a := by omega
  have h6 : a * a ≤ a * a * a := Nat.le_mul_of_pos_right _ h5
  have h7 : a ≤ a * a := Nat.le_mul_of_pos_right _ h5
  have e1 : a * (770 * a) = 770 * (a * a) := by grind
  have e2 : a * (770 * a + a * (770 * a)) = 770 * (a * a) + 770 * (a * a * a) := by grind
  have h8 : a * a * a ≤ x * x * x :=
    Nat.mul_le_mul (Nat.mul_le_mul ha ha) ha
  rw [e1] at h1
  rw [e2] at h4
  have hpos : 0 < a * a * a := Nat.mul_pos (Nat.mul_pos h5 h5) h5
  rw [hp]
  omega

theorem fits (T : TM.Machine) (word : List Nat) : Thh T word < 2 ^ W T word := by
  have := fits_aux word.length T.length (maxRow T) (size T word)
    (by simp only [size]; omega) (by simp only [size]; omega) (by simp only [size]; omega)
  simpa only [Thh, Bs, Ss, W] using this

theorem size_lt (T : TM.Machine) (word : List Nat) : size T word < 2 ^ W T word := by
  refine Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) ?_)
  simp only [W]
  omega

theorem cell_nat (k : Nat) : cell (k : Int) = k + k * k * 2 + 1 := by
  have := cell_cast (k : Int)
  omega

theorem cell_fits (k s : Nat) (hk : k ≤ s) : cell (k : Int) < 2 ^ (3 * s + 12) := by
  rw [cell_nat]
  have ha : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  have hp : 2 ^ (3 * s + 12) = 2 ^ s * 2 ^ s * 2 ^ s * 4096 := by
    have : 3 * s + 12 = s + s + s + 12 := by omega
    rw [this, Nat.pow_add, Nat.pow_add, Nat.pow_add]
  generalize 2 ^ s = x at ha hp
  have h1 : k * k ≤ x * x := Nat.mul_le_mul (by omega) (by omega)
  have h2 : x * x ≤ x * x * x := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : k ≤ x * x := Nat.le_trans (by omega) (Nat.le_mul_of_pos_right x (by omega))
  have h4 : 0 < x * x * x := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  rw [hp]
  omega

theorem row_length_le {T : TM.Machine} {q : Nat} {row : List TM.Rule} (h : T[q]? = some row) :
    row.length ≤ maxRow T := by
  induction T generalizing q with
  | nil => simp at h
  | cons x xs ih =>
    cases q with
    | zero =>
      have : x = row := by simpa using h
      subst this
      simp only [maxRow]
      omega
    | succ q =>
      have := ih (q := q) (by simpa using h)
      simp only [maxRow]
      omega

theorem write_le_row {row : List TM.Rule} {j : Nat} {r : TM.Rule} (h : row[j]? = some r) :
    r.write ≤ rowSum row := by
  induction row generalizing j with
  | nil => simp at h
  | cons x xs ih =>
    cases j with
    | zero =>
      have : x = r := by simpa using h
      subst this
      simp only [rowSum]
      omega
    | succ j =>
      have := ih (j := j) (by simpa using h)
      simp only [rowSum]
      omega

theorem write_le {T : TM.Machine} {q j : Nat} {row : List TM.Rule} {r : TM.Rule}
    (h : T[q]? = some row) (hr : row[j]? = some r) : r.write ≤ symBound T := by
  have hw := write_le_row hr
  induction T generalizing q with
  | nil => simp at h
  | cons x xs ih =>
    cases q with
    | zero =>
      have : x = row := by simpa using h
      subst this
      simp only [symBound]
      omega
    | succ q =>
      have := ih (q := q) (by simpa using h)
      simp only [symBound]
      omega

theorem mem_le_wordSum {x : Nat} {xs : List Nat} (h : x ∈ xs) : x ≤ wordSum xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [wordSum]
    rcases List.mem_cons.mp h with rfl | h'
    · omega
    · have := ih h'
      omega

/-! ## Straight-line pieces -/

theorem seq_lt (b a : Int) (r : List Int) (m : Nat → Int) :
    Seq [.lt] (b :: a :: r) m (b2i (a < b) :: r) m :=
  seq_single fun _ _ _ _ h => advance_ok h

theorem seq_head (w : Nat) (r : List Int) (m : Nat → Int) :
    Seq (headCode w) r m (m 0 :: r) m :=
  (seq_pushW r m w 0 (Nat.two_pow_pos w)).append (seq_load 0 r m)

theorem seq_addr (w : Nat) (h : Int) (r : List Int) (m : Nat → Int) (hh : m 0 = h) :
    Seq (addrCode w) r m (((cell h : Nat) : Int) :: r) m := by
  subst hh
  have q := ((((((((seq_head w r m).append (seq_head w _ m)).append (seq_head w _ m)).append
    (seq_mul _ _ _ m)).append (seq_push 2 (by omega) _ m)).append (seq_mul _ _ _ m)).append
    (seq_add _ _ _ m)).append (seq_push 1 (by omega) _ m)).append (seq_add _ _ _ m)
  have e : m 0 + m 0 * m 0 * ((2 : Nat) : Int) + ((1 : Nat) : Int) = ((cell (m 0) : Nat) : Int) := by
    rw [cell_cast]
    rfl
  rw [e] at q
  exact q

theorem seq_readSym (w : Nat) (r : List Int) (m : Nat → Int) (h : Int) (hh : m 0 = h) :
    Seq (readSym w) r m (m (cell h) :: r) m :=
  (seq_addr w h r m hh).append (seq_load (cell h) r m)

theorem seq_guard (w K Th Jg : Nat) (h a : Int) (r : List Int) (m : Nat → Int) (hh : m 0 = h)
    (hv : m (cell h) = a) (hK : K < 2 ^ w) (hTh : Th < 2 ^ w) (hJg : Jg < 2 ^ w) :
    Seq (guard w K Th Jg) (a :: r) m
      (((Th : Int) - (Jg : Int)) :: b2i (a < (K : Int)) :: a :: r) m := by
  have qR := seq_readSym w (a :: r) m h hh
  rw [hv] at qR
  exact (((((qR.append (seq_pushW _ m w K hK)).append (seq_lt _ _ _ m)).append
    (seq_pushW _ m w Th hTh)).append (seq_pushW _ m w Jg hJg)).append (seq_sub _ _ _ m))

theorem seq_select (w Rb J : Nat) (a : Int) (r : List Int) (m : Nat → Int) (hR : bR w < 2 ^ w)
    (hRb : Rb < 2 ^ w) (hJ : J < 2 ^ w) :
    Seq (select w Rb J) (a :: r) m ((a * (bR w : Int) + (Rb : Int) - (J : Int)) :: r) m :=
  (((((seq_pushW _ m w (bR w) hR).append (seq_mul _ _ _ m)).append (seq_pushW _ m w Rb hRb)).append
    (seq_add _ _ _ m)).append (seq_pushW _ m w J hJ)).append (seq_sub _ _ _ m)

theorem seq_write (w v : Nat) (h : Int) (m : Nat → Int) (hh : m 0 = h) (hv : v < 2 ^ w) :
    Seq (writeCode w v) [] m [] (fun j => if j = cell h then (v : Int) else m j) :=
  ((seq_pushW [] m w v hv).append (seq_addr w h _ m hh)).append (seq_store (cell h) _ [] m)

theorem seq_moveOp (d : TM.Dir) (h : Int) (r : List Int) (m : Nat → Int) :
    Seq [moveOp d] (((1 : Nat) : Int) :: h :: r) m (d.shift h :: r) m := by
  cases d
  · exact seq_sub _ _ _ m
  · exact seq_add _ _ _ m

theorem seq_move (w : Nat) (d : TM.Dir) (h : Int) (m : Nat → Int) (hh : m 0 = h) :
    Seq (moveCode w d) [] m [] (fun j => if j = 0 then d.shift h else m j) := by
  subst hh
  exact ((((((seq_pushW [] m w 0 (Nat.two_pow_pos w)).append (seq_load 0 [] m)).append
    (seq_push 1 (by omega) _ m)).append (seq_moveOp d (m 0) [] m)).append
    (seq_pushW _ m w 0 (Nat.two_pow_pos w))).append (seq_store 0 _ [] m))

/-! ## Dispatch and rules -/

theorem step_jz_to {P : List Instr} {a target : Nat} {off c : Int} {r : List Int} {m : Nat → Int}
    {i o : List Nat} (hx : P[a]? = some .jz) (ht : target < P.length) (hc : c = 0)
    (he : (a : Int) + off = target) :
    step P ⟨a, off :: c :: r, m, i, o⟩ = .next ⟨target, r, m, i, o⟩ := by
  have h0 : (0 : Int) ≤ target := by omega
  have h1 : (target : Int) < (P.length : Int) := by omega
  simp only [step, hx, exec]
  rw [ite_eq_left hc]
  simp only [jumpTo, he]
  rw [ite_eq_left ⟨h0, h1⟩, Int.toNat_natCast]

/-- A symbol below `K`: the dispatcher reaches its rule with an empty stack. -/
theorem dispatch_fall {P : List Instr} {w K Th E a : Nat} {h : Int} {m : Nat → Int}
    {i o : List Nat} (hAt : At P E (dispatch w K Th E)) (hm : m 0 = h)
    (hv : m (cell h) = (a : Int)) (ha : a < K) (hK : K < 2 ^ w) (hTh : Th < 2 ^ w)
    (hE : E + bD w < 2 ^ w) (hR : bR w < 2 ^ w) (hT : E + bD w + a * bR w < P.length) :
    ∃ L, 0 < L ∧ run P L ⟨E, [], m, i, o⟩ = .next ⟨E + bD w + a * bR w, [], m, i, o⟩ := by
  have hbD : bD w = 48 * w + 40 := rfl
  have hc : b2i ((a : Int) < (K : Int)) ≠ 0 := by
    have : (a : Int) < K := by omega
    simp [b2i, this]
  have qR := seq_readSym w [((0 : Nat) : Int)] m h hm
  rw [hv] at qR
  have qS := ((((seq_push 0 (by omega) [] m).append qR).append
    (seq_guard w K Th (E + (36 * w + 32)) h _ _ m hm hv hK hTh (by omega))).append
    (seq_jz_fall _ _ _ m hc)).append (seq_select w (E + bD w) (E + (48 * w + 39)) _ _ m hR hE
    (by omega))
  have hAt' : At P E ([Instr.push ⟨0, by omega⟩] ++ readSym w ++
      guard w K Th (E + (36 * w + 32)) ++ [Instr.jz] ++
      select w (E + bD w) (E + (48 * w + 39)) ++ [Instr.jz]) := hAt
  have hlA : ([Instr.push ⟨0, by omega⟩] ++ readSym w ++
      guard w K Th (E + (36 * w + 32)) ++ [Instr.jz] ++
      select w (E + bD w) (E + (48 * w + 39))).length = 48 * w + 39 := by
    simp [readSym_length, guard_length, select_length] <;> omega
  have e := qS P E i o hAt'.left (by rw [hlA]; omega)
  rw [hlA] at e
  have hx : P[E + (48 * w + 39)]? = some .jz := by
    have := hAt'.right
    rw [hlA] at this
    exact this.head
  have hstep := step_jz_to (r := []) (m := m) (i := i) (o := o) (c := ((0 : Nat) : Int))
    (off := (a : Int) * (bR w : Int) + ((E + bD w : Nat) : Int) - ((E + (48 * w + 39) : Nat) : Int))
    hx hT rfl (by omega)
  exact ⟨48 * w + 39 + 1, by omega, by rw [run_add e]; simp only [run, hstep]⟩

/-- A symbol out of range: the dispatcher leaves for the trailing `halt`. -/
theorem dispatch_out {P : List Instr} {w K Th E a : Nat} {h : Int} {m : Nat → Int}
    {i o : List Nat} (hAt : At P E (dispatch w K Th E)) (hm : m 0 = h)
    (hv : m (cell h) = (a : Int)) (ha : K ≤ a) (hK : K < 2 ^ w) (hTh : Th < 2 ^ w)
    (hJ : E + (36 * w + 32) < 2 ^ w) (hT : Th < P.length) (hE : E + (36 * w + 32) < P.length) :
    ∃ L, run P L ⟨E, [], m, i, o⟩ = .next ⟨Th, [(a : Int), ((0 : Nat) : Int)], m, i, o⟩ := by
  have hc : b2i ((a : Int) < (K : Int)) = 0 := by
    have : ¬ (a : Int) < K := by omega
    simp [b2i, this]
  have qR := seq_readSym w [((0 : Nat) : Int)] m h hm
  rw [hv] at qR
  have qS := ((seq_push 0 (by omega) [] m).append qR).append
    (seq_guard w K Th (E + (36 * w + 32)) h _ _ m hm hv hK hTh hJ)
  have hAt' : At P E ([Instr.push ⟨0, by omega⟩] ++ readSym w ++
      guard w K Th (E + (36 * w + 32)) ++ [Instr.jz] ++
      select w (E + bD w) (E + (48 * w + 39)) ++ [Instr.jz]) := hAt
  have hA := hAt'.left.left
  have hlA : ([Instr.push ⟨0, by omega⟩] ++ readSym w ++
      guard w K Th (E + (36 * w + 32))).length = 36 * w + 32 := by
    simp [readSym_length, guard_length] <;> omega
  have e := qS P E i o hA.left (by rw [hlA]; omega)
  rw [hlA] at e
  have hx : P[E + (36 * w + 32)]? = some .jz := by
    have := hA.right
    rw [hlA] at this
    exact this.head
  have hstep := step_jz_taken (r := [(a : Int), ((0 : Nat) : Int)]) (m := m) (i := i) (o := o)
    hx hT hc
  exact ⟨36 * w + 32 + 1, by rw [run_add e]; simp only [run, hstep]⟩

/-- `m` holds configuration `c`: the head in cell 0, the tape at `cell`. -/
def Tracks (m : Nat → Int) (c : TM.Config) : Prop :=
  m 0 = c.head ∧ ∀ h, m (cell h) = (c.tape h : Int)

/-- A rule block writes, moves and jumps to the next state. -/
theorem rule_step {P : List Instr} {w tgt start : Nat} {r : TM.Rule} {m : Nat → Int}
    {i o : List Nat} {c : TM.Config} (hAt : At P start (ruleBlock w r tgt start))
    (ht : Tracks m c) (hv : r.write < 2 ^ w) (hT : tgt < 2 ^ w)
    (hJ : start + (32 * w + 24) < 2 ^ w) (hLen : tgt < P.length)
    (hb : start + (32 * w + 24) < P.length) :
    ∃ L m', 0 < L ∧ run P L ⟨start, [], m, i, o⟩ = .next ⟨tgt, [], m', i, o⟩ ∧
      Tracks m' (TM.apply c r) := by
  have h1 : (fun j => if j = cell c.head then (r.write : Int) else m j) 0 = c.head := by
    have : (0 : Nat) ≠ cell c.head := fun e => cell_ne_zero _ e.symm
    simp [this, ht.1]
  have qS := ((((((seq_write w r.write c.head m ht.1 hv).append
    (seq_move w r.move c.head _ h1)).append (seq_push 0 (by omega) [] _)).append
    (seq_pushW _ _ w tgt hT)).append (seq_pushW _ _ w (start + (32 * w + 24)) hJ)).append
    (seq_sub _ _ _ _))
  have hAt' : At P start (writeCode w r.write ++ moveCode w r.move ++
      [Instr.push ⟨0, by omega⟩] ++ pushW w tgt ++
      pushW w (start + (32 * w + 24)) ++ [Instr.sub] ++ [Instr.jz]) := hAt
  have hlA : (writeCode w r.write ++ moveCode w r.move ++
      [Instr.push ⟨0, by omega⟩] ++ pushW w tgt ++
      pushW w (start + (32 * w + 24)) ++ [Instr.sub]).length = 32 * w + 24 := by
    simp [writeCode_length, moveCode_length, pushW_length] <;> omega
  have e := qS P start i o hAt'.left (by rw [hlA]; omega)
  rw [hlA] at e
  have hx : P[start + (32 * w + 24)]? = some .jz := by
    have := hAt'.right
    rw [hlA] at this
    exact this.head
  have hstep := step_jz_to (r := []) (i := i) (o := o) (c := ((0 : Nat) : Int))
    (m := fun j => if j = 0 then r.move.shift c.head else
      if j = cell c.head then (r.write : Int) else m j)
    (off := (tgt : Int) - ((start + (32 * w + 24) : Nat) : Int)) hx hLen rfl (by omega)
  refine ⟨32 * w + 24 + 1, fun j => if j = 0 then r.move.shift c.head else
    if j = cell c.head then (r.write : Int) else m j, by omega,
    by rw [run_add e]; simp only [run, hstep], ?_, ?_⟩
  · simp [TM.apply]
  · intro x
    have hx0 : cell x ≠ 0 := cell_ne_zero x
    by_cases hxh : x = c.head
    · subst hxh
      simp [TM.apply, hx0]
    · have hne : cell x ≠ cell c.head := fun e => hxh (cell_inj e)
      simp [TM.apply, hx0, hne, hxh, ht.2 x]

/-! ## Simulation -/

/-- The simulation relation: `pc` at the state's dispatcher, empty stack, the tape in memory. -/
def Rel (T : TM.Machine) (word : List Nat) (c : TM.Config) (s : State) : Prop :=
  s.pc = Tgt T word c.state ∧ s.stack = [] ∧ Tracks s.mem c

theorem state_bounds (T : TM.Machine) (word : List Nat) {q : Nat} (hq : q < T.length) :
    Bs T word + q * Ss T word + Ss T word ≤ Thh T word := by
  have : (q + 1) * Ss T word ≤ T.length * Ss T word := Nat.mul_le_mul_right _ hq
  rw [Nat.add_mul, Nat.one_mul] at this
  simp only [Thh]
  omega

theorem tgt_le (T : TM.Machine) (word : List Nat) (q : Nat) : Tgt T word q ≤ Thh T word := by
  have : min q T.length * Ss T word ≤ T.length * Ss T word :=
    Nat.mul_le_mul_right _ (by omega)
  simp only [Tgt, Thh]
  omega

/-- One machine step is matched by at least one emd step, which gives divergence. -/
theorem sim_step {T : TM.Machine} {word : List Nat} {c c' : TM.Config} {s : State}
    (hr : Rel T word c s) (hs : TM.step T c = some c') :
    ∃ k s', 0 < k ∧ run (compile T word) k s = .next s' ∧ Rel T word c' s' ∧
      s'.input = s.input ∧ s'.output = s.output := by
  obtain ⟨pc, st, m, i, o⟩ := s
  obtain ⟨hpc, hst, ht⟩ := hr
  simp only at hpc hst ht
  subst hst
  simp only [TM.step, TM.rule, Option.map_eq_some_iff, Option.bind_eq_some_iff] at hs
  obtain ⟨r, ⟨row, hrow, hrule⟩, rfl⟩ := hs
  have hq : c.state < T.length := by
    rcases List.getElem?_eq_some_iff.mp hrow with ⟨h, _⟩
    exact h
  have ha : c.tape c.head < row.length := by
    rcases List.getElem?_eq_some_iff.mp hrule with ⟨h, _⟩
    exact h
  have haK : c.tape c.head < maxRow T := Nat.lt_of_lt_of_le ha (row_length_le hrow)
  have hpc' : pc = Bs T word + c.state * Ss T word := by
    rw [hpc, Tgt, Nat.min_eq_left (by omega)]
  subst hpc'
  have hReg := compile_region word hrow
  have hEnd := state_bounds T word hq
  have hFit := fits T word
  have hSize := size_lt T word
  have hLen := compile_length T word
  have hS : Ss T word = bD (W T word) + maxRow T * bR (W T word) := rfl
  have hbD : bD (W T word) = 48 * W T word + 40 := rfl
  have hbR : bR (W T word) = 32 * W T word + 25 := rfl
  have hKs : maxRow T ≤ size T word := by simp only [size]; omega
  have hWs : symBound T ≤ size T word := by simp only [size]; omega
  have hStep : (c.tape c.head + 1) * bR (W T word) ≤ maxRow T * bR (W T word) :=
    Nat.mul_le_mul_right _ haK
  rw [Nat.add_mul, Nat.one_mul] at hStep
  generalize hE : Bs T word + c.state * Ss T word = E at hReg hEnd
  have hDisp := hReg.left
  obtain ⟨L₁, hL₁, h₁⟩ := dispatch_fall (i := i) (o := o) (a := c.tape c.head) hDisp ht.1 (ht.2 _)
    haK (by omega) hFit (by omega) (by omega) (by omega)
  have hAtRule := hReg.right.comp
    (rules_at_some (W T word) (Tgt T word) (maxRow T) (E + bD (W T word)) row (c.tape c.head) r
      haK hrule)
  rw [dispatch_length] at hAtRule
  have hTgt := tgt_le T word r.next
  have hw := write_le hrow hrule
  obtain ⟨L₂, m', hL₂, h₂, ht'⟩ := rule_step (i := i) (o := o) hAtRule ht
    (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨L₁ + L₂, ⟨Tgt T word r.next, [], m', i, o⟩, by omega, ?_, ⟨rfl, rfl, ht'⟩, rfl, rfl⟩
  rw [run_add h₁]
  exact h₂

/-- A machine that stops is matched by a `halt`, memory unchanged. -/
theorem sim_halt {T : TM.Machine} {word : List Nat} {c : TM.Config} {s : State}
    (hr : Rel T word c s) (hs : TM.step T c = none) :
    ∃ fuel s', run (compile T word) fuel s = .halt s' ∧ s'.mem = s.mem ∧ s'.input = s.input ∧
      s'.output = s.output := by
  obtain ⟨pc, st, m, i, o⟩ := s
  obtain ⟨hpc, hst, ht⟩ := hr
  simp only at hpc hst ht
  subst hst
  have hFit := fits T word
  have hSize := size_lt T word
  have hLen := compile_length T word
  have hEndHalt := compile_end T word
  have hKs : maxRow T ≤ size T word := by simp only [size]; omega
  have stopAt : ∀ (a : Nat) (st : List Int), (compile T word)[a]? = some .halt →
      run (compile T word) 1 ⟨a, st, m, i, o⟩ = .halt ⟨a, st, m, i, o⟩ := by
    intro a st hx
    simp only [run, step, hx, exec]
  cases hrow : T[c.state]? with
  | none =>
    have hge : T.length ≤ c.state := List.getElem?_eq_none_iff.mp hrow
    have : pc = Thh T word := by rw [hpc, Tgt, Nat.min_eq_right hge, Thh]
    subst this
    exact ⟨1, _, stopAt _ _ hEndHalt, rfl, rfl, rfl⟩
  | some row =>
    have hq : c.state < T.length := by
      rcases List.getElem?_eq_some_iff.mp hrow with ⟨h, _⟩
      exact h
    have hnone : row[c.tape c.head]? = none := by
      simpa [TM.step, TM.rule, hrow] using hs
    have hpc' : pc = Bs T word + c.state * Ss T word := by
      rw [hpc, Tgt, Nat.min_eq_left (by omega)]
    subst hpc'
    have hReg := compile_region word hrow
    have hEnd := state_bounds T word hq
    have hS : Ss T word = bD (W T word) + maxRow T * bR (W T word) := rfl
    have hbD : bD (W T word) = 48 * W T word + 40 := rfl
    have hbR : bR (W T word) = 32 * W T word + 25 := rfl
    generalize hE : Bs T word + c.state * Ss T word = E at hReg hEnd
    have hDisp := hReg.left
    by_cases haK : c.tape c.head < maxRow T
    · have hStep : (c.tape c.head + 1) * bR (W T word) ≤ maxRow T * bR (W T word) :=
        Nat.mul_le_mul_right _ haK
      rw [Nat.add_mul, Nat.one_mul] at hStep
      obtain ⟨L₁, _, h₁⟩ := dispatch_fall (i := i) (o := o) (a := c.tape c.head) hDisp ht.1 (ht.2 _)
        haK (by omega) hFit (by omega) (by omega) (by omega)
      have hAtHalt := hReg.right.comp
        (rules_at_none (W T word) (Tgt T word) (maxRow T) (E + bD (W T word)) row (c.tape c.head)
          haK hnone)
      rw [dispatch_length] at hAtHalt
      refine ⟨L₁ + 1, ⟨E + bD (W T word) + c.tape c.head * bR (W T word), [], m, i, o⟩, ?_, rfl, rfl, rfl⟩
      rw [run_add h₁]
      exact stopAt _ _ hAtHalt.head
    · obtain ⟨L₁, h₁⟩ := dispatch_out (i := i) (o := o) (a := c.tape c.head) hDisp ht.1 (ht.2 _)
        (by omega) (by omega) hFit (by omega) (by omega) (by omega)
      refine ⟨L₁ + 1, ⟨Thh T word, [(c.tape c.head : Int), ((0 : Nat) : Int)], m, i, o⟩, ?_, rfl, rfl, rfl⟩
      rw [run_add h₁]
      exact stopAt _ _ hEndHalt

theorem sim_run {T : TM.Machine} {word : List Nat} (k : Nat) {c c' : TM.Config} {s : State}
    (hr : Rel T word c s) (h : TM.run T k c = some c') :
    ∃ fuel s', run (compile T word) fuel s = .next s' ∧ Rel T word c' s' ∧
      s'.input = s.input ∧ s'.output = s.output := by
  induction k generalizing c s with
  | zero =>
    simp only [TM.run, Option.some.injEq] at h
    subst h
    exact ⟨0, s, rfl, hr, rfl, rfl⟩
  | succ k ih =>
    simp only [TM.run] at h
    cases hs : TM.step T c with
    | none => simp [hs] at h
    | some c₁ =>
      rw [hs] at h
      obtain ⟨n, s₁, _, h₁, hr₁, hi₁, ho₁⟩ := sim_step hr hs
      obtain ⟨fuel, s', h₂, hr', hi', ho'⟩ := ih hr₁ h
      exact ⟨n + fuel, s', by rw [run_add h₁]; exact h₂, hr', hi'.trans hi₁, ho'.trans ho₁⟩

theorem not_halts_step {T : TM.Machine} {c : TM.Config} (h : ¬ TM.Halts T c) :
    ∃ c', TM.step T c = some c' ∧ ¬ TM.Halts T c' := by
  cases hs : TM.step T c with
  | none => exact absurd ⟨0, c, rfl, hs⟩ h
  | some c' =>
    refine ⟨c', rfl, fun ⟨k, c'', h₁, h₂⟩ => h ⟨k + 1, c'', ?_, h₂⟩⟩
    simp only [TM.run, hs]
    exact h₁

theorem sim_diverges {T : TM.Machine} {word : List Nat} (n : Nat) {c : TM.Config} {s : State}
    (hr : Rel T word c s) (h : ¬ TM.Halts T c) : ∃ t, run (compile T word) n s = .next t := by
  induction n using Nat.strongRecOn generalizing c s with
  | _ n ih =>
    obtain ⟨c', hs, hc'⟩ := not_halts_step h
    obtain ⟨k, s', hk, hrun, hr', _⟩ := sim_step hr hs
    by_cases hn : n ≤ k
    · exact run_prefix hrun hn
    · obtain ⟨t, ht⟩ := ih (n - k) (by omega) hr' hc'
      have e : n = k + (n - k) := by omega
      exact ⟨t, by rw [e, run_add hrun]; exact ht⟩

/-- A machine that halts is matched by a halting emd run whose memory holds the final tape. -/
theorem simulates_halting {T : TM.Machine} {word : List Nat} {c c' : TM.Config} {s : State} {k : Nat}
    (hr : Rel T word c s) (h : TM.run T k c = some c') (hh : TM.step T c' = none) :
    ∃ fuel s', run (compile T word) fuel s = .halt s' ∧ Tracks s'.mem c' ∧
      s'.input = s.input ∧ s'.output = s.output := by
  obtain ⟨n, s₁, h₁, hr₁, hi₁, ho₁⟩ := sim_run k hr h
  obtain ⟨f, s', h₂, hm, hi₂, ho₂⟩ := sim_halt hr₁ hh
  exact ⟨n + f, s', by rw [run_add h₁]; exact h₂, by rw [hm]; exact hr₁.2.2,
    hi₂.trans hi₁, ho₂.trans ho₁⟩

/-- From any state related to `c`, the compiled program halts exactly when the machine does. -/
theorem halts_iff {T : TM.Machine} {word : List Nat} {c : TM.Config} {s : State}
    (hr : Rel T word c s) :
    (∃ fuel s', run (compile T word) fuel s = .halt s') ↔ TM.Halts T c := by
  constructor
  · intro ⟨fuel, s', hs⟩
    apply Classical.byContradiction
    intro h
    obtain ⟨t, ht⟩ := sim_diverges fuel hr h
    rw [hs] at ht
    simp at ht
  · intro ⟨k, c', h, hh⟩
    obtain ⟨fuel, s', hs, _⟩ := simulates_halting hr h hh
    exact ⟨fuel, s', hs⟩

/-! ## The input word -/

def writeWord : (Nat → Int) → Nat → List Nat → (Nat → Int)
  | m, _, [] => m
  | m, i, x :: xs => writeWord (fun j => if j = cell (i : Int) then (x : Int) else m j) (i + 1) xs

theorem seq_prologue (w i : Nat) (xs : List Nat) (m : Nat → Int) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (hc : ∀ k, i ≤ k → k < i + xs.length → cell (k : Int) < 2 ^ w) :
    Seq (prologue w i xs) [] m [] (writeWord m i xs) := by
  induction xs generalizing i m with
  | nil => exact fun _ _ _ _ _ _ => rfl
  | cons x xs ih =>
    have q := ((seq_pushW [] m w x (hx x (by simp))).append
      (seq_pushW _ m w (cell (i : Int)) (hc i (by omega) (by simp)))).append
      (seq_store (cell (i : Int)) _ [] m)
    exact q.append (ih (i + 1) _ (fun y hy => hx y (by simp [hy]))
      (fun k h₁ h₂ => hc k (by omega) (by simp only [List.length_cons]; omega)))

theorem writeWord_zero (m : Nat → Int) (i : Nat) (xs : List Nat) : writeWord m i xs 0 = m 0 := by
  induction xs generalizing m i with
  | nil => rfl
  | cons x xs ih =>
    simp only [writeWord, ih]
    have : (0 : Nat) ≠ cell (i : Int) := fun e => cell_ne_zero _ e.symm
    simp [this]

theorem writeWord_cell (m : Nat → Int) (i : Nat) (xs : List Nat) (h : Int) :
    writeWord m i xs (cell h) =
      if (i : Int) ≤ h ∧ h < i + xs.length then ((xs.getD (h - i).toNat 0 : Nat) : Int)
      else m (cell h) := by
  induction xs generalizing m i with
  | nil =>
    have : ¬ ((i : Int) ≤ h ∧ h < i + ([] : List Nat).length) := by
      simp only [List.length_nil]
      omega
    rw [ite_eq_right this]
    rfl
  | cons x xs ih =>
    simp only [writeWord, ih]
    by_cases hh : h = (i : Int)
    · subst hh
      have h1 : ¬ (((i + 1 : Nat) : Int) ≤ (i : Int) ∧ (i : Int) < ((i + 1 : Nat) : Int) + xs.length) := by
        omega
      have h2 : (i : Int) ≤ i ∧ (i : Int) < i + (x :: xs).length := by
        simp only [List.length_cons]
        omega
      rw [ite_eq_right h1, ite_eq_left h2]
      simp
    · have hne : cell h ≠ cell (i : Int) := fun e => hh (cell_inj e)
      simp only [hne, ite_false]
      by_cases hin : (i : Int) < h ∧ h < i + (xs.length + 1 : Nat)
      · have h1 : ((i + 1 : Nat) : Int) ≤ h ∧ h < ((i + 1 : Nat) : Int) + xs.length := by omega
        have h2 : (i : Int) ≤ h ∧ h < i + (x :: xs).length := by
          simp only [List.length_cons]
          omega
        rw [ite_eq_left h1, ite_eq_left h2]
        have e : (h - (i : Int)).toNat = (h - ((i + 1 : Nat) : Int)).toNat + 1 := by omega
        rw [e]
        simp
      · have h1 : ¬ (((i + 1 : Nat) : Int) ≤ h ∧ h < ((i + 1 : Nat) : Int) + xs.length) := by omega
        have h2 : ¬ ((i : Int) ≤ h ∧ h < i + (x :: xs).length) := by
          simp only [List.length_cons]
          omega
        rw [ite_eq_right h1, ite_eq_right h2]

theorem tracks_word (word : List Nat) :
    Tracks (writeWord (fun _ => 0) 0 word) ⟨0, 0, TM.wordTape word⟩ := by
  constructor
  · exact writeWord_zero _ _ _
  · intro h
    rw [writeWord_cell]
    simp only [TM.wordTape]
    by_cases h0 : 0 ≤ h
    · by_cases h1 : h < word.length
      · simp [h0, h1]
      · simp [h0, h1, List.getD_eq_getElem?_getD]
    · simp [h0]

/-- The prologue leaves the machine at state 0, head 0, with the word on the tape. -/
theorem prologue_run (T : TM.Machine) (word input : List Nat) :
    ∃ n s, run (compile T word) n (State.init input) = .next s ∧
      Rel T word ⟨0, 0, TM.wordTape word⟩ s ∧ s.input = input ∧ s.output = [] := by
  have hFit := fits T word
  have hLen := compile_length T word
  have hBs : Bs T word ≤ Thh T word := by simp only [Thh]; omega
  have hAt : At (compile T word) 0 (prologue (W T word) 0 word) :=
    ⟨[], layout (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word) T ++ [.halt],
      by simp [compile], rfl⟩
  have hl : (prologue (W T word) 0 word).length = Bs T word := by
    simp [prologue_length, Bs]
  have q := seq_prologue (W T word) 0 word (fun _ => 0)
    (fun x hx => by
      have h1 := mem_le_wordSum hx
      have h2 := size_lt T word
      have h3 : wordSum word ≤ size T word := by simp only [size]; omega
      omega)
    (fun k _ hk => cell_fits k (size T word) (by simp only [size]; omega))
    (compile T word) 0 input [] hAt (by rw [hl]; omega)
  rw [hl] at q
  refine ⟨Bs T word, _, q, ⟨?_, rfl, ?_⟩, rfl, rfl⟩
  · simp [Tgt]
  · exact tracks_word word

/-! ## Main theorems -/

/-- A Turing machine started on `word` halts exactly when its compiled emd program does. -/
theorem halts_iff_init (T : TM.Machine) (word input : List Nat) :
    (∃ fuel s, run (compile T word) fuel (State.init input) = .halt s) ↔
      TM.Halts T ⟨0, 0, TM.wordTape word⟩ := by
  obtain ⟨n, s₀, h₀, hr, _⟩ := prologue_run T word input
  rw [← halts_iff hr]
  constructor
  · intro ⟨fuel, s, hs⟩
    by_cases hf : fuel ≤ n
    · obtain ⟨t, ht⟩ := run_prefix h₀ hf
      rw [hs] at ht
      simp at ht
    · have e : fuel = n + (fuel - n) := by omega
      rw [e, run_add h₀] at hs
      exact ⟨_, _, hs⟩
  · intro ⟨fuel, s, hs⟩
    exact ⟨n + fuel, s, by rw [run_add h₀]; exact hs⟩

/-- The same on the blank tape. -/
theorem halts_iff_blank (T : TM.Machine) (input : List Nat) :
    (∃ fuel s, run (compile T []) fuel (State.init input) = .halt s) ↔
      TM.Halts T ⟨0, 0, fun _ => 0⟩ := by
  have e : TM.wordTape [] = fun _ => 0 := by
    funext h
    simp [TM.wordTape]
  rw [halts_iff_init, e]

/-- The simulation is clean: a compiled machine never faults, whether it halts or not. -/
theorem compiled_never_faults (T : TM.Machine) (word input : List Nat) (fuel : Nat) (f : Fault) :
    run (compile T word) fuel (State.init input) ≠ .fault f := by
  by_cases h : TM.Halts T ⟨0, 0, TM.wordTape word⟩
  · obtain ⟨k, s, hs⟩ := (halts_iff_init T word input).2 h
    exact run_halt_fault_exclusive hs
  · obtain ⟨n, s₀, h₀, hr, _⟩ := prologue_run T word input
    intro hf
    by_cases hle : fuel ≤ n
    · obtain ⟨t, ht⟩ := run_prefix h₀ hle
      rw [hf] at ht
      simp at ht
    · have e : fuel = n + (fuel - n) := by omega
      rw [e, run_add h₀] at hf
      obtain ⟨t, ht⟩ := sim_diverges (fuel - n) hr h
      rw [hf] at ht
      simp at ht

/-- A machine that halts on `word`: emd halts, memory holds the final head and tape, and the
program read no input and wrote no output. -/
theorem final_tape_of_machine_halts (T : TM.Machine) (word input : List Nat) {k : Nat}
    {c' : TM.Config} (h : TM.run T k ⟨0, 0, TM.wordTape word⟩ = some c')
    (hh : TM.step T c' = none) :
    ∃ fuel s, run (compile T word) fuel (State.init input) = .halt s ∧ Tracks s.mem c' ∧
      s.input = input ∧ s.output = [] := by
  obtain ⟨n, s₀, h₀, hr, hi₀, ho₀⟩ := prologue_run T word input
  obtain ⟨f, s, hs, ht, hi, ho⟩ := simulates_halting hr h hh
  exact ⟨n + f, s, by rw [run_add h₀]; exact hs, ht, hi.trans hi₀, ho.trans ho₀⟩

/-- The converse: any emd halt comes from a machine that halted, with that final tape in memory. -/
theorem machine_halts_of_final (T : TM.Machine) (word input : List Nat) {fuel : Nat} {s : State}
    (h : run (compile T word) fuel (State.init input) = .halt s) :
    ∃ k c', TM.run T k ⟨0, 0, TM.wordTape word⟩ = some c' ∧ TM.step T c' = none ∧
      Tracks s.mem c' ∧ s.input = input ∧ s.output = [] := by
  obtain ⟨k, c', hk, hh⟩ := (halts_iff_init T word input).1 ⟨fuel, s, h⟩
  obtain ⟨f, s', hs', ht, hi, ho⟩ := final_tape_of_machine_halts T word input hk hh
  have e := run_halt_unique h hs'
  subst e
  exact ⟨k, c', hk, hh, ht, hi, ho⟩

/-! ## The universal fragment -/

/-- The instructions the compiler emits: 9 kinds, 11 of the 29 opcodes. -/
def inFragment : Instr → Bool
  | .push n => n.val ≤ 2
  | .mul | .add | .sub | .lt | .load | .store | .jz | .halt => true
  | _ => false

theorem frag_pushW (w n : Nat) : (pushW w n).all inFragment = true := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih =>
    have h : n % 2 ≤ 2 := by omega
    simp [pushW, List.all_append, ih, inFragment, h]

theorem frag_addr (w : Nat) : (addrCode w).all inFragment = true := by
  simp [addrCode, headCode, List.all_append, frag_pushW, inFragment]

theorem frag_read (w : Nat) : (readSym w).all inFragment = true := by
  simp [readSym, List.all_append, frag_addr, inFragment]

theorem frag_rule (w : Nat) (r : TM.Rule) (tgt start : Nat) :
    (ruleBlock w r tgt start).all inFragment = true := by
  cases hd : r.move <;>
    simp [ruleBlock, writeCode, moveCode, moveOp, hd, List.all_append, frag_pushW, frag_addr,
      inFragment]

theorem frag_rules (w : Nat) (tgt : Nat → Nat) (K start : Nat) (row : List TM.Rule) :
    (rules w tgt K start row).all inFragment = true := by
  induction K generalizing start row with
  | zero => rfl
  | succ K ih =>
    cases row with
    | nil =>
      simp only [rules, List.all_append, ih, Bool.and_true]
      simp [inFragment]
    | cons r rs => simp only [rules, List.all_append, ih, frag_rule, Bool.and_true]

theorem frag_region (w K : Nat) (tgt : Nat → Nat) (Th E : Nat) (row : List TM.Rule) :
    (region w K tgt Th E row).all inFragment = true := by
  simp [region, dispatch, guard, select, List.all_append, frag_read, frag_pushW, frag_rules,
    inFragment]

theorem frag_layout (w K : Nat) (tgt : Nat → Nat) (Th E : Nat) (T : TM.Machine) :
    (layout w K tgt Th E T).all inFragment = true := by
  induction T generalizing E with
  | nil => rfl
  | cons row rows ih => simp only [layout, List.all_append, ih, frag_region, Bool.and_true]

theorem frag_prologue (w i : Nat) (xs : List Nat) :
    (prologue w i xs).all inFragment = true := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [prologue, List.all_append, ih, frag_pushW, inFragment]

/-- Every instruction of every compiled machine is in the fragment. With `halts_iff_init`, this
makes `push 0..2`, `mul`, `add`, `sub`, `lt`, `load`, `store`, `jz`, `halt` universal. -/
theorem compile_uses (T : TM.Machine) (word : List Nat) :
    ∀ x ∈ compile T word, inFragment x = true := by
  intro x hx
  have h : (compile T word).all inFragment = true := by
    simp [compile, List.all_append, frag_prologue, frag_layout, inFragment]
  exact List.all_eq_true.mp h x hx

end Turing

end Emd

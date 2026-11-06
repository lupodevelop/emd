import Emd

/-! # Source text: line breaks are irrelevant, the limit is exact, the round trip still holds. -/

namespace Emd

theorem linesFit_anti {k n : Nat} {l : List Nat} (h : k ≤ n) (hf : linesFit n l = true) :
    linesFit k l = true := by
  induction l generalizing k n with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = 10
    · simpa [linesFit, hc] using hf
    · simp only [linesFit, hc, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
      exact ⟨by omega, ih (by omega) hf.2⟩

/-- A break only shortens lines, so it can never take a source over the limit. -/
theorem linesFit_insert (pre : List Nat) {post : List Nat} {n : Nat}
    (h : linesFit n (pre ++ post) = true) : linesFit n (pre ++ 10 :: post) = true := by
  induction pre generalizing n with
  | nil =>
    simp only [List.nil_append, linesFit, ↓reduceIte] at h ⊢
    exact linesFit_anti (by omega) h
  | cons c cs ih =>
    by_cases hc : c = 10
    · simp only [List.cons_append, linesFit, hc, ↓reduceIte] at h ⊢
      exact ih h
    · simp only [List.cons_append, linesFit, hc, ↓reduceIte, Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih h.2⟩

theorem toSyms_insert (pre post : List Nat) :
    toSyms (pre ++ 10 :: post) = toSyms (pre ++ post) := by
  induction pre with
  | nil => simp [toSyms]
  | cons c cs ih =>
    by_cases hc : c = 10
    · simp [toSyms, hc, ih]
    · simp [toSyms, hc, ih]

/-- Inserting a line break anywhere, even inside a pair, gives the same program. -/
theorem line_break_irrelevant (pre post : List Nat) (h : linesFit 0 (pre ++ post) = true) :
    decodeSource (pre ++ 10 :: post) = decodeSource (pre ++ post) := by
  unfold decodeSource
  rw [ite_eq_left h, ite_eq_left (linesFit_insert pre h), toSyms_insert]

/-- A valid source stays valid, and the same program, after any inserted break. -/
theorem decodeSource_insert (pre post : List Nat) {P : List Instr}
    (h : decodeSource (pre ++ post) = some P) : decodeSource (pre ++ 10 :: post) = some P := by
  have hf : linesFit 0 (pre ++ post) = true := by
    unfold decodeSource at h
    by_cases hb : linesFit 0 (pre ++ post) = true
    · exact hb
    · simp [hb] at h
  rw [line_break_irrelevant pre post hf, h]

theorem trailing_newline_irrelevant (cps : List Nat) (h : linesFit 0 cps = true) :
    decodeSource (cps ++ [10]) = decodeSource cps := by
  have := line_break_irrelevant cps [] (by simpa using h)
  simpa using this

/-! ## The limit -/

theorem linesFit_short {n : Nat} {l : List Nat} (h : n + l.length ≤ maxLine) :
    linesFit n l = true := by
  induction l generalizing n with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons] at h
    by_cases hc : c = 10
    · simp only [linesFit, hc, ↓reduceIte]
      exact ih (by omega)
    · simp only [linesFit, hc, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, ih (by omega)⟩

theorem linesFit_long {line : List Nat} (post : List Nat) {n : Nat} (hl : ∀ c ∈ line, c ≠ 10)
    (hn : n ≤ maxLine) (hlen : maxLine < n + line.length) :
    linesFit n (line ++ post) = false := by
  induction line generalizing n with
  | nil => simp at hlen; omega
  | cons c cs ih =>
    have hc : c ≠ 10 := hl c (by simp)
    simp only [List.cons_append, linesFit, hc, ↓reduceIte, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    by_cases hm : n < maxLine
    · right
      simp only [List.length_cons] at hlen
      exact ih (fun d hd => hl d (by simp [hd])) (by omega) (by omega)
    · left
      exact hm

theorem linesFit_prefix (pre : List Nat) {x : List Nat} {n : Nat} (hn : n ≤ maxLine)
    (hx : ∀ k, k ≤ maxLine → linesFit k x = false) : linesFit n (pre ++ x) = false := by
  induction pre generalizing n with
  | nil => exact hx n hn
  | cons c cs ih =>
    by_cases hc : c = 10
    · simp only [List.cons_append, linesFit, hc, ↓reduceIte]
      exact ih (by omega)
    · simp only [List.cons_append, linesFit, hc, ↓reduceIte, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      by_cases hm : n < maxLine
      · exact .inr (ih (by omega))
      · exact .inl hm

/-- A stretch of more than 32 code points with no break, anywhere in a source, is rejected. -/
theorem overlong_rejected (pre line post : List Nat) (hl : ∀ c ∈ line, c ≠ 10)
    (hlen : maxLine < line.length) : decodeSource (pre ++ line ++ post) = none := by
  have h : linesFit 0 (pre ++ (line ++ post)) = false :=
    linesFit_prefix pre (by simp [maxLine]) fun k hk => linesFit_long post hl hk (by omega)
  simp [decodeSource, List.append_assoc, h]

/-! ## Other code points -/

theorem toSyms_foreign (pre : List Nat) {c : Nat} (post : List Nat) (hc : c ≠ 10)
    (hf : Sym.ofCodePoint c = none) : toSyms (pre ++ c :: post) = none := by
  induction pre with
  | nil => simp [toSyms, hc, hf]
  | cons d ds ih =>
    by_cases hd : d = 10
    · simp [toSyms, hd, ih]
    · simp [toSyms, hd, ih]

/-- Anything else outside the alphabet is rejected: a line break is only U+000A. -/
theorem foreign_rejected (pre : List Nat) {c : Nat} (post : List Nat) (hc : c ≠ 10)
    (hf : Sym.ofCodePoint c = none) : decodeSource (pre ++ c :: post) = none := by
  simp [decodeSource, toSyms_foreign pre post hc hf]

theorem carriage_return_rejected (pre post : List Nat) : decodeSource (pre ++ 13 :: post) = none :=
  foreign_rejected pre post (by omega) rfl

/-! ## The round trip -/

/-- A source at width 32: a break after every 32 code points, none at the end. -/
def formatAt : Nat → List Sym → List Nat
  | _, [] => []
  | col, s :: ss =>
    if col = maxLine then 10 :: s.codePoint :: formatAt 1 ss
    else s.codePoint :: formatAt (col + 1) ss

def formatSource (P : List Instr) : List Nat := formatAt 0 (encodeProgram P)

theorem codePoint_ne_newline : ∀ s : Sym, s.codePoint ≠ 10 := by decide

theorem linesFit_format {col : Nat} (l : List Sym) (h : col ≤ maxLine) :
    linesFit col (formatAt col l) = true := by
  induction l generalizing col with
  | nil => rfl
  | cons s ss ih =>
    have hm : maxLine = 32 := rfl
    by_cases hc : col = maxLine
    · simp only [formatAt, hc, ↓reduceIte, linesFit, codePoint_ne_newline, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨by omega, ih (by omega)⟩
    · simp only [formatAt, hc, ↓reduceIte, linesFit, codePoint_ne_newline, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨by omega, ih (by omega)⟩

theorem toSyms_format (col : Nat) (l : List Sym) : toSyms (formatAt col l) = some l := by
  induction l generalizing col with
  | nil => rfl
  | cons s ss ih =>
    by_cases hc : col = maxLine
    · simp [formatAt, hc, toSyms, codePoint_ne_newline, ofCodePoint_codePoint, ih]
    · simp [formatAt, hc, toSyms, codePoint_ne_newline, ofCodePoint_codePoint, ih]

/-- Formatting a program at width 32 decodes back to it. -/
theorem decodeSource_format (P : List Instr) : decodeSource (formatSource P) = some P := by
  unfold decodeSource formatSource
  rw [ite_eq_left (linesFit_format _ (by simp [maxLine])), toSyms_format]
  exact decodeProgram_encodeProgram P

theorem toSyms_codePoints (l : List Sym) : toSyms (l.map Sym.codePoint) = some l := by
  induction l with
  | nil => rfl
  | cons s ss ih => simp [toSyms, codePoint_ne_newline, ofCodePoint_codePoint, ih]

/-- The encoding round trip through `decodeSource`, on one line: exact at the limit. -/
theorem decodeSource_one_line (P : List Instr) (h : (encodeProgram P).length ≤ maxLine) :
    decodeSource ((encodeProgram P).map Sym.codePoint) = some P := by
  unfold decodeSource
  rw [ite_eq_left (linesFit_short (by simpa using h)), toSyms_codePoints]
  exact decodeProgram_encodeProgram P

end Emd

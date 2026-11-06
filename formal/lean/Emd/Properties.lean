import Emd

/-! # Properties of the model: unique sources, determinism of whole runs, step invariants. -/

namespace Emd

/-! ## Encoding -/

/-- A program has exactly one source: decoding only succeeds on the program's own encoding. -/
theorem encodeProgram_decodeProgram : ∀ {l : List Sym} {P : List Instr},
    decodeProgram l = some P → encodeProgram P = l
  | [], P, h => by
    simp only [decodeProgram, Option.some.injEq] at h
    subst h
    rfl
  | [_], _, h => by simp [decodeProgram] at h
  | f :: o :: rest, P, h => by
    simp only [decodeProgram, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨i, hi, is, his, rfl⟩ := h
    simp [encodeProgram, encode_decode f o i hi, encodeProgram_decodeProgram his]

def allSyms : List Sym := [0, 1, 2, 3, 4, 5, 6, 7]

def allPairs : List (Sym × Sym) := allSyms.flatMap fun f => allSyms.map fun o => (f, o)

theorem mem_allPairs : ∀ f o : Sym, (f, o) ∈ allPairs := by decide

theorem allPairs_nodup : allPairs.Nodup := by decide

theorem allPairs_length : allPairs.length = 64 := by decide

/-- Of the 64 pairs, exactly 32 decode to an instruction. -/
theorem assigned_count : (allPairs.filter fun p => (decode p).isSome).length = 32 := by decide

theorem codePoint_injective : ∀ a b : Sym, a.codePoint = b.codePoint → a = b := by decide

theorem codePoint_ofCodePoint {n : Nat} {s : Sym} (h : Sym.ofCodePoint n = some s) :
    s.codePoint = n := by
  unfold Sym.ofCodePoint at h
  split at h <;> first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | simp at h

/-! ## Determinism of whole runs -/

/-- Once finished, more fuel changes nothing. -/
theorem run_stable {P : List Instr} {n : Nat} {s : State} {o : Outcome}
    (h : run P n s = o) (ho : ∀ t, o ≠ .next t) (k : Nat) : run P (n + k) s = o := by
  induction n generalizing s with
  | zero =>
    simp only [run] at h
    exact absurd h.symm (ho s)
  | succ n ih =>
    rw [Nat.add_right_comm]
    simp only [run] at h ⊢
    cases hs : step P s with
    | next t =>
      rw [hs] at h
      exact ih h
    | halt t => rw [hs] at h; exact h
    | fault f => rw [hs] at h; exact h

theorem run_halt_mono {P : List Instr} {n m : Nat} {s a : State}
    (h : run P n s = .halt a) (hm : n ≤ m) : run P m s = .halt a := by
  have e : m = n + (m - n) := by omega
  rw [e]
  exact run_stable h (by simp) _

theorem run_fault_mono {P : List Instr} {n m : Nat} {s : State} {f : Fault}
    (h : run P n s = .fault f) (hm : n ≤ m) : run P m s = .fault f := by
  have e : m = n + (m - n) := by omega
  rw [e]
  exact run_stable h (by simp) _

/-- Any fuel that halts reaches the same final state. -/
theorem run_halt_unique {P : List Instr} {n m : Nat} {s a b : State}
    (ha : run P n s = .halt a) (hb : run P m s = .halt b) : a = b := by
  have := run_halt_mono ha (Nat.le_max_left n m)
  rw [run_halt_mono hb (Nat.le_max_right n m)] at this
  exact (Outcome.halt.inj this).symm

/-- Any fuel that faults reaches the same fault. -/
theorem run_fault_unique {P : List Instr} {n m : Nat} {s : State} {f g : Fault}
    (hf : run P n s = .fault f) (hg : run P m s = .fault g) : f = g := by
  have := run_fault_mono hf (Nat.le_max_left n m)
  rw [run_fault_mono hg (Nat.le_max_right n m)] at this
  exact (Outcome.fault.inj this).symm

/-- A program cannot both halt and fault from the same state, at any two fuels. -/
theorem run_halt_fault_exclusive {P : List Instr} {n m : Nat} {s a : State} {f : Fault}
    (ha : run P n s = .halt a) : run P m s ≠ .fault f := by
  intro hf
  have := run_halt_mono ha (Nat.le_max_left n m)
  rw [run_fault_mono hf (Nat.le_max_right n m)] at this
  cases this

/-- What a user sees: the same program and input give the same output and the same stack. -/
theorem run_observable {P : List Instr} {input : List Nat} {n m : Nat} {a b : State}
    (ha : run P n (State.init input) = .halt a) (hb : run P m (State.init input) = .halt b) :
    a.output = b.output ∧ a.stack = b.stack := by
  rw [run_halt_unique ha hb]
  exact ⟨rfl, rfl⟩

/-! ## Invariants of a step -/

/-- The declared change of stack depth of each instruction. -/
def stackEffect : Instr → Int
  | .push _ | .dup | .over | .read => 1
  | .swap | .rot | .load | .not | .halt | .call => 0
  | .drop | .add | .sub | .mul | .div | .mod | .jmp | .ret | .write | .eq | .lt | .gt => -1
  | .store | .jz | .jnz => -2

theorem jumpTo_next {P : List Instr} {s s' : State} {t : Int} (h : jumpTo P s t = .next s') :
    s' = { s with pc := t.toNat } ∧ t.toNat < P.length := by
  unfold jumpTo at h
  split at h
  · rename_i hc
    exact ⟨(Outcome.next.inj h).symm, by omega⟩
  · cases h

/-- All the frame conditions of one executed instruction, proved at once. -/
theorem exec_spec {P : List Instr} {s s' : State} {i : Instr} (h : exec P s i = .next s') :
    s'.pc < P.length ∧
    (s'.stack.length : Int) = s.stack.length + stackEffect i ∧
    (i ≠ .store → s'.mem = s.mem) ∧
    (i = .store → ∃ a v r, s.stack = a :: v :: r ∧ 0 ≤ a ∧
      s'.mem = fun j => if j = a.toNat then v else s.mem j) ∧
    (i ≠ .read → s'.input = s.input) ∧
    (i = .read → s'.input = s.input.tail) ∧
    (i ≠ .write → s'.output = s.output) ∧
    (i = .write → ∃ v, s'.output = s.output ++ [v]) := by
  obtain ⟨pc, st, m, inp, out⟩ := s
  cases i <;> simp only [exec, binary, divLike, advance] at h <;>
    (repeat' split at h) <;>
    first
      | cases h
      | (obtain ⟨rfl, hlt⟩ := jumpTo_next h
         simp_all [stackEffect] <;>
           first
             | omega
             | exact ⟨by omega, _, _, ⟨rfl, rfl⟩, by assumption, rfl⟩)

theorem step_exec {P : List Instr} {s s' : State} (h : step P s = .next s') :
    ∃ i, P[s.pc]? = some i ∧ exec P s i = .next s' := by
  unfold step at h
  cases hp : P[s.pc]? with
  | none => simp [hp] at h
  | some i =>
    rw [hp] at h
    exact ⟨i, rfl, h⟩

/-- A running machine always has its pc inside the program. -/
theorem step_pc_lt {P : List Instr} {s s' : State} (h : step P s = .next s') :
    s'.pc < P.length := by
  obtain ⟨i, _, he⟩ := step_exec h
  exact (exec_spec he).1

/-- Output only grows, and at most by one byte, on `write`. -/
theorem step_output_prefix {P : List Instr} {s s' : State} (h : step P s = .next s') :
    s.output <+: s'.output := by
  obtain ⟨i, _, he⟩ := step_exec h
  obtain ⟨_, _, _, _, _, _, h7, h8⟩ := exec_spec he
  by_cases hi : i = .write
  · obtain ⟨v, hv⟩ := h8 hi
    exact ⟨[v], hv.symm⟩
  · rw [h7 hi]
    exact List.prefix_rfl

/-- Input only shrinks, and at most by one byte, on `read`. -/
theorem step_input_suffix {P : List Instr} {s s' : State} (h : step P s = .next s') :
    s'.input <:+ s.input := by
  obtain ⟨i, _, he⟩ := step_exec h
  obtain ⟨_, _, _, _, h5, h6, _, _⟩ := exec_spec he
  by_cases hi : i = .read
  · rw [h6 hi]
    exact List.tail_suffix _
  · rw [h5 hi]
    exact List.suffix_rfl

/-- Only `store` changes memory. -/
theorem step_mem_frame {P : List Instr} {s s' : State} {i : Instr} (h : step P s = .next s')
    (hi : P[s.pc]? = some i) (hne : i ≠ .store) : s'.mem = s.mem := by
  simp only [step, hi] at h
  exact (exec_spec h).2.2.1 hne

/-- `store` changes memory at its address and nowhere else. -/
theorem step_store_mem {P : List Instr} {s s' : State} (h : step P s = .next s')
    (hi : P[s.pc]? = some .store) :
    ∃ a v r, s.stack = a :: v :: r ∧ 0 ≤ a ∧
      s'.mem = fun j => if j = a.toNat then v else s.mem j := by
  simp only [step, hi] at h
  exact (exec_spec h).2.2.2.1 rfl

/-- The stack depth changes exactly by the instruction's declared effect. -/
theorem stack_effect {P : List Instr} {s s' : State} {i : Instr} (h : step P s = .next s')
    (hi : P[s.pc]? = some i) : (s'.stack.length : Int) = s.stack.length + stackEffect i := by
  simp only [step, hi] at h
  exact (exec_spec h).2.1

/-- A `call` to a `ret`: the return address `call` left brings execution back. -/
theorem call_ret_returns {P : List Instr} {pc t : Nat} {off : Int} {r : List Int} {m : Nat → Int}
    {i o : List Nat} (hc : P[pc]? = some .call) (ht : P[t]? = some .ret)
    (hoff : (pc : Int) + off = t) (hn : pc + 1 < P.length) :
    run P 2 ⟨pc, off :: r, m, i, o⟩ = .next ⟨pc + 1, r, m, i, o⟩ := by
  have hlt : t < P.length := (List.getElem?_eq_some_iff.mp ht).1
  have h1 : (0 : Int) ≤ (pc : Int) + off ∧ (pc : Int) + off < (P.length : Int) := by omega
  have h2 : (0 : Int) ≤ (pc : Int) + 1 ∧ (pc : Int) + 1 < (P.length : Int) := by omega
  have e1 : ((pc : Int) + off).toNat = t := by omega
  have e2 : ((pc : Int) + 1).toNat = pc + 1 := by omega
  simp [run, step, hc, ht, exec, jumpTo, h1, h2, e1, e2]

end Emd

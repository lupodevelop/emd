(* emd simulates Turing machines directly: the same construction and the same statements as
   formal/lean/Emd/Turing.lean, proved again with no classical axiom.

   The tape lives in memory, one cell per position, and the head in cell 0. Position h goes to
   cell h + 2h^2 + 1. Each state has a dispatcher that reads the symbol and jumps to its rule
   with a relative offset computed at run time. The compiler avoids dup and jmp, so a small
   fragment of the instruction set is already universal: see compile_uses. *)

From Stdlib Require Import ZArith List Bool Lia PeanoNat.
From EmdFormal Require Import Emd Props.
Import ListNotations.
Open Scope nat_scope.

Local Notation "a +++ b" := (app a b) (at level 58, left associativity).

(* ---------- Running code in pieces ---------- *)

Lemma run_add : forall P n k s s', run P n s = next s' -> run P (n + k) s = run P k s'.
Proof.
  induction n as [| n IH]; intros k s s' H; cbn [run Nat.add] in *.
  - injection H as <-. reflexivity.
  - destruct (step P s); try discriminate H. exact (IH _ _ _ H).
Qed.

Lemma run_prefix : forall P k n s s', run P k s = next s' -> n <= k -> exists t, run P n s = next t.
Proof.
  induction k as [| k IH]; intros n s s' H Hn.
  - assert (n = 0) by lia. subst n. exists s'. exact H.
  - destruct n as [| n].
    + exists s. reflexivity.
    + cbn [run] in *. destruct (step P s); try discriminate H.
      eapply IH; [exact H | lia].
Qed.

Definition At (P : list instr) (a : nat) (l : list instr) : Prop :=
  exists pre suf, P = pre ++ (l ++ suf) /\ length pre = a.

Lemma At_left : forall P a l1 l2, At P a (l1 ++ l2) -> At P a l1.
Proof.
  intros P a l1 l2 [pre [suf [e hl]]]. exists pre, (l2 ++ suf). split; [| exact hl].
  rewrite e. rewrite <- app_assoc. reflexivity.
Qed.

Lemma At_right : forall P a l1 l2, At P a (l1 ++ l2) -> At P (a + length l1) l2.
Proof.
  intros P a l1 l2 [pre [suf [e hl]]]. exists (pre ++ l1), suf. split.
  - rewrite e, <- !app_assoc. reflexivity.
  - rewrite length_app, hl. reflexivity.
Qed.

Lemma At_head : forall P a x l, At P a (x :: l) -> nth_error P a = Some x.
Proof.
  intros P a x l [pre [suf [e hl]]]. subst.
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma At_comp : forall P l l' a b, At P a l -> At l b l' -> At P (a + b) l'.
Proof.
  intros P l l' a b [pre [suf [e hl]]] [pre' [suf' [e' hl']]].
  exists (pre ++ pre'), (suf' ++ suf). split.
  - rewrite e, e'. rewrite <- !app_assoc. reflexivity.
  - rewrite length_app, hl, hl'. reflexivity.
Qed.

(* Straight-line code: from the start of l it takes exactly length l steps to its end. *)
Definition Seq (l : list instr) (st : list Z) (m : nat -> Z) (st' : list Z) (m' : nat -> Z) : Prop :=
  forall P a i o, At P a l -> a + length l < length P ->
    run P (length l) (mkState a st m i o) = next (mkState (a + length l) st' m' i o).

Lemma Seq_append : forall l1 l2 st st1 st2 m m1 m2,
  Seq l1 st m st1 m1 -> Seq l2 st1 m1 st2 m2 -> Seq (l1 ++ l2) st m st2 m2.
Proof.
  intros l1 l2 st st1 st2 m m1 m2 h1 h2 P a i o hAt hlen.
  rewrite length_app in *.
  pose proof (h1 P a i o (At_left _ _ _ _ hAt) ltac:(lia)) as e1.
  pose proof (h2 P (a + length l1) i o (At_right _ _ _ _ hAt) ltac:(lia)) as e2.
  rewrite (run_add _ _ _ _ _ e1), e2, Nat.add_assoc. reflexivity.
Qed.

Arguments Seq_append {l1 l2 st st1 st2 m m1 m2}.
Local Notation "a >> b" := (Seq_append a b) (at level 58, left associativity).

Lemma advance_ok : forall P a st m i o, a + 1 < length P ->
  advance P (mkState a st m i o) = next (mkState (a + 1) st m i o).
Proof.
  intros P a st m i o h. unfold advance, jump_to. cbn [pc stack mem input output].
  assert (E1 : (0 <=? Z.of_nat a + 1)%Z = true) by (apply Z.leb_le; lia).
  assert (E2 : (Z.of_nat a + 1 <? Z.of_nat (length P))%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2. cbn [andb].
  replace (Z.to_nat (Z.of_nat a + 1)) with (a + 1) by lia. reflexivity.
Qed.

Lemma seq_single : forall x st st' m m',
  (forall P a i o, a + 1 < length P ->
    exec P (mkState a st m i o) x = next (mkState (a + 1) st' m' i o)) ->
  Seq [x] st m st' m'.
Proof.
  intros x st st' m m' H P a i o hAt hlen.
  cbn [length] in *.
  cbn [run]. unfold step. cbn [pc].
  rewrite (At_head _ _ _ _ hAt), (H P a i o hlen). reflexivity.
Qed.

Lemma seq_push : forall s st m, Seq [i_push s] st m (Z.of_nat (sym_index s) :: st) m.
Proof. intros. apply seq_single. intros. exact (advance_ok _ _ _ _ _ _ H). Qed.

Lemma seq_add : forall b a r m, Seq [i_add] (b :: a :: r) m ((a + b)%Z :: r) m.
Proof. intros. apply seq_single. intros. exact (advance_ok _ _ _ _ _ _ H). Qed.

Lemma seq_sub : forall b a r m, Seq [i_sub] (b :: a :: r) m ((a - b)%Z :: r) m.
Proof. intros. apply seq_single. intros. exact (advance_ok _ _ _ _ _ _ H). Qed.

Lemma seq_mul : forall b a r m, Seq [i_mul] (b :: a :: r) m ((a * b)%Z :: r) m.
Proof. intros. apply seq_single. intros. exact (advance_ok _ _ _ _ _ _ H). Qed.

Lemma seq_lt : forall b a r m, Seq [i_lt] (b :: a :: r) m (b2z (a <? b)%Z :: r) m.
Proof. intros. apply seq_single. intros. exact (advance_ok _ _ _ _ _ _ H). Qed.

Lemma seq_load : forall n r m, Seq [i_load] (Z.of_nat n :: r) m (m n :: r) m.
Proof.
  intros n r m. apply seq_single. intros P a i o h.
  assert (E : (Z.of_nat n <? 0)%Z = false) by (apply Z.ltb_ge; lia).
  cbn -[advance Z.ltb Z.to_nat Z.of_nat]. rewrite E, Nat2Z.id.
  exact (advance_ok _ _ _ _ _ _ h).
Qed.

Lemma seq_store : forall n v r m,
  Seq [i_store] (Z.of_nat n :: v :: r) m r (fun k => if Nat.eqb k n then v else m k).
Proof.
  intros n v r m. apply seq_single. intros P a i o h.
  assert (E : (Z.of_nat n <? 0)%Z = false) by (apply Z.ltb_ge; lia).
  cbn -[advance Z.ltb Z.to_nat Z.of_nat Nat.eqb]. rewrite E, Nat2Z.id.
  exact (advance_ok _ _ _ _ _ _ h).
Qed.

Lemma seq_jz_fall : forall off c r m, c <> 0%Z -> Seq [i_jz] (off :: c :: r) m r m.
Proof.
  intros off c r m hc. apply seq_single. intros P a i o h.
  assert (E : (c =? 0)%Z = false) by (apply Z.eqb_neq; exact hc).
  cbn -[advance jump_to Z.eqb]. rewrite E.
  exact (advance_ok _ _ _ _ _ _ h).
Qed.

Lemma step_jz_to : forall P a target off c r m i o,
  nth_error P a = Some i_jz -> target < length P -> c = 0%Z ->
  (Z.of_nat a + off)%Z = Z.of_nat target ->
  step P (mkState a (off :: c :: r) m i o) = next (mkState target r m i o).
Proof.
  intros P a target off c r m i o hx ht hc he. subst c.
  unfold step. cbn [pc]. rewrite hx.
  cbn -[jump_to]. unfold jump_to, with_stack. cbn [pc stack mem input output].
  rewrite he.
  assert (E1 : (0 <=? Z.of_nat target)%Z = true) by (apply Z.leb_le; lia).
  assert (E2 : (Z.of_nat target <? Z.of_nat (length P))%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2. cbn [andb]. rewrite Nat2Z.id. reflexivity.
Qed.

(* ---------- Fixed-width constants ---------- *)

Definition bit (n : nat) : sym := if Nat.eqb (n mod 2) 0 then S0 else S1.

Lemma bit_index : forall n, Z.of_nat (sym_index (bit n)) = Z.of_nat (n mod 2).
Proof.
  intro n. unfold bit. destruct (Nat.eqb_spec (n mod 2) 0) as [E | E].
  - rewrite E. reflexivity.
  - pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as hub.
    assert (n mod 2 = 1) as -> by lia. reflexivity.
Qed.

(* The length is independent of n, which breaks the circularity between offsets and layout. *)
Fixpoint pushW (w n : nat) : list instr :=
  match w with
  | O => [i_push S0]
  | S w' => pushW w' (n / 2) +++ [i_push S2] +++ [i_mul] +++ [i_push (bit n)] +++ [i_add]
  end.

Lemma pushW_length : forall w n, length (pushW w n) = 4 * w + 1.
Proof.
  induction w as [| w IH]; intro n; [reflexivity |].
  cbn [pushW]. rewrite !length_app, IH. cbn [length]. lia.
Qed.

Lemma seq_pushW : forall w n st m, n < 2 ^ w -> Seq (pushW w n) st m (Z.of_nat n :: st) m.
Proof.
  induction w as [| w IH]; intros n st m H.
  - cbn in H. assert (n = 0) by lia. subst n. exact (seq_push S0 st m).
  - cbn [pushW].
    rewrite Nat.pow_succ_r' in H.
    pose proof (Nat.div_mod n 2 ltac:(lia)) as hdm.
    pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as hub.
    assert (Hn : n / 2 < 2 ^ w) by lia.
    pose proof (IH (n / 2) st m Hn >> seq_push S2 _ m >> seq_mul _ _ _ m >>
      seq_push (bit n) _ m >> seq_add _ _ _ m) as q.
    assert (e : (Z.of_nat (n / 2) * Z.of_nat (sym_index S2) + Z.of_nat (sym_index (bit n)))%Z
                = Z.of_nat n).
    { rewrite bit_index. cbn [sym_index]. lia. }
    rewrite e in q. exact q.
Qed.

Lemma two_pow_pos : forall w, 0 < 2 ^ w.
Proof. intro w. apply Nat.neq_0_lt_0. apply Nat.pow_nonzero. lia. Qed.

Lemma lt_two_pow : forall n, n < 2 ^ n.
Proof. intro n. apply Nat.pow_gt_lin_r. lia. Qed.

(* ---------- Turing machines ---------- *)

Inductive dir := dleft | dright.

Definition shift (d : dir) (h : Z) : Z :=
  match d with dleft => (h - 1)%Z | dright => (h + 1)%Z end.

Record rule := mkRule { rwrite : nat; rmove : dir; rnext : nat }.

(* T[q][a] is the rule for state q reading a. A state or symbol outside the table halts. *)
Definition machine := list (list rule).

Record config := mkConfig { cstate : nat; chead : Z; ctape : Z -> nat }.

Definition tm_apply (c : config) (r : rule) : config :=
  mkConfig (rnext r) (shift (rmove r) (chead c))
    (fun h => if Z.eqb h (chead c) then rwrite r else ctape c h).

Definition tm_rule (T : machine) (c : config) : option rule :=
  match nth_error T (cstate c) with
  | Some row => nth_error row (ctape c (chead c))
  | None => None
  end.

Definition tm_step (T : machine) (c : config) : option config :=
  match tm_rule T c with
  | Some r => Some (tm_apply c r)
  | None => None
  end.

Fixpoint tm_run (T : machine) (k : nat) (c : config) : option config :=
  match k with
  | O => Some c
  | S k' =>
    match tm_step T c with
    | Some c' => tm_run T k' c'
    | None => None
    end
  end.

Definition tm_halts (T : machine) (c : config) : Prop :=
  exists k c', tm_run T k c = Some c' /\ tm_step T c' = None.

(* A word on positions 0, 1, ..., blank (0) everywhere else. *)
Definition word_tape (word : list nat) : Z -> nat :=
  fun h => if (0 <=? h)%Z then nth (Z.to_nat h) word 0 else 0.

(* ---------- Tape addresses ---------- *)

Definition cell (h : Z) : nat := Z.to_nat (h + h * h * 2 + 1).

Lemma cell_value_pos : forall h, (1 <= h + h * h * 2 + 1)%Z.
Proof.
  intro h. destruct (Z_le_gt_dec 0 h).
  - nia.
  - nia.
Qed.

Lemma cell_cast : forall h, Z.of_nat (cell h) = (h + h * h * 2 + 1)%Z.
Proof. intro h. pose proof (cell_value_pos h). unfold cell. lia. Qed.

Lemma cell_ne_zero : forall h, cell h <> 0.
Proof. intro h. pose proof (cell_value_pos h). unfold cell. lia. Qed.

Lemma cell_inj : forall a b, cell a = cell b -> a = b.
Proof.
  intros a b h.
  assert (e : Z.of_nat (cell a) = Z.of_nat (cell b)) by (rewrite h; reflexivity).
  rewrite !cell_cast in e.
  assert (hz : ((a - b) * (1 + 2 * (a + b)) = 0)%Z) by lia.
  apply Z.mul_eq_0 in hz. lia.
Qed.

(* ---------- The code ---------- *)

Definition headCode (w : nat) : list instr := pushW w 0 +++ [i_load].

(* Reads the head three times instead of duplicating it, so the fragment needs no dup. *)
Definition addrCode (w : nat) : list instr :=
  headCode w +++ headCode w +++ headCode w +++ [i_mul] +++ [i_push S2] +++ [i_mul] +++ [i_add]
    +++ [i_push S1] +++ [i_add].

Definition bD (w : nat) : nat := 48 * w + 40.
Definition bR (w : nat) : nat := 32 * w + 25.
Definition bS (w K : nat) : nat := bD w + K * bR w.

Definition readSym (w : nat) : list instr := addrCode w +++ [i_load].

(* Leaves Th - Jg, the comparison and the symbol: the jz after it leaves when out of range. *)
Definition guard (w K Th Jg : nat) : list instr :=
  readSym w +++ pushW w K +++ [i_lt] +++ pushW w Th +++ pushW w Jg +++ [i_sub].

(* Rule a starts at Rb + a * bR w; J is the address of the jz that follows. *)
Definition select (w Rb J : nat) : list instr :=
  pushW w (bR w) +++ [i_mul] +++ pushW w Rb +++ [i_add] +++ pushW w J +++ [i_sub].

(* The 0 pushed first stays under everything: the last jz is an unconditional jump. *)
Definition dispatch (w K Th E : nat) : list instr :=
  [i_push S0] +++ readSym w +++ guard w K Th (E + (36 * w + 32)) +++ [i_jz] +++
    select w (E + bD w) (E + (48 * w + 39)) +++ [i_jz].

Definition writeCode (w v : nat) : list instr := pushW w v +++ addrCode w +++ [i_store].

Definition moveOp (d : dir) : instr :=
  match d with dleft => i_sub | dright => i_add end.

Definition moveCode (w : nat) (d : dir) : list instr :=
  pushW w 0 +++ [i_load] +++ [i_push S1] +++ [moveOp d] +++ pushW w 0 +++ [i_store].

Definition ruleBlock (w : nat) (r : rule) (tgt start : nat) : list instr :=
  writeCode w (rwrite r) +++ moveCode w (rmove r) +++ [i_push S0] +++ pushW w tgt +++
    pushW w (start + (32 * w + 24)) +++ [i_sub] +++ [i_jz].

(* A symbol the row does not cover gets a block of halt, so every rule has an address. *)
Fixpoint rules (w : nat) (tgt : nat -> nat) (K start : nat) (row : list rule) : list instr :=
  match K with
  | O => []
  | S K' =>
    match row with
    | [] => repeat i_halt (bR w) ++ rules w tgt K' (start + bR w) []
    | r :: rs => ruleBlock w r (tgt (rnext r)) start ++ rules w tgt K' (start + bR w) rs
    end
  end.

Definition region (w K : nat) (tgt : nat -> nat) (Th E : nat) (row : list rule) : list instr :=
  dispatch w K Th E ++ rules w tgt K (E + bD w) row.

Fixpoint layout (w K : nat) (tgt : nat -> nat) (Th E : nat) (T : machine) : list instr :=
  match T with
  | [] => []
  | row :: rows => region w K tgt Th E row ++ layout w K tgt Th (E + bS w K) rows
  end.

(* Writes the input word onto the tape before the machine starts. *)
Fixpoint prologue (w i : nat) (xs : list nat) : list instr :=
  match xs with
  | [] => []
  | x :: rest =>
    pushW w x +++ pushW w (cell (Z.of_nat i)) +++ [i_store] ++ prologue w (S i) rest
  end.

Fixpoint maxRow (T : machine) : nat :=
  match T with
  | [] => 0
  | row :: rows => Nat.max (length row) (maxRow rows)
  end.

Fixpoint rowSum (row : list rule) : nat :=
  match row with
  | [] => 0
  | r :: rs => rwrite r + rowSum rs
  end.

Fixpoint symBound (T : machine) : nat :=
  match T with
  | [] => 0
  | row :: rows => rowSum row + symBound rows
  end.

Fixpoint wordSum (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: rest => x + wordSum rest
  end.

Definition size (T : machine) (word : list nat) : nat :=
  length T + maxRow T + symBound T + length word + wordSum word.

(* Wide enough for every constant of the program: see fits. *)
Definition W (T : machine) (word : list nat) : nat := 3 * size T word + 12.
Definition Bs (T : machine) (word : list nat) : nat := length word * (8 * W T word + 3).
Definition Ss (T : machine) (word : list nat) : nat := bS (W T word) (maxRow T).
Definition Thh (T : machine) (word : list nat) : nat := Bs T word + length T * Ss T word.

(* Targets past the table clamp to the trailing halt, matching a state outside the table. *)
Definition Tgt (T : machine) (word : list nat) (q : nat) : nat :=
  Bs T word + Nat.min q (length T) * Ss T word.

Definition compile (T : machine) (word : list nat) : list instr :=
  prologue (W T word) 0 word +++
    layout (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word) T +++ [i_halt].

(* ---------- Lengths ---------- *)

Lemma addrCode_length : forall w, length (addrCode w) = 12 * w + 12.
Proof.
  intro w. unfold addrCode, headCode. rewrite !length_app, !pushW_length. cbn [length]. lia.
Qed.

Lemma readSym_length : forall w, length (readSym w) = 12 * w + 13.
Proof. intro w. unfold readSym. rewrite length_app, addrCode_length. cbn [length]. lia. Qed.

Lemma guard_length : forall w K Th Jg, length (guard w K Th Jg) = 24 * w + 18.
Proof.
  intros. unfold guard. rewrite !length_app, readSym_length, !pushW_length. cbn [length]. lia.
Qed.

Lemma select_length : forall w Rb J, length (select w Rb J) = 12 * w + 6.
Proof. intros. unfold select. rewrite !length_app, !pushW_length. cbn [length]. lia. Qed.

Lemma dispatch_length : forall w K Th E, length (dispatch w K Th E) = bD w.
Proof.
  intros. unfold dispatch, bD.
  rewrite !length_app, readSym_length, guard_length, select_length. cbn [length]. lia.
Qed.

Lemma writeCode_length : forall w v, length (writeCode w v) = 16 * w + 14.
Proof.
  intros. unfold writeCode. rewrite !length_app, addrCode_length, pushW_length.
  cbn [length]. lia.
Qed.

Lemma moveCode_length : forall w d, length (moveCode w d) = 8 * w + 6.
Proof. intros. unfold moveCode. rewrite !length_app, !pushW_length. cbn [length]. lia. Qed.

Lemma ruleBlock_length : forall w r tgt start, length (ruleBlock w r tgt start) = bR w.
Proof.
  intros. unfold ruleBlock, bR.
  rewrite !length_app, writeCode_length, moveCode_length, !pushW_length. cbn [length]. lia.
Qed.

Lemma rules_length : forall w tgt K start row, length (rules w tgt K start row) = K * bR w.
Proof.
  intros w tgt. induction K as [| K IH]; intros start row; [reflexivity |].
  destruct row as [| r rs]; cbn [rules].
  - rewrite length_app, repeat_length, IH. lia.
  - rewrite length_app, ruleBlock_length, IH. lia.
Qed.

Lemma region_length : forall w K tgt Th E row, length (region w K tgt Th E row) = bS w K.
Proof.
  intros. unfold region, bS. rewrite length_app, dispatch_length, rules_length. reflexivity.
Qed.

Lemma layout_length : forall w K tgt Th E T, length (layout w K tgt Th E T) = length T * bS w K.
Proof.
  intros w K tgt Th E T. revert E. induction T as [| row rows IH]; intro E; [reflexivity |].
  cbn [layout length]. rewrite length_app, region_length, IH. lia.
Qed.

Lemma prologue_length : forall w xs i, length (prologue w i xs) = length xs * (8 * w + 3).
Proof.
  intros w. induction xs as [| x xs IH]; intro i; [reflexivity |].
  cbn [prologue length]. rewrite !length_app, !pushW_length, IH. cbn [length]. lia.
Qed.

Lemma compile_length : forall T word, length (compile T word) = Thh T word + 1.
Proof.
  intros. unfold compile, Thh, Bs, Ss.
  rewrite !length_app, prologue_length, layout_length. cbn [length]. lia.
Qed.

(* ---------- Positions in the program ---------- *)

Lemma rules_at_some : forall w tgt K start row j r,
  j < K -> nth_error row j = Some r ->
  At (rules w tgt K start row) (j * bR w) (ruleBlock w r (tgt (rnext r)) (start + j * bR w)).
Proof.
  intros w tgt. induction K as [| K IH]; intros start row j r hj h; [lia |].
  destruct row as [| x xs]; [destruct j; discriminate h |].
  destruct j as [| j].
  - cbn in h. injection h as <-.
    exists [], (rules w tgt K (start + bR w) xs). split; [| reflexivity].
    cbn [rules]. replace (start + 0 * bR w) with start by lia. reflexivity.
  - cbn in h. destruct (IH (start + bR w) xs j r ltac:(lia) h) as [pre [suf [e hl]]].
    replace (start + S j * bR w) with (start + bR w + j * bR w) by lia.
    exists (ruleBlock w x (tgt (rnext x)) start ++ pre), suf. split.
    + cbn [rules]. rewrite e. rewrite <- app_assoc. reflexivity.
    + rewrite length_app, ruleBlock_length, hl. lia.
Qed.

Lemma rules_at_none : forall w tgt K start row j,
  j < K -> nth_error row j = None -> At (rules w tgt K start row) (j * bR w) [i_halt].
Proof.
  intros w tgt. induction K as [| K IH]; intros start row j hj h; [lia |].
  destruct j as [| j].
  - destruct row as [| x xs]; [| discriminate h].
    exists [], (repeat i_halt (32 * w + 24) ++ rules w tgt K (start + bR w) []). split; [| reflexivity].
    cbn [rules]. unfold bR at 1.
    replace (32 * w + 25) with (S (32 * w + 24)) by lia. reflexivity.
  - assert (hrec : forall head rs, length head = bR w -> nth_error rs j = None ->
        At (head ++ rules w tgt K (start + bR w) rs) (S j * bR w) [i_halt]).
    { intros head rs hhead hrs.
      destruct (IH (start + bR w) rs j ltac:(lia) hrs) as [pre [suf [e hl]]].
      exists (head ++ pre), suf. split.
      - rewrite e. rewrite <- app_assoc. reflexivity.
      - rewrite length_app, hhead, hl. lia. }
    destruct row as [| x xs].
    + apply hrec; [apply repeat_length | destruct j; reflexivity].
    + apply hrec; [apply ruleBlock_length | exact h].
Qed.

Lemma layout_at : forall w K tgt Th T E q row,
  nth_error T q = Some row ->
  At (layout w K tgt Th E T) (q * bS w K) (region w K tgt Th (E + q * bS w K) row).
Proof.
  intros w K tgt Th. induction T as [| x xs IH]; intros E q row h.
  - destruct q; discriminate h.
  - destruct q as [| q].
    + cbn in h. injection h as <-.
      exists [], (layout w K tgt Th (E + bS w K) xs). split; [| reflexivity].
      cbn [layout]. replace (E + 0 * bS w K) with E by lia. reflexivity.
    + cbn in h. destruct (IH (E + bS w K) q row h) as [pre [suf [e hl]]].
      replace (E + S q * bS w K) with (E + bS w K + q * bS w K) by lia.
      exists (region w K tgt Th E x ++ pre), suf. split.
      * cbn [layout]. rewrite e. rewrite <- app_assoc. reflexivity.
      * rewrite length_app, region_length, hl. lia.
Qed.

Lemma compile_region : forall T word q row,
  nth_error T q = Some row ->
  At (compile T word) (Bs T word + q * Ss T word)
    (region (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word + q * Ss T word) row).
Proof.
  intros T word q row h.
  assert (hl : At (compile T word) (Bs T word)
      (layout (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word) T)).
  { exists (prologue (W T word) 0 word), [i_halt]. split.
    - unfold compile. rewrite <- app_assoc. reflexivity.
    - rewrite prologue_length. reflexivity. }
  exact (At_comp _ _ _ _ _ hl (layout_at _ _ _ _ T _ q row h)).
Qed.

Lemma compile_end : forall T word, nth_error (compile T word) (Thh T word) = Some i_halt.
Proof.
  intros T word. apply (At_head _ _ _ []).
  exists (prologue (W T word) 0 word +++
    layout (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word) T), []. split.
  - reflexivity.
  - rewrite length_app, prologue_length, layout_length. unfold Thh, Bs, Ss. reflexivity.
Qed.

(* ---------- Constants fit the width ---------- *)

Lemma pow_split : forall s, 2 ^ (3 * s + 12) = 2 ^ s * 2 ^ s * 2 ^ s * 4096.
Proof.
  intro s. replace (3 * s + 12) with (s + s + s + 12) by lia.
  rewrite !Nat.pow_add_r. reflexivity.
Qed.

Lemma fits_aux : forall L n K s, L <= s -> n <= s -> K <= s ->
  L * (8 * (3 * s + 12) + 3) + n * bS (3 * s + 12) K < 2 ^ (3 * s + 12).
Proof.
  intros L n K s hL hn hK.
  rewrite pow_split.
  pose proof (lt_two_pow s) as hax.
  generalize dependent (2 ^ s). intros x hax.
  remember (s + 1) as a eqn:hA.
  assert (h1 : L * (8 * (3 * s + 12) + 3) <= a * (770 * a))
    by (apply Nat.mul_le_mono; lia).
  assert (h2 : K * bR (3 * s + 12) <= a * (770 * a))
    by (apply Nat.mul_le_mono; unfold bR; lia).
  assert (h3 : bS (3 * s + 12) K <= 770 * a + a * (770 * a)) by (unfold bS, bD; lia).
  assert (h4 : n * bS (3 * s + 12) K <= a * (770 * a + a * (770 * a)))
    by (apply Nat.mul_le_mono; lia).
  assert (h5 : 0 < a) by lia.
  assert (h6 : a * a <= a * a * a) by nia.
  assert (e1 : a * (770 * a) = 770 * (a * a)) by lia.
  assert (e2 : a * (770 * a + a * (770 * a)) = 770 * (a * a) + 770 * (a * a * a)) by lia.
  assert (h8 : a * a * a <= x * x * x)
    by (apply Nat.mul_le_mono; [apply Nat.mul_le_mono |]; lia).
  rewrite e1 in h1. rewrite e2 in h4.
  assert (hpos : 0 < a * a * a) by nia.
  lia.
Qed.

Lemma fits : forall T word, Thh T word < 2 ^ W T word.
Proof.
  intros T word.
  exact (fits_aux (length word) (length T) (maxRow T) (size T word)
    ltac:(unfold size; lia) ltac:(unfold size; lia) ltac:(unfold size; lia)).
Qed.

Lemma size_lt : forall T word, size T word < 2 ^ W T word.
Proof.
  intros T word. apply (Nat.lt_le_trans _ (2 ^ size T word)); [apply lt_two_pow |].
  apply Nat.pow_le_mono_r; [lia | unfold W; lia].
Qed.

Lemma cell_nat : forall k, cell (Z.of_nat k) = k + k * k * 2 + 1.
Proof. intro k. pose proof (cell_cast (Z.of_nat k)) as h. lia. Qed.

Lemma cell_fits : forall k s, k <= s -> cell (Z.of_nat k) < 2 ^ (3 * s + 12).
Proof.
  intros k s hk. rewrite cell_nat, pow_split.
  pose proof (lt_two_pow s) as ha.
  generalize dependent (2 ^ s). intros x ha.
  assert (h1 : k * k <= x * x) by (apply Nat.mul_le_mono; lia).
  assert (h2 : x * x <= x * x * x) by nia.
  assert (h3 : k <= x * x) by nia.
  assert (h4 : 0 < x * x * x) by nia.
  lia.
Qed.

Lemma row_length_le : forall T q row, nth_error T q = Some row -> length row <= maxRow T.
Proof.
  induction T as [| x xs IH]; intros q row h; [destruct q; discriminate h |].
  destruct q as [| q]; cbn in h |- *.
  - injection h as <-. lia.
  - pose proof (IH q row h). lia.
Qed.

Lemma write_le_row : forall row j r, nth_error row j = Some r -> rwrite r <= rowSum row.
Proof.
  induction row as [| x xs IH]; intros j r h; [destruct j; discriminate h |].
  destruct j as [| j]; cbn in h |- *.
  - injection h as <-. lia.
  - pose proof (IH j r h). lia.
Qed.

Lemma write_le : forall T q j row r,
  nth_error T q = Some row -> nth_error row j = Some r -> rwrite r <= symBound T.
Proof.
  induction T as [| x xs IH]; intros q j row r h hr; [destruct q; discriminate h |].
  destruct q as [| q]; cbn in h |- *.
  - injection h as <-. pose proof (write_le_row _ _ _ hr). lia.
  - pose proof (IH q j row r h hr). lia.
Qed.

Lemma mem_le_wordSum : forall x xs, In x xs -> x <= wordSum xs.
Proof.
  intros x. induction xs as [| y ys IH]; intro h; [destruct h |].
  destruct h as [<- | h]; cbn [wordSum]; [lia |]. pose proof (IH h). lia.
Qed.

(* ---------- Straight-line pieces ---------- *)

Lemma seq_head : forall w r m, Seq (headCode w) r m (m 0 :: r) m.
Proof.
  intros w r m. exact (seq_pushW w 0 r m (two_pow_pos w) >> seq_load 0 r m).
Qed.

Lemma seq_addr : forall w h r m, m 0 = h -> Seq (addrCode w) r m (Z.of_nat (cell h) :: r) m.
Proof.
  intros w h r m hh. subst h.
  pose proof (seq_head w r m >> seq_head w _ m >> seq_head w _ m >> seq_mul _ _ _ m >>
    seq_push S2 _ m >> seq_mul _ _ _ m >> seq_add _ _ _ m >> seq_push S1 _ m >> seq_add _ _ _ m) as q.
  assert (e : (m O + m O * m O * Z.of_nat (sym_index S2) + Z.of_nat (sym_index S1))%Z
              = Z.of_nat (cell (m O))).
  { rewrite cell_cast. reflexivity. }
  rewrite e in q. exact q.
Qed.

Lemma seq_readSym : forall w r m h, m 0 = h -> Seq (readSym w) r m (m (cell h) :: r) m.
Proof.
  intros w r m h hh. exact (seq_addr w h r m hh >> seq_load (cell h) r m).
Qed.

Lemma seq_guard : forall w K Th Jg h a r m, m 0 = h -> m (cell h) = a ->
  K < 2 ^ w -> Th < 2 ^ w -> Jg < 2 ^ w ->
  Seq (guard w K Th Jg) (a :: r) m
    ((Z.of_nat Th - Z.of_nat Jg)%Z :: b2z (a <? Z.of_nat K)%Z :: a :: r) m.
Proof.
  intros w K Th Jg h a r m hh hv hK hTh hJg.
  pose proof (seq_readSym w (a :: r) m h hh) as qR. rewrite hv in qR.
  exact (qR >> seq_pushW w K _ m hK >> seq_lt _ _ _ m >> seq_pushW w Th _ m hTh >>
    seq_pushW w Jg _ m hJg >> seq_sub _ _ _ m).
Qed.

Lemma seq_select : forall w Rb J a r m, bR w < 2 ^ w -> Rb < 2 ^ w -> J < 2 ^ w ->
  Seq (select w Rb J) (a :: r) m
    ((a * Z.of_nat (bR w) + Z.of_nat Rb - Z.of_nat J)%Z :: r) m.
Proof.
  intros w Rb J a r m hR hRb hJ.
  exact (seq_pushW w (bR w) _ m hR >> seq_mul _ _ _ m >> seq_pushW w Rb _ m hRb >>
    seq_add _ _ _ m >> seq_pushW w J _ m hJ >> seq_sub _ _ _ m).
Qed.

Lemma seq_write : forall w v h m, m 0 = h -> v < 2 ^ w ->
  Seq (writeCode w v) [] m [] (fun j => if Nat.eqb j (cell h) then Z.of_nat v else m j).
Proof.
  intros w v h m hh hv.
  exact (seq_pushW w v [] m hv >> seq_addr w h _ m hh >> seq_store (cell h) _ [] m).
Qed.

Lemma seq_moveOp : forall d h r m,
  Seq [moveOp d] (Z.of_nat (sym_index S1) :: h :: r) m (shift d h :: r) m.
Proof.
  intros [|] h r m.
  - exact (seq_sub _ _ _ m).
  - exact (seq_add _ _ _ m).
Qed.

Lemma seq_move : forall w d h m, m 0 = h ->
  Seq (moveCode w d) [] m [] (fun j => if Nat.eqb j 0 then shift d h else m j).
Proof.
  intros w d h m hh. subst h.
  exact (seq_pushW w 0 [] m (two_pow_pos w) >> seq_load 0 [] m >> seq_push S1 _ m >>
    seq_moveOp d (m 0) [] m >> seq_pushW w 0 _ m (two_pow_pos w) >> seq_store 0 _ [] m).
Qed.

(* ---------- Dispatch and rules ---------- *)

(* A symbol below K: the dispatcher reaches its rule with an empty stack. *)
Lemma dispatch_fall : forall P w K Th E a h m i o,
  At P E (dispatch w K Th E) -> m 0 = h -> m (cell h) = Z.of_nat a -> a < K ->
  K < 2 ^ w -> Th < 2 ^ w -> E + bD w < 2 ^ w -> bR w < 2 ^ w ->
  E + bD w + a * bR w < length P ->
  exists L, 0 < L /\ run P L (mkState E [] m i o) = next (mkState (E + bD w + a * bR w) [] m i o).
Proof.
  intros P w K Th E a h m i o hAt hm hv ha hK hTh hE hR hT.
  assert (hbD : bD w = 48 * w + 40) by reflexivity.
  assert (hc : b2z (Z.of_nat a <? Z.of_nat K)%Z <> 0%Z).
  { assert (Ec : (Z.of_nat a <? Z.of_nat K)%Z = true) by (apply Z.ltb_lt; lia).
    rewrite Ec. discriminate. }
  pose proof (seq_readSym w [Z.of_nat (sym_index S0)] m h hm) as qR. rewrite hv in qR.
  pose proof (seq_push S0 [] m >> qR >>
    seq_guard w K Th (E + (36 * w + 32)) h _ _ m hm hv hK hTh ltac:(lia) >>
    seq_jz_fall _ _ _ m hc >>
    seq_select w (E + bD w) (E + (48 * w + 39)) _ _ m hR hE ltac:(lia)) as qS.
  unfold dispatch in hAt.
  assert (hlA : length ([i_push S0] +++ readSym w +++ guard w K Th (E + (36 * w + 32)) +++ [i_jz] +++
      select w (E + bD w) (E + (48 * w + 39))) = 48 * w + 39).
  { rewrite !length_app, readSym_length, guard_length, select_length. cbn [length]. lia. }
  pose proof (qS P E i o (At_left _ _ _ _ hAt) ltac:(rewrite hlA; lia)) as e.
  rewrite hlA in e.
  assert (hx : nth_error P (E + (48 * w + 39)) = Some i_jz).
  { pose proof (At_right _ _ _ _ hAt) as hr. rewrite hlA in hr. exact (At_head _ _ _ _ hr). }
  assert (hstep := step_jz_to P _ (E + bD w + a * bR w)
    (Z.of_nat a * Z.of_nat (bR w) + Z.of_nat (E + bD w) - Z.of_nat (E + (48 * w + 39)))%Z
    (Z.of_nat (sym_index S0)) [] m i o hx hT eq_refl ltac:(lia)).
  exists (48 * w + 39 + 1). split; [lia |].
  rewrite (run_add _ _ _ _ _ e). cbn [run]. rewrite hstep. reflexivity.
Qed.

(* A symbol out of range: the dispatcher leaves for the trailing halt. *)
Lemma dispatch_out : forall P w K Th E a h m i o,
  At P E (dispatch w K Th E) -> m 0 = h -> m (cell h) = Z.of_nat a -> K <= a ->
  K < 2 ^ w -> Th < 2 ^ w -> E + (36 * w + 32) < 2 ^ w -> Th < length P ->
  E + (36 * w + 32) < length P ->
  exists L, run P L (mkState E [] m i o)
    = next (mkState Th [Z.of_nat a; Z.of_nat (sym_index S0)] m i o).
Proof.
  intros P w K Th E a h m i o hAt hm hv ha hK hTh hJ hT hE.
  assert (hc : b2z (Z.of_nat a <? Z.of_nat K)%Z = 0%Z).
  { assert (Ec : (Z.of_nat a <? Z.of_nat K)%Z = false) by (apply Z.ltb_ge; lia).
    rewrite Ec. reflexivity. }
  pose proof (seq_readSym w [Z.of_nat (sym_index S0)] m h hm) as qR. rewrite hv in qR.
  pose proof (seq_push S0 [] m >> qR >>
    seq_guard w K Th (E + (36 * w + 32)) h _ _ m hm hv hK hTh hJ) as qS.
  unfold dispatch in hAt.
  pose proof (At_left _ _ _ _ (At_left _ _ _ _ hAt)) as hA.
  assert (hlA : length ([i_push S0] +++ readSym w +++ guard w K Th (E + (36 * w + 32)))
      = 36 * w + 32).
  { rewrite !length_app, readSym_length, guard_length. cbn [length]. lia. }
  pose proof (qS P E i o (At_left _ _ _ _ hA) ltac:(rewrite hlA; lia)) as e.
  rewrite hlA in e.
  assert (hx : nth_error P (E + (36 * w + 32)) = Some i_jz).
  { pose proof (At_right _ _ _ _ hA) as hr. rewrite hlA in hr. exact (At_head _ _ _ _ hr). }
  assert (hstep := step_jz_to P _ Th (Z.of_nat Th - Z.of_nat (E + (36 * w + 32)))%Z _
    [Z.of_nat a; Z.of_nat (sym_index S0)] m i o hx hT hc ltac:(lia)).
  exists (36 * w + 32 + 1).
  rewrite (run_add _ _ _ _ _ e). cbn [run]. rewrite hstep. reflexivity.
Qed.

(* m holds configuration c: the head in cell 0, the tape at cell. *)
Definition Tracks (m : nat -> Z) (c : config) : Prop :=
  m 0 = chead c /\ forall h, m (cell h) = Z.of_nat (ctape c h).

(* A rule block writes, moves and jumps to the next state. *)
Lemma rule_step : forall P w tgt start r m i o c,
  At P start (ruleBlock w r tgt start) -> Tracks m c -> rwrite r < 2 ^ w -> tgt < 2 ^ w ->
  start + (32 * w + 24) < 2 ^ w -> tgt < length P -> start + (32 * w + 24) < length P ->
  exists L m', 0 < L /\ run P L (mkState start [] m i o) = next (mkState tgt [] m' i o) /\
    Tracks m' (tm_apply c r).
Proof.
  intros P w tgt start r m i o c hAt ht hv hT hJ hLen hb.
  destruct ht as [ht0 httape].
  set (m1 := fun j => if Nat.eqb j (cell (chead c)) then Z.of_nat (rwrite r) else m j).
  assert (h1 : m1 0 = chead c).
  { unfold m1. destruct (Nat.eqb_spec 0 (cell (chead c))) as [E | E].
    - exfalso. exact (cell_ne_zero _ (eq_sym E)).
    - exact ht0. }
  set (m2 := fun j => if Nat.eqb j 0 then shift (rmove r) (chead c) else m1 j).
  pose proof (seq_write w (rwrite r) (chead c) m ht0 hv >>
    seq_move w (rmove r) (chead c) m1 h1 >> seq_push S0 [] _ >>
    seq_pushW w tgt _ _ hT >> seq_pushW w (start + (32 * w + 24)) _ _ hJ >> seq_sub _ _ _ _) as qS.
  unfold ruleBlock in hAt.
  assert (hlA : length (writeCode w (rwrite r) +++ moveCode w (rmove r) +++ [i_push S0] +++
      pushW w tgt +++ pushW w (start + (32 * w + 24)) +++ [i_sub]) = 32 * w + 24).
  { rewrite !length_app, writeCode_length, moveCode_length, !pushW_length. cbn [length]. lia. }
  pose proof (qS P start i o (At_left _ _ _ _ hAt) ltac:(rewrite hlA; lia)) as e.
  rewrite hlA in e.
  assert (hx : nth_error P (start + (32 * w + 24)) = Some i_jz).
  { pose proof (At_right _ _ _ _ hAt) as hr. rewrite hlA in hr. exact (At_head _ _ _ _ hr). }
  assert (hstep := step_jz_to P _ tgt (Z.of_nat tgt - Z.of_nat (start + (32 * w + 24)))%Z
    (Z.of_nat (sym_index S0)) [] m2 i o hx hLen eq_refl ltac:(lia)).
  unfold m2 in hstep.
  exists (32 * w + 24 + 1), m2. split; [lia |]. split.
  - rewrite (run_add _ _ _ _ _ e). cbn [run]. rewrite hstep. reflexivity.
  - split.
    + reflexivity.
    + intro x. unfold m2, m1, tm_apply. cbn [ctape].
      destruct (Nat.eqb_spec (cell x) 0) as [E0 | E0]; [exfalso; exact (cell_ne_zero x E0) |].
      destruct (Z.eqb_spec x (chead c)) as [Ex | Ex].
      * subst x. rewrite Nat.eqb_refl. reflexivity.
      * destruct (Nat.eqb_spec (cell x) (cell (chead c))) as [Ec | Ec].
        -- exfalso. exact (Ex (cell_inj _ _ Ec)).
        -- apply httape.
Qed.

(* ---------- Simulation ---------- *)

(* The simulation relation: pc at the state's dispatcher, empty stack, the tape in memory. *)
Definition Rel (T : machine) (word : list nat) (c : config) (s : state) : Prop :=
  pc s = Tgt T word (cstate c) /\ stack s = [] /\ Tracks (mem s) c.

Lemma state_bounds : forall T word q, q < length T ->
  Bs T word + q * Ss T word + Ss T word <= Thh T word.
Proof.
  intros T word q hq.
  assert (S q * Ss T word <= length T * Ss T word) by (apply Nat.mul_le_mono_r; lia).
  unfold Thh. lia.
Qed.

Lemma tgt_le : forall T word q, Tgt T word q <= Thh T word.
Proof.
  intros T word q.
  assert (Nat.min q (length T) * Ss T word <= length T * Ss T word)
    by (apply Nat.mul_le_mono_r; lia).
  unfold Tgt, Thh. lia.
Qed.

(* One machine step is matched by at least one emd step, which gives divergence. *)
Lemma sim_step : forall T word c c' s, Rel T word c s -> tm_step T c = Some c' ->
  exists k s', 0 < k /\ run (compile T word) k s = next s' /\ Rel T word c' s' /\
    input s' = input s /\ output s' = output s.
Proof.
  intros T word c c' [pc0 st m i o] [hpc [hst ht]] hs.
  cbn [pc stack mem input output] in hpc, hst, ht. subst st.
  unfold tm_step, tm_rule in hs.
  destruct (nth_error T (cstate c)) as [row |] eqn:hrow; [| discriminate hs].
  destruct (nth_error row (ctape c (chead c))) as [r |] eqn:hrule; [| discriminate hs].
  injection hs as <-.
  assert (hq : cstate c < length T) by (apply nth_error_Some; congruence).
  assert (ha : ctape c (chead c) < length row) by (apply nth_error_Some; congruence).
  pose proof (row_length_le _ _ _ hrow) as hrl.
  assert (haK : ctape c (chead c) < maxRow T) by lia.
  assert (hpc' : pc0 = Bs T word + cstate c * Ss T word).
  { rewrite hpc. unfold Tgt. rewrite Nat.min_l by lia. reflexivity. }
  clear hpc. subst pc0.
  pose proof (compile_region T word _ _ hrow) as hReg.
  pose proof (state_bounds T word _ hq) as hEnd.
  pose proof (fits T word) as hFit.
  pose proof (size_lt T word) as hSize.
  pose proof (compile_length T word) as hLen.
  assert (hS : Ss T word = bD (W T word) + maxRow T * bR (W T word)) by reflexivity.
  assert (hbD : bD (W T word) = 48 * W T word + 40) by reflexivity.
  assert (hbR : bR (W T word) = 32 * W T word + 25) by reflexivity.
  assert (hKs : maxRow T <= size T word) by (unfold size; lia).
  assert (hWs : symBound T <= size T word) by (unfold size; lia).
  assert (hStep : S (ctape c (chead c)) * bR (W T word) <= maxRow T * bR (W T word))
    by (apply Nat.mul_le_mono_r; lia).
  remember (Bs T word + cstate c * Ss T word) as E eqn:hE.
  unfold region in hReg.
  pose proof (At_left _ _ _ _ hReg) as hDisp.
  destruct (dispatch_fall _ _ _ _ _ (ctape c (chead c)) _ _ i o hDisp (proj1 ht) (proj2 ht _) haK
    ltac:(lia) hFit ltac:(lia) ltac:(lia) ltac:(lia)) as [L1 [hL1 h1]].
  pose proof (At_comp _ _ _ _ _ (At_right _ _ _ _ hReg)
    (rules_at_some (W T word) (Tgt T word) (maxRow T) (E + bD (W T word)) row _ r haK hrule))
    as hAtRule.
  rewrite dispatch_length in hAtRule.
  pose proof (tgt_le T word (rnext r)) as hTgt.
  pose proof (write_le _ _ _ _ _ hrow hrule) as hw.
  destruct (rule_step _ _ _ _ _ _ i o c hAtRule ht ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia)) as [L2 [m' [hL2 [h2 ht']]]].
  exists (L1 + L2), (mkState (Tgt T word (rnext r)) [] m' i o).
  split; [lia |]. split.
  - rewrite (run_add _ _ _ _ _ h1). exact h2.
  - split; [split; [reflexivity | split; [reflexivity | exact ht']] | split; reflexivity].
Qed.

(* A machine that stops is matched by a halt, memory unchanged. *)
Lemma sim_halt : forall T word c s, Rel T word c s -> tm_step T c = None ->
  exists fuel s', run (compile T word) fuel s = halted s' /\ mem s' = mem s /\
    input s' = input s /\ output s' = output s.
Proof.
  intros T word c [pc0 st m i o] [hpc [hst ht]] hs.
  cbn [pc stack mem input output] in hpc, hst, ht. subst st.
  pose proof (fits T word) as hFit.
  pose proof (size_lt T word) as hSize.
  pose proof (compile_length T word) as hLen.
  pose proof (compile_end T word) as hEndHalt.
  assert (hKs : maxRow T <= size T word) by (unfold size; lia).
  assert (stopAt : forall a st, nth_error (compile T word) a = Some i_halt ->
      run (compile T word) 1 (mkState a st m i o) = halted (mkState a st m i o)).
  { intros a st hx. cbn [run]. unfold step. cbn [pc]. rewrite hx. reflexivity. }
  unfold tm_step, tm_rule in hs.
  destruct (nth_error T (cstate c)) as [row |] eqn:hrow.
  - assert (hq : cstate c < length T) by (apply nth_error_Some; congruence).
    destruct (nth_error row (ctape c (chead c))) as [r |] eqn:hnone; [discriminate hs |].
    assert (hpc' : pc0 = Bs T word + cstate c * Ss T word).
    { rewrite hpc. unfold Tgt. rewrite Nat.min_l by lia. reflexivity. }
    clear hpc. subst pc0.
    pose proof (compile_region T word _ _ hrow) as hReg.
    pose proof (state_bounds T word _ hq) as hEnd.
    assert (hS : Ss T word = bD (W T word) + maxRow T * bR (W T word)) by reflexivity.
    assert (hbD : bD (W T word) = 48 * W T word + 40) by reflexivity.
    assert (hbR : bR (W T word) = 32 * W T word + 25) by reflexivity.
    remember (Bs T word + cstate c * Ss T word) as E eqn:hE.
    unfold region in hReg.
    pose proof (At_left _ _ _ _ hReg) as hDisp.
    destruct (Nat.lt_ge_cases (ctape c (chead c)) (maxRow T)) as [haK | haK].
    + assert (hStep : S (ctape c (chead c)) * bR (W T word) <= maxRow T * bR (W T word))
        by (apply Nat.mul_le_mono_r; lia).
      destruct (dispatch_fall _ _ _ _ _ (ctape c (chead c)) _ _ i o hDisp (proj1 ht) (proj2 ht _)
        haK ltac:(lia) hFit ltac:(lia) ltac:(lia) ltac:(lia)) as [L1 [_ h1]].
      pose proof (At_comp _ _ _ _ _ (At_right _ _ _ _ hReg)
        (rules_at_none (W T word) (Tgt T word) (maxRow T) (E + bD (W T word)) row _ haK hnone))
        as hAtHalt.
      rewrite dispatch_length in hAtHalt.
      exists (L1 + 1), (mkState (E + bD (W T word) + ctape c (chead c) * bR (W T word)) [] m i o).
      split; [| repeat split].
      rewrite (run_add _ _ _ _ _ h1). exact (stopAt _ _ (At_head _ _ _ _ hAtHalt)).
    + destruct (dispatch_out _ _ _ _ _ (ctape c (chead c)) _ _ i o hDisp (proj1 ht) (proj2 ht _)
        haK ltac:(lia) hFit ltac:(lia) ltac:(lia) ltac:(lia)) as [L1 h1].
      exists (L1 + 1), (mkState (Thh T word)
        [Z.of_nat (ctape c (chead c)); Z.of_nat (sym_index S0)] m i o).
      split; [| repeat split].
      rewrite (run_add _ _ _ _ _ h1). exact (stopAt _ _ hEndHalt).
  - assert (hge : length T <= cstate c) by (apply nth_error_None; exact hrow).
    assert (hpc' : pc0 = Thh T word).
    { rewrite hpc. unfold Tgt, Thh. rewrite Nat.min_r by exact hge. reflexivity. }
    clear hpc. subst pc0.
    exists 1, (mkState (Thh T word) [] m i o).
    split; [exact (stopAt _ _ hEndHalt) | repeat split].
Qed.

Lemma sim_run : forall T word k c c' s, Rel T word c s -> tm_run T k c = Some c' ->
  exists fuel s', run (compile T word) fuel s = next s' /\ Rel T word c' s' /\
    input s' = input s /\ output s' = output s.
Proof.
  intros T word. induction k as [| k IH]; intros c c' s hr h.
  - cbn [tm_run] in h. injection h as <-. exists 0, s. repeat split; try reflexivity; apply hr.
  - cbn [tm_run] in h. destruct (tm_step T c) as [c1 |] eqn:hs; [| discriminate h].
    destruct (sim_step _ _ _ _ _ hr hs) as [n [s1 [_ [h1 [hr1 [hi1 ho1]]]]]].
    destruct (IH _ _ _ hr1 h) as [fuel [s' [h2 [hr' [hi' ho']]]]].
    exists (n + fuel), s'. split; [| split; [exact hr' | split; congruence]].
    rewrite (run_add _ _ _ _ _ h1). exact h2.
Qed.

(* A machine that halts is matched by a halting emd run whose memory holds the final tape. *)
Theorem simulates_halting : forall T word c c' s k, Rel T word c s ->
  tm_run T k c = Some c' -> tm_step T c' = None ->
  exists fuel s', run (compile T word) fuel s = halted s' /\ Tracks (mem s') c' /\
    input s' = input s /\ output s' = output s.
Proof.
  intros T word c c' s k hr h hh.
  destruct (sim_run _ _ _ _ _ _ hr h) as [n [s1 [h1 [hr1 [hi1 ho1]]]]].
  destruct (sim_halt _ _ _ _ hr1 hh) as [f [s' [h2 [hm [hi2 ho2]]]]].
  exists (n + f), s'. split; [rewrite (run_add _ _ _ _ _ h1); exact h2 |].
  split; [rewrite hm; apply hr1 | split; congruence].
Qed.

(* Any emd halt comes from a machine that halts, with no classical reasoning. *)
Lemma machine_halts_of_run : forall T word fuel c s s', Rel T word c s ->
  run (compile T word) fuel s = halted s' -> tm_halts T c.
Proof.
  intros T word fuel. induction fuel as [fuel IH] using lt_wf_ind. intros c s s' hr h.
  destruct (tm_step T c) as [c1 |] eqn:hs.
  - destruct (sim_step _ _ _ _ _ hr hs) as [k [s1 [hk [hrun [hr1 _]]]]].
    destruct (Nat.le_gt_cases fuel k) as [hle | hgt].
    + destruct (run_prefix _ _ _ _ _ hrun hle) as [t ht]. rewrite h in ht. discriminate ht.
    + replace fuel with (k + (fuel - k)) in h by lia. rewrite (run_add _ _ _ _ _ hrun) in h.
      destruct (IH (fuel - k) ltac:(lia) c1 s1 s' hr1 h) as [k1 [c2 [h1 h2]]].
      exists (S k1), c2. split; [cbn [tm_run]; rewrite hs; exact h1 | exact h2].
  - exists 0, c. split; [reflexivity | exact hs].
Qed.

(* From any state related to c, the compiled program halts exactly when the machine does. *)
Theorem halts_iff : forall T word c s, Rel T word c s ->
  (exists fuel s', run (compile T word) fuel s = halted s') <-> tm_halts T c.
Proof.
  intros T word c s hr. split.
  - intros [fuel [s' h]]. exact (machine_halts_of_run _ _ _ _ _ _ hr h).
  - intros [k [c' [h hh]]].
    destruct (simulates_halting _ _ _ _ _ _ hr h hh) as [fuel [s' [hs _]]].
    exists fuel, s'. exact hs.
Qed.

(* A state related to a configuration never faults, whether the machine halts or not. *)
Lemma never_faults_rel : forall T word fuel c s f, Rel T word c s ->
  run (compile T word) fuel s <> faulted f.
Proof.
  intros T word fuel. induction fuel as [fuel IH] using lt_wf_ind. intros c s f hr hf.
  destruct (tm_step T c) as [c1 |] eqn:hs.
  - destruct (sim_step _ _ _ _ _ hr hs) as [k [s1 [hk [hrun [hr1 _]]]]].
    destruct (Nat.le_gt_cases fuel k) as [hle | hgt].
    + destruct (run_prefix _ _ _ _ _ hrun hle) as [t ht]. rewrite hf in ht. discriminate ht.
    + replace fuel with (k + (fuel - k)) in hf by lia. rewrite (run_add _ _ _ _ _ hrun) in hf.
      exact (IH (fuel - k) ltac:(lia) c1 s1 f hr1 hf).
  - destruct (sim_halt _ _ _ _ hr hs) as [n [s' [h _]]].
    exact (run_halt_fault_exclusive _ _ _ _ _ _ h hf).
Qed.

(* ---------- The input word ---------- *)

Fixpoint writeWord (m : nat -> Z) (i : nat) (xs : list nat) : nat -> Z :=
  match xs with
  | [] => m
  | x :: rest =>
    writeWord (fun j => if Nat.eqb j (cell (Z.of_nat i)) then Z.of_nat x else m j) (S i) rest
  end.

Lemma seq_prologue : forall w xs i m, (forall x, In x xs -> x < 2 ^ w) ->
  (forall k, i <= k -> k < i + length xs -> cell (Z.of_nat k) < 2 ^ w) ->
  Seq (prologue w i xs) [] m [] (writeWord m i xs).
Proof.
  intros w. induction xs as [| x xs IH]; intros i m hx hc.
  - intros P a i' o _ _. cbn [prologue length run]. rewrite Nat.add_0_r. reflexivity.
  - cbn [prologue writeWord].
    refine (seq_pushW w x [] m (hx x (or_introl eq_refl)) >>
      seq_pushW w (cell (Z.of_nat i)) _ m (hc i ltac:(lia) ltac:(cbn [length]; lia)) >>
      seq_store (cell (Z.of_nat i)) _ [] m >> IH (S i) _ _ _).
    + intros y hy. exact (hx y (or_intror hy)).
    + intros k h1 h2. apply hc; cbn [length]; lia.
Qed.

Lemma writeWord_zero : forall xs m i, writeWord m i xs 0 = m 0.
Proof.
  induction xs as [| x xs IH]; intros m i; [reflexivity |].
  cbn [writeWord]. rewrite IH.
  destruct (Nat.eqb_spec 0 (cell (Z.of_nat i))) as [E | E].
  - exfalso. exact (cell_ne_zero _ (eq_sym E)).
  - reflexivity.
Qed.

Lemma writeWord_out : forall xs m i h,
  ~ (Z.of_nat i <= h < Z.of_nat i + Z.of_nat (length xs))%Z ->
  writeWord m i xs (cell h) = m (cell h).
Proof.
  induction xs as [| x xs IH]; intros m i h hout; [reflexivity |].
  cbn [length] in hout. cbn [writeWord]. rewrite IH by lia.
  destruct (Nat.eqb_spec (cell h) (cell (Z.of_nat i))) as [E | E]; [| reflexivity].
  pose proof (cell_inj _ _ E). lia.
Qed.

Lemma writeWord_in : forall xs m i h,
  (Z.of_nat i <= h < Z.of_nat i + Z.of_nat (length xs))%Z ->
  writeWord m i xs (cell h) = Z.of_nat (nth (Z.to_nat (h - Z.of_nat i)) xs 0).
Proof.
  induction xs as [| x xs IH]; intros m i h hin.
  - cbn [length] in hin. lia.
  - cbn [length] in hin. cbn [writeWord].
    destruct (Z.eq_dec h (Z.of_nat i)) as [E | E].
    + subst h. rewrite writeWord_out by lia. rewrite Nat.eqb_refl.
      replace (Z.to_nat (Z.of_nat i - Z.of_nat i)) with 0 by lia. reflexivity.
    + rewrite IH by lia.
      replace (Z.to_nat (h - Z.of_nat i)) with (S (Z.to_nat (h - Z.of_nat (S i)))) by lia.
      reflexivity.
Qed.

Lemma tracks_word : forall word,
  Tracks (writeWord (fun _ => 0%Z) 0 word) (mkConfig 0 0%Z (word_tape word)).
Proof.
  intro word. split.
  - rewrite writeWord_zero. reflexivity.
  - intro h. cbn [ctape]. unfold word_tape.
    destruct (Z.leb_spec0 0 h) as [h0 | h0].
    + destruct (Z_lt_le_dec h (Z.of_nat (length word))) as [h1 | h1].
      * rewrite writeWord_in by (cbn [Z.of_nat]; lia).
        cbn [Z.of_nat]. rewrite Z.sub_0_r. reflexivity.
      * rewrite writeWord_out by (cbn [Z.of_nat]; lia).
        rewrite nth_overflow by lia. reflexivity.
    + rewrite writeWord_out by (cbn [Z.of_nat]; lia). reflexivity.
Qed.

(* The prologue leaves the machine at state 0, head 0, with the word on the tape. *)
Lemma prologue_run : forall T word inp,
  exists n s, run (compile T word) n (init inp) = next s /\
    Rel T word (mkConfig 0 0%Z (word_tape word)) s /\ input s = inp /\ output s = [].
Proof.
  intros T word inp.
  pose proof (fits T word) as hFit.
  pose proof (compile_length T word) as hLen.
  assert (hBs : Bs T word <= Thh T word) by (unfold Thh; lia).
  assert (hAt : At (compile T word) 0 (prologue (W T word) 0 word)).
  { exists [], (layout (W T word) (maxRow T) (Tgt T word) (Thh T word) (Bs T word) T ++ [i_halt]).
    split; [| reflexivity].
    unfold compile. rewrite <- app_assoc. reflexivity. }
  assert (hl : length (prologue (W T word) 0 word) = Bs T word)
    by (rewrite prologue_length; reflexivity).
  assert (hx : forall x, In x word -> x < 2 ^ W T word).
  { intros x hx.
    pose proof (mem_le_wordSum _ _ hx) as h1.
    pose proof (size_lt T word) as h2.
    assert (wordSum word <= size T word) by (unfold size; lia).
    lia. }
  assert (hc : forall k, 0 <= k -> k < 0 + length word -> cell (Z.of_nat k) < 2 ^ W T word).
  { intros k _ hk. apply cell_fits. unfold size. lia. }
  pose proof (seq_prologue (W T word) word 0 (fun _ => 0%Z) hx hc
    (compile T word) 0 inp [] hAt ltac:(rewrite hl; lia)) as q.
  rewrite hl in q.
  exists (Bs T word), (mkState (0 + Bs T word) [] (writeWord (fun _ => 0%Z) 0 word) inp []).
  split; [exact q |]. split; [| split; reflexivity].
  split; [| split; [reflexivity | exact (tracks_word word)]].
  cbn [pc cstate]. unfold Tgt. replace (Nat.min 0 (length T)) with 0 by lia. lia.
Qed.

(* ---------- Main theorems ---------- *)

(* A Turing machine started on word halts exactly when its compiled emd program does. *)
Theorem halts_iff_init : forall T word inp,
  (exists fuel s, run (compile T word) fuel (init inp) = halted s) <->
  tm_halts T (mkConfig 0 0%Z (word_tape word)).
Proof.
  intros T word inp.
  destruct (prologue_run T word inp) as [n [s0 [h0 [hr _]]]].
  rewrite <- (halts_iff _ _ _ _ hr). split.
  - intros [fuel [s hs]].
    destruct (Nat.le_gt_cases fuel n) as [hf | hf].
    + destruct (run_prefix _ _ _ _ _ h0 hf) as [t ht]. rewrite hs in ht. discriminate ht.
    + replace fuel with (n + (fuel - n)) in hs by lia. rewrite (run_add _ _ _ _ _ h0) in hs.
      exists (fuel - n), s. exact hs.
  - intros [fuel [s hs]]. exists (n + fuel), s. rewrite (run_add _ _ _ _ _ h0). exact hs.
Qed.

(* The same on the blank tape. *)
Theorem halts_iff_blank : forall T inp,
  (exists fuel s, run (compile T []) fuel (init inp) = halted s) <->
  tm_halts T (mkConfig 0 0%Z (fun _ => 0)).
Proof.
  intros T inp.
  assert (hr : Rel T [] (mkConfig 0 0%Z (fun _ => 0)) (init inp)).
  { split; [| split; [reflexivity | split; [reflexivity | intro; reflexivity]]].
    unfold Tgt, Bs. cbn [pc init cstate length].
    replace (Nat.min 0 (length T)) with 0 by lia. reflexivity. }
  exact (halts_iff _ _ _ _ hr).
Qed.

(* The simulation is clean: a compiled machine never faults, whether it halts or not. *)
Theorem compiled_never_faults : forall T word inp fuel f,
  run (compile T word) fuel (init inp) <> faulted f.
Proof.
  intros T word inp fuel f hf.
  destruct (prologue_run T word inp) as [n [s0 [h0 [hr _]]]].
  destruct (Nat.le_gt_cases fuel n) as [hle | hgt].
  - destruct (run_prefix _ _ _ _ _ h0 hle) as [t ht]. rewrite hf in ht. discriminate ht.
  - replace fuel with (n + (fuel - n)) in hf by lia. rewrite (run_add _ _ _ _ _ h0) in hf.
    exact (never_faults_rel _ _ _ _ _ _ hr hf).
Qed.

(* A machine that halts on word: emd halts, memory holds the final head and tape, and the program
   read no input and wrote no output. *)
Theorem final_tape_of_machine_halts : forall T word inp k c',
  tm_run T k (mkConfig 0 0%Z (word_tape word)) = Some c' -> tm_step T c' = None ->
  exists fuel s, run (compile T word) fuel (init inp) = halted s /\ Tracks (mem s) c' /\
    input s = inp /\ output s = [].
Proof.
  intros T word inp k c' h hh.
  destruct (prologue_run T word inp) as [n [s0 [h0 [hr [hi0 ho0]]]]].
  destruct (simulates_halting _ _ _ _ _ _ hr h hh) as [f [s [hs [ht [hi ho]]]]].
  exists (n + f), s. split; [rewrite (run_add _ _ _ _ _ h0); exact hs |].
  split; [exact ht | split; congruence].
Qed.

(* The converse: any emd halt comes from a machine that halted, with that final tape in memory. *)
Theorem machine_halts_of_final : forall T word inp fuel s,
  run (compile T word) fuel (init inp) = halted s ->
  exists k c', tm_run T k (mkConfig 0 0%Z (word_tape word)) = Some c' /\ tm_step T c' = None /\
    Tracks (mem s) c' /\ input s = inp /\ output s = [].
Proof.
  intros T word inp fuel s h.
  destruct (proj1 (halts_iff_init T word inp) (ex_intro _ fuel (ex_intro _ s h)))
    as [k [c' [hk hh]]].
  destruct (final_tape_of_machine_halts _ _ inp _ _ hk hh) as [f [s' [hs' [ht [hi ho]]]]].
  pose proof (run_halt_unique _ _ _ _ _ _ h hs') as e. subst s'.
  exists k, c'. auto.
Qed.

(* ---------- The universal fragment ---------- *)

(* The instructions the compiler emits: 9 kinds, 11 of the 29 opcodes. *)
Definition inFragment (x : instr) : bool :=
  match x with
  | i_push S0 | i_push S1 | i_push S2 => true
  | i_mul | i_add | i_sub | i_lt | i_load | i_store | i_jz | i_halt => true
  | _ => false
  end.

Lemma frag_pushW : forall w n, forallb inFragment (pushW w n) = true.
Proof.
  induction w as [| w IH]; intro n; [reflexivity |].
  cbn [pushW]. rewrite !forallb_app, IH. unfold bit.
  destruct (Nat.eqb (n mod 2) 0); reflexivity.
Qed.

Lemma frag_addr : forall w, forallb inFragment (addrCode w) = true.
Proof.
  intro w. unfold addrCode, headCode. rewrite !forallb_app, frag_pushW. reflexivity.
Qed.

Lemma frag_read : forall w, forallb inFragment (readSym w) = true.
Proof. intro w. unfold readSym. rewrite forallb_app, frag_addr. reflexivity. Qed.

Lemma frag_rule : forall w r tgt start, forallb inFragment (ruleBlock w r tgt start) = true.
Proof.
  intros w r tgt start. unfold ruleBlock, writeCode, moveCode.
  rewrite !forallb_app, !frag_pushW, !frag_addr.
  destruct (rmove r); reflexivity.
Qed.

Lemma frag_repeat : forall n, forallb inFragment (repeat i_halt n) = true.
Proof. induction n as [| n IH]; [reflexivity | exact IH]. Qed.

Lemma frag_rules : forall w tgt K start row, forallb inFragment (rules w tgt K start row) = true.
Proof.
  intros w tgt. induction K as [| K IH]; intros start row; [reflexivity |].
  destruct row as [| r rs]; cbn [rules]; rewrite forallb_app, IH.
  - rewrite frag_repeat. reflexivity.
  - rewrite frag_rule. reflexivity.
Qed.

Lemma frag_region : forall w K tgt Th E row, forallb inFragment (region w K tgt Th E row) = true.
Proof.
  intros. unfold region, dispatch, guard, select.
  rewrite !forallb_app, frag_read, !frag_pushW, frag_rules. reflexivity.
Qed.

Lemma frag_layout : forall w K tgt Th T E, forallb inFragment (layout w K tgt Th E T) = true.
Proof.
  intros w K tgt Th. induction T as [| row rows IH]; intro E; [reflexivity |].
  cbn [layout]. rewrite forallb_app, frag_region, IH. reflexivity.
Qed.

Lemma frag_prologue : forall w xs i, forallb inFragment (prologue w i xs) = true.
Proof.
  intro w. induction xs as [| x xs IH]; intro i; [reflexivity |].
  cbn [prologue]. rewrite !forallb_app, !frag_pushW, IH. reflexivity.
Qed.

(* Every instruction of every compiled machine is in the fragment. With halts_iff_init, this makes
   push 0..2, mul, add, sub, lt, load, store, jz, halt universal. *)
Theorem compile_uses : forall T word x, In x (compile T word) -> inFragment x = true.
Proof.
  intros T word x hx.
  assert (h : forallb inFragment (compile T word) = true).
  { unfold compile. rewrite !forallb_app, frag_prologue, frag_layout. reflexivity. }
  exact (proj1 (forallb_forall _ _) h x hx).
Qed.

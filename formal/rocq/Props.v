(* Properties of the model, the same statements as formal/lean/Emd/Properties.lean:
   unique sources, determinism of whole runs, step invariants. *)

From Stdlib Require Import ZArith List Bool Lia.
From EmdFormal Require Import Emd.
Import ListNotations.
Open Scope Z_scope.

(* ---------- Encoding ---------- *)

(* A program has exactly one source: decoding only succeeds on the program's own encoding. *)
Theorem encode_program_decode_program :
  forall l P, decode_program l = Some P -> encode_program P = l.
Proof.
  fix IH 1. intros l P H.
  destruct l as [| f [| o rest]].
  - simpl in H. injection H as <-. reflexivity.
  - simpl in H. discriminate H.
  - cbn [decode_program] in H.
    destruct (decode (f, o)) as [i |] eqn:Hd;
      destruct (decode_program rest) as [tl |] eqn:Hr; try discriminate H.
    injection H as <-. simpl.
    rewrite (encode_decode f o i Hd). simpl.
    rewrite (IH rest tl Hr). reflexivity.
Qed.

Definition all_syms : list sym := [S0; S1; S2; S3; S4; S5; S6; S7].

Definition all_pairs : list (sym * sym) :=
  flat_map (fun f => map (fun o => (f, o)) all_syms) all_syms.

Theorem mem_all_pairs : forall p, In p all_pairs.
Proof.
  intros [f o]. apply in_flat_map. exists f. split.
  - destruct f; simpl; tauto.
  - apply in_map. destruct o; simpl; tauto.
Qed.

Theorem all_pairs_length : length all_pairs = 64%nat.
Proof. reflexivity. Qed.

Theorem all_pairs_nodup : NoDup all_pairs.
Proof.
  unfold all_pairs, all_syms; simpl.
  repeat (constructor; [simpl; intuition discriminate |]).
  constructor.
Qed.

(* Of the 64 pairs, exactly 32 decode to an instruction. *)
Theorem assigned_count :
  length (filter (fun p => match decode p with Some _ => true | None => false end) all_pairs)
    = 32%nat.
Proof. reflexivity. Qed.

Theorem code_point_injective : forall a b, code_point a = code_point b -> a = b.
Proof. destruct a, b; simpl; intro H; try reflexivity; discriminate H. Qed.

Theorem code_point_of_code_point :
  forall n s, sym_of_code_point n = Some s -> code_point s = n.
Proof.
  intros n s H. unfold sym_of_code_point in H.
  repeat match type of H with
  | context [Nat.eqb n ?k] =>
    let E := fresh "E" in
    destruct (Nat.eqb n k) eqn:E;
    [apply PeanoNat.Nat.eqb_eq in E; subst n; injection H as <-; reflexivity |]
  end.
  discriminate H.
Qed.

(* ---------- Determinism of whole runs ---------- *)

(* Once finished, more fuel changes nothing. *)
Theorem run_stable : forall P n s o k,
  run P n s = o -> (forall t, o <> next t) -> run P (n + k) s = o.
Proof.
  induction n as [| n IH]; intros s o k H Ho.
  - simpl in H. subst o. exfalso. exact (Ho s eq_refl).
  - simpl in H |- *. destruct (step P s) as [t | t | f]; auto.
Qed.

Theorem run_halt_mono : forall P n m s a,
  run P n s = halted a -> (n <= m)%nat -> run P m s = halted a.
Proof.
  intros P n m s a H Hm.
  replace m with (n + (m - n))%nat by lia.
  apply run_stable; [exact H | discriminate].
Qed.

Theorem run_fault_mono : forall P n m s f,
  run P n s = faulted f -> (n <= m)%nat -> run P m s = faulted f.
Proof.
  intros P n m s f H Hm.
  replace m with (n + (m - n))%nat by lia.
  apply run_stable; [exact H | discriminate].
Qed.

(* Any fuel that halts reaches the same final state. *)
Theorem run_halt_unique : forall P n m s a b,
  run P n s = halted a -> run P m s = halted b -> a = b.
Proof.
  intros P n m s a b Ha Hb.
  pose proof (run_halt_mono P n (max n m) s a Ha (PeanoNat.Nat.le_max_l n m)) as A.
  pose proof (run_halt_mono P m (max n m) s b Hb (PeanoNat.Nat.le_max_r n m)) as B.
  rewrite A in B. injection B. auto.
Qed.

(* Any fuel that faults reaches the same fault. *)
Theorem run_fault_unique : forall P n m s f g,
  run P n s = faulted f -> run P m s = faulted g -> f = g.
Proof.
  intros P n m s f g Hf Hg.
  pose proof (run_fault_mono P n (max n m) s f Hf (PeanoNat.Nat.le_max_l n m)) as A.
  pose proof (run_fault_mono P m (max n m) s g Hg (PeanoNat.Nat.le_max_r n m)) as B.
  rewrite A in B. injection B. auto.
Qed.

(* A program cannot both halt and fault from the same state, at any two fuels. *)
Theorem run_halt_fault_exclusive : forall P n m s a f,
  run P n s = halted a -> run P m s <> faulted f.
Proof.
  intros P n m s a f Ha Hf.
  pose proof (run_halt_mono P n (max n m) s a Ha (PeanoNat.Nat.le_max_l n m)) as A.
  pose proof (run_fault_mono P m (max n m) s f Hf (PeanoNat.Nat.le_max_r n m)) as B.
  rewrite A in B. discriminate B.
Qed.

(* What a user sees: the same program and input give the same output and the same stack. *)
Theorem run_observable : forall P inp n m a b,
  run P n (init inp) = halted a -> run P m (init inp) = halted b ->
  output a = output b /\ stack a = stack b.
Proof.
  intros P inp n m a b Ha Hb.
  rewrite (run_halt_unique P n m (init inp) a b Ha Hb). auto.
Qed.

(* ---------- Invariants of a step ---------- *)

(* The declared change of stack depth of each instruction. *)
Definition stack_effect_of (i : instr) : Z :=
  match i with
  | i_push _ | i_dup | i_over | i_read => 1
  | i_swap | i_rot | i_load | i_not | i_halt | i_call => 0
  | i_drop | i_add | i_sub | i_mul | i_div | i_mod | i_jmp | i_ret | i_write | i_eq | i_lt | i_gt => -1
  | i_store | i_jz | i_jnz => -2
  end.

Lemma jump_to_next : forall P s s' t,
  jump_to P s t = next s' ->
  s' = mkState (Z.to_nat t) (stack s) (mem s) (input s) (output s) /\
  (Z.to_nat t < length P)%nat.
Proof.
  unfold jump_to. intros P s s' t H.
  destruct ((0 <=? t) && (t <? Z.of_nat (length P))) eqn:E; [| discriminate H].
  apply andb_true_iff in E. destruct E as [E1 E2].
  apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  injection H as <-. split; [reflexivity | lia].
Qed.

(* All the frame conditions of one executed instruction, proved at once. *)
Theorem exec_spec : forall P s s' i,
  exec P s i = next s' ->
  (pc s' < length P)%nat /\
  Z.of_nat (length (stack s')) = Z.of_nat (length (stack s)) + stack_effect_of i /\
  (i <> i_store -> mem s' = mem s) /\
  (i = i_store -> exists a v r, stack s = a :: v :: r /\ 0 <= a /\
    mem s' = fun k => if Nat.eqb k (Z.to_nat a) then v else mem s k) /\
  (i <> i_read -> input s' = input s) /\
  (i = i_read -> input s' = tl (input s)) /\
  (i <> i_write -> output s' = output s) /\
  (i = i_write -> exists v, output s' = output s ++ [v]).
Proof.
  intros P [pc0 st m inp out] s' i H.
  destruct i;
    unfold exec, binary, div_like, advance, with_stack in H; simpl in H;
    repeat match type of H with
    | context [match ?x with _ => _ end] => destruct x eqn:?
    end;
    try discriminate H;
    apply jump_to_next in H; destruct H as [-> Hlt]; cbn [pc stack mem input output tl];
    repeat split; try exact Hlt;
    try (intros; congruence);
    try (cbn [length stack_effect_of]; lia);
    try (intros _; reflexivity);
    try (intros _; eexists; reflexivity);
    intros _; do 3 eexists; split; [reflexivity | split; [apply Z.ltb_ge; assumption | reflexivity]].
Qed.

Lemma step_exec : forall P s s',
  step P s = next s' -> exists i, nth_error P (pc s) = Some i /\ exec P s i = next s'.
Proof.
  unfold step. intros P s s' H.
  destruct (nth_error P (pc s)) as [i |]; [| discriminate H].
  exists i. auto.
Qed.

(* A running machine always has its pc inside the program. *)
Theorem step_pc_lt : forall P s s', step P s = next s' -> (pc s' < length P)%nat.
Proof.
  intros P s s' H. destruct (step_exec P s s' H) as [i [_ E]].
  apply (exec_spec P s s' i E).
Qed.

(* Output only grows, and at most by one byte, on write. *)
Theorem step_output_prefix : forall P s s',
  step P s = next s' -> exists l, output s' = output s ++ l.
Proof.
  intros P s s' H. destruct (step_exec P s s' H) as [i [_ E]].
  destruct (exec_spec P s s' i E) as [_ [_ [_ [_ [_ [_ [H7 H8]]]]]]].
  destruct (i) eqn:Ei; try (exists []; rewrite app_nil_r; apply H7; discriminate).
  destruct (H8 eq_refl) as [v Hv]. exists [v]. exact Hv.
Qed.

(* Input only shrinks, and at most by one byte, on read. *)
Theorem step_input_suffix : forall P s s',
  step P s = next s' -> exists l, input s = l ++ input s'.
Proof.
  intros P s s' H. destruct (step_exec P s s' H) as [i [_ E]].
  destruct (exec_spec P s s' i E) as [_ [_ [_ [_ [H5 [H6 _]]]]]].
  destruct (i) eqn:Ei; try (exists []; simpl; symmetry; apply H5; discriminate).
  rewrite (H6 eq_refl). destruct (input s) as [| b rest].
  - exists []. reflexivity.
  - exists [b]. reflexivity.
Qed.

(* Only store changes memory. *)
Theorem step_mem_frame : forall P s s' i,
  step P s = next s' -> nth_error P (pc s) = Some i -> i <> i_store -> mem s' = mem s.
Proof.
  unfold step. intros P s s' i H Hi Hne. rewrite Hi in H.
  apply (exec_spec P s s' i H). exact Hne.
Qed.

(* store changes memory at its address and nowhere else. *)
Theorem step_store_mem : forall P s s',
  step P s = next s' -> nth_error P (pc s) = Some i_store ->
  exists a v r, stack s = a :: v :: r /\ 0 <= a /\
    mem s' = fun k => if Nat.eqb k (Z.to_nat a) then v else mem s k.
Proof.
  unfold step. intros P s s' H Hi. rewrite Hi in H.
  apply (exec_spec P s s' i_store H). reflexivity.
Qed.

(* The stack depth changes exactly by the instruction's declared effect. *)
Theorem stack_effect : forall P s s' i,
  step P s = next s' -> nth_error P (pc s) = Some i ->
  Z.of_nat (length (stack s')) = Z.of_nat (length (stack s)) + stack_effect_of i.
Proof.
  unfold step. intros P s s' i H Hi. rewrite Hi in H.
  apply (exec_spec P s s' i H).
Qed.

(* A call to a ret: the return address call left brings execution back. *)
Theorem call_ret_returns : forall P k t off r m i o,
  nth_error P k = Some i_call ->
  nth_error P t = Some i_ret ->
  Z.of_nat k + off = Z.of_nat t ->
  (k + 1 < length P)%nat ->
  run P 2 (mkState k (off :: r) m i o) = next (mkState (k + 1) r m i o).
Proof.
  intros P k t off r m i o Hc Ht Hoff Hn.
  assert (Hlt : (t < length P)%nat) by (apply nth_error_Some; rewrite Ht; discriminate).
  assert (S1 : step P (mkState k (off :: r) m i o)
               = next (mkState t ((Z.of_nat k + 1) :: r) m i o)).
  { unfold step. simpl pc. rewrite Hc. simpl exec. unfold jump_to, with_stack. simpl.
    rewrite Hoff.
    replace ((0 <=? Z.of_nat t) && (Z.of_nat t <? Z.of_nat (length P))) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Nat2Z.id. reflexivity. }
  assert (S2 : step P (mkState t ((Z.of_nat k + 1) :: r) m i o) = next (mkState (k + 1) r m i o)).
  { unfold step. simpl pc. rewrite Ht. simpl exec. unfold jump_to, with_stack. simpl.
    replace ((0 <=? Z.of_nat k + 1) && (Z.of_nat k + 1 <? Z.of_nat (length P))) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    replace (Z.to_nat (Z.of_nat k + 1)) with (k + 1)%nat by lia.
    reflexivity. }
  unfold run. rewrite S1, S2. reflexivity.
Qed.

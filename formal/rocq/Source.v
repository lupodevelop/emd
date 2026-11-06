(* Source text, the same statements as formal/lean/Emd/Source.lean: line breaks are irrelevant,
   the limit is exact, the round trip still holds. *)

From Stdlib Require Import List Bool Lia PeanoNat.
From EmdFormal Require Import Emd.
Import ListNotations.
Open Scope nat_scope.

Lemma lines_fit_anti : forall l k n, k <= n -> lines_fit n l = true -> lines_fit k l = true.
Proof.
  induction l as [| c cs IH]; intros k n h hf; [reflexivity |].
  cbn [lines_fit] in *. destruct (Nat.eqb c 10); [exact hf |].
  apply andb_true_iff in hf. destruct hf as [h1 h2]. apply Nat.ltb_lt in h1.
  apply andb_true_iff. split.
  - apply Nat.ltb_lt. lia.
  - exact (IH (S k) (S n) ltac:(lia) h2).
Qed.

(* A break only shortens lines, so it can never take a source over the limit. *)
Lemma lines_fit_insert : forall pre post n,
  lines_fit n (pre ++ post) = true -> lines_fit n (pre ++ 10 :: post) = true.
Proof.
  induction pre as [| c cs IH]; intros post n h.
  - cbn [app lines_fit] in *. exact (lines_fit_anti _ 0 n ltac:(lia) h).
  - cbn [app lines_fit] in *. destruct (Nat.eqb c 10).
    + exact (IH _ _ h).
    + apply andb_true_iff in h. destruct h as [h1 h2].
      apply andb_true_iff. split; [exact h1 | exact (IH _ _ h2)].
Qed.

Lemma to_syms_insert : forall pre post, to_syms (pre ++ 10 :: post) = to_syms (pre ++ post).
Proof.
  induction pre as [| c cs IH]; intro post; [reflexivity |].
  cbn [app to_syms]. rewrite IH. reflexivity.
Qed.

(* Inserting a line break anywhere, even inside a pair, gives the same program. *)
Theorem line_break_irrelevant : forall pre post, lines_fit 0 (pre ++ post) = true ->
  decode_source (pre ++ 10 :: post) = decode_source (pre ++ post).
Proof.
  intros pre post h. unfold decode_source.
  rewrite h, (lines_fit_insert _ _ _ h), to_syms_insert. reflexivity.
Qed.

(* A valid source stays valid, and the same program, after any inserted break. *)
Theorem decode_source_insert : forall pre post P,
  decode_source (pre ++ post) = Some P -> decode_source (pre ++ 10 :: post) = Some P.
Proof.
  intros pre post P h.
  assert (hf : lines_fit 0 (pre ++ post) = true).
  { unfold decode_source in h. destruct (lines_fit 0 (pre ++ post)); [reflexivity | discriminate h]. }
  rewrite (line_break_irrelevant _ _ hf). exact h.
Qed.

Theorem trailing_newline_irrelevant : forall cps, lines_fit 0 cps = true ->
  decode_source (cps ++ [10]) = decode_source cps.
Proof.
  intros cps h.
  pose proof (line_break_irrelevant cps []) as e. rewrite app_nil_r in e. exact (e h).
Qed.

(* ---------- The limit ---------- *)

Lemma lines_fit_short : forall l n, n + length l <= 32 -> lines_fit n l = true.
Proof.
  induction l as [| c cs IH]; intros n h; [reflexivity |].
  cbn [length] in h. cbn [lines_fit]. destruct (Nat.eqb c 10).
  - apply IH. lia.
  - apply andb_true_iff. split; [apply Nat.ltb_lt; lia | apply IH; lia].
Qed.

Lemma lines_fit_long : forall line post n, (forall c, In c line -> c <> 10) -> n <= 32 ->
  32 < n + length line -> lines_fit n (line ++ post) = false.
Proof.
  induction line as [| c cs IH]; intros post n hl hn hlen.
  - cbn [length] in hlen. lia.
  - cbn [length] in hlen. cbn [app lines_fit].
    assert (hc : Nat.eqb c 10 = false)
      by (apply Nat.eqb_neq; apply hl; left; reflexivity).
    rewrite hc. destruct (Nat.ltb_spec n 32) as [hm | hm].
    + rewrite (IH post (S n)); [reflexivity | | lia | lia].
      intros d hd. apply hl. right. exact hd.
    + reflexivity.
Qed.

Lemma lines_fit_prefix : forall pre x n, n <= 32 ->
  (forall k, k <= 32 -> lines_fit k x = false) -> lines_fit n (pre ++ x) = false.
Proof.
  induction pre as [| c cs IH]; intros x n hn hx; [exact (hx n hn) |].
  cbn [app lines_fit]. destruct (Nat.eqb c 10).
  - apply IH; [lia | exact hx].
  - destruct (Nat.ltb_spec n 32) as [hm | hm].
    + rewrite (IH x (S n) ltac:(lia) hx). reflexivity.
    + reflexivity.
Qed.

(* A stretch of more than 32 code points with no break, anywhere in a source, is rejected. *)
Theorem overlong_rejected : forall pre line post, (forall c, In c line -> c <> 10) ->
  32 < length line -> decode_source (pre ++ line ++ post) = None.
Proof.
  intros pre line post hl hlen. unfold decode_source.
  rewrite (lines_fit_prefix pre (line ++ post) 0 ltac:(lia)
    (fun k hk => lines_fit_long line post k hl hk ltac:(lia))).
  reflexivity.
Qed.

(* ---------- Other code points ---------- *)

Lemma to_syms_foreign : forall pre c post, c <> 10 -> sym_of_code_point c = None ->
  to_syms (pre ++ c :: post) = None.
Proof.
  induction pre as [| d ds IH]; intros c post hc hf.
  - cbn [app to_syms].
    apply Nat.eqb_neq in hc. rewrite hc, hf. reflexivity.
  - cbn [app to_syms]. rewrite (IH c post hc hf).
    destruct (Nat.eqb d 10); [reflexivity |].
    destruct (sym_of_code_point d); reflexivity.
Qed.

(* Anything else outside the alphabet is rejected: a line break is only U+000A. *)
Theorem foreign_rejected : forall pre c post, c <> 10 -> sym_of_code_point c = None ->
  decode_source (pre ++ c :: post) = None.
Proof.
  intros pre c post hc hf. unfold decode_source.
  rewrite (to_syms_foreign pre c post hc hf).
  destruct (lines_fit 0 (pre ++ c :: post)); reflexivity.
Qed.

Theorem carriage_return_rejected : forall pre post, decode_source (pre ++ 13 :: post) = None.
Proof. intros. apply foreign_rejected; [lia | reflexivity]. Qed.

(* ---------- The round trip ---------- *)

(* A source at width 32: a break after every 32 code points, none at the end. *)
Fixpoint format_at (col : nat) (l : list sym) : list nat :=
  match l with
  | [] => []
  | s :: ss =>
    if Nat.eqb col 32 then 10 :: code_point s :: format_at 1 ss
    else code_point s :: format_at (S col) ss
  end.

Definition format_source (P : list instr) : list nat := format_at 0 (encode_program P).

Lemma code_point_ne_newline : forall s, Nat.eqb (code_point s) 10 = false.
Proof. destruct s; reflexivity. Qed.

Lemma lines_fit_format : forall l col, col <= 32 -> lines_fit col (format_at col l) = true.
Proof.
  induction l as [| s ss IH]; intros col h; [reflexivity |].
  cbn [format_at]. destruct (Nat.eqb_spec col 32) as [hc | hc].
  - cbn [lines_fit]. rewrite code_point_ne_newline. cbn [Nat.eqb lines_fit]. apply IH. lia.
  - cbn [lines_fit]. rewrite code_point_ne_newline.
    apply andb_true_iff. split; [apply Nat.ltb_lt; lia | apply IH; lia].
Qed.

Lemma to_syms_format : forall l col, to_syms (format_at col l) = Some l.
Proof.
  induction l as [| s ss IH]; intro col; [reflexivity |].
  cbn [format_at]. destruct (Nat.eqb col 32); cbn [to_syms]; try (cbn [Nat.eqb]);
    rewrite code_point_ne_newline, of_code_point_code_point, IH; reflexivity.
Qed.

(* Formatting a program at width 32 decodes back to it. *)
Theorem decode_source_format : forall P, decode_source (format_source P) = Some P.
Proof.
  intro P. unfold decode_source, format_source.
  rewrite (lines_fit_format _ 0 ltac:(lia)), to_syms_format.
  apply decode_program_encode_program.
Qed.

Lemma to_syms_code_points : forall l, to_syms (map code_point l) = Some l.
Proof.
  induction l as [| s ss IH]; [reflexivity |].
  cbn [map to_syms]. rewrite code_point_ne_newline, of_code_point_code_point, IH. reflexivity.
Qed.

(* The encoding round trip through decode_source, on one line: exact at the limit. *)
Theorem decode_source_one_line : forall P, length (encode_program P) <= 32 ->
  decode_source (map code_point (encode_program P)) = Some P.
Proof.
  intros P h. unfold decode_source.
  rewrite lines_fit_short by (rewrite length_map; lia).
  rewrite to_syms_code_points. apply decode_program_encode_program.
Qed.

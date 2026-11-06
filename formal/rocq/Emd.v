(* emd: the reference model in Rocq.

   A second formalization, written separately from formal/lean/Emd.lean: same
   ISA, same semantics, same theorems. crates/emd-vm/tests/differential.rs runs
   the Rust VM against the interpreters extracted from both, which is what checks
   that the two definitions agree.

   Stack convention: the head of the list is the top. *)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-abstract-large-number".

(* ---------- Alphabet ---------- *)

Inductive sym := S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7.

Definition sym_index (s : sym) : nat :=
  match s with
  | S0 => 0 | S1 => 1 | S2 => 2 | S3 => 3 | S4 => 4 | S5 => 5 | S6 => 6 | S7 => 7
  end.

(* U+002D U+2010 U+2011 U+2012 U+2013 U+2014 U+2015 U+2212 *)
Definition code_point (s : sym) : nat :=
  match s with
  | S0 => 45 | S1 => 8208 | S2 => 8209 | S3 => 8210
  | S4 => 8211 | S5 => 8212 | S6 => 8213 | S7 => 8722
  end.

Definition sym_of_code_point (n : nat) : option sym :=
  if Nat.eqb n 45 then Some S0
  else if Nat.eqb n 8208 then Some S1
  else if Nat.eqb n 8209 then Some S2
  else if Nat.eqb n 8210 then Some S3
  else if Nat.eqb n 8211 then Some S4
  else if Nat.eqb n 8212 then Some S5
  else if Nat.eqb n 8213 then Some S6
  else if Nat.eqb n 8722 then Some S7
  else None.

Theorem of_code_point_code_point : forall s, sym_of_code_point (code_point s) = Some s.
Proof. destruct s; reflexivity. Qed.

(* ---------- Instructions ---------- *)

Inductive instr :=
  | i_push (n : sym)
  | i_dup | i_drop | i_swap | i_over | i_rot
  | i_add | i_sub | i_mul | i_div | i_mod
  | i_load | i_store
  | i_jmp | i_jz | i_jnz | i_halt | i_call | i_ret
  | i_read | i_write
  | i_eq | i_lt | i_gt | i_not.

Definition encode (i : instr) : sym * sym :=
  match i with
  | i_push n => (S0, n)
  | i_dup => (S1, S0) | i_drop => (S1, S1) | i_swap => (S1, S2) | i_over => (S1, S3) | i_rot => (S1, S4)
  | i_add => (S2, S0) | i_sub => (S2, S1) | i_mul => (S2, S2) | i_div => (S2, S3) | i_mod => (S2, S4)
  | i_load => (S3, S0) | i_store => (S3, S1)
  | i_jmp => (S4, S0) | i_jz => (S4, S1) | i_jnz => (S4, S2) | i_halt => (S4, S3) | i_call => (S4, S4) | i_ret => (S4, S5)
  | i_read => (S5, S0) | i_write => (S5, S1)
  | i_eq => (S6, S0) | i_lt => (S6, S1) | i_gt => (S6, S2) | i_not => (S6, S3)
  end.

Definition decode (p : sym * sym) : option instr :=
  match p with
  | (S0, n) => Some (i_push n)
  | (S1, S0) => Some i_dup | (S1, S1) => Some i_drop | (S1, S2) => Some i_swap | (S1, S3) => Some i_over | (S1, S4) => Some i_rot
  | (S2, S0) => Some i_add | (S2, S1) => Some i_sub | (S2, S2) => Some i_mul
  | (S2, S3) => Some i_div | (S2, S4) => Some i_mod
  | (S3, S0) => Some i_load | (S3, S1) => Some i_store
  | (S4, S0) => Some i_jmp | (S4, S1) => Some i_jz | (S4, S2) => Some i_jnz | (S4, S3) => Some i_halt | (S4, S4) => Some i_call | (S4, S5) => Some i_ret
  | (S5, S0) => Some i_read | (S5, S1) => Some i_write
  | (S6, S0) => Some i_eq | (S6, S1) => Some i_lt | (S6, S2) => Some i_gt | (S6, S3) => Some i_not
  | _ => None
  end.

Theorem decode_encode : forall i, decode (encode i) = Some i.
Proof. destruct i; reflexivity. Qed.

Theorem encode_decode : forall f o i, decode (f, o) = Some i -> encode i = (f, o).
Proof.
  intros f o i H. destruct f, o; simpl in H; inversion H; reflexivity.
Qed.

Fixpoint encode_program (P : list instr) : list sym :=
  match P with
  | [] => []
  | i :: rest => fst (encode i) :: snd (encode i) :: encode_program rest
  end.

Fixpoint decode_program (l : list sym) : option (list instr) :=
  match l with
  | [] => Some []
  | [_] => None
  | f :: o :: rest =>
    match decode (f, o), decode_program rest with
    | Some i, Some tl => Some (i :: tl)
    | _, _ => None
    end
  end.

Theorem decode_program_encode_program :
  forall P, decode_program (encode_program P) = Some P.
Proof.
  induction P as [| i rest IH].
  - reflexivity.
  - destruct i; simpl; rewrite IH; reflexivity.
Qed.

Theorem encode_program_injective :
  forall P Q, encode_program P = encode_program Q -> P = Q.
Proof.
  intros P Q H.
  assert (E := decode_program_encode_program P).
  rewrite H, decode_program_encode_program in E.
  injection E; auto.
Qed.

(* ---------- Source text ---------- *)

(* A source is lines separated by U+000A, each at most 32 code points. Every U+000A is removed
   before decoding, so a break may fall anywhere, even inside a pair, and at the end. *)

(* n code points so far on the current line; every line stays within 32. *)
Fixpoint lines_fit (n : nat) (l : list nat) : bool :=
  match l with
  | [] => true
  | c :: cs =>
    if Nat.eqb c 10 then lines_fit 0 cs else Nat.ltb n 32 && lines_fit (S n) cs
  end.

(* Symbols of a source, line breaks removed; None on any other foreign code point. *)
Fixpoint to_syms (l : list nat) : option (list sym) :=
  match l with
  | [] => Some []
  | c :: cs =>
    if Nat.eqb c 10 then to_syms cs
    else
      match sym_of_code_point c, to_syms cs with
      | Some s, Some r => Some (s :: r)
      | _, _ => None
      end
  end.

Definition decode_source (l : list nat) : option (list instr) :=
  if lines_fit 0 l then
    match to_syms l with
    | Some syms => decode_program syms
    | None => None
    end
  else None.

(* ---------- Semantics ---------- *)

Record state := mkState {
  pc : nat;
  stack : list Z;
  mem : nat -> Z;
  input : list nat;
  output : list nat
}.

Definition init (inp : list nat) : state := mkState 0 [] (fun _ => 0) inp [].

Inductive fault :=
  | stackUnderflow | divisionByZero | negativeAddress | pcOutOfRange | invalidByte.

Inductive outcome :=
  | next (s : state)
  | halted (s : state)
  | faulted (f : fault).

Definition with_stack (s : state) (st : list Z) : state :=
  mkState (pc s) st (mem s) (input s) (output s).

(* pc outside [0, |P|) is a fault, |P| included: a program ends only with halt. *)
Definition jump_to (P : list instr) (s : state) (target : Z) : outcome :=
  if (0 <=? target) && (target <? Z.of_nat (length P))
  then next (mkState (Z.to_nat target) (stack s) (mem s) (input s) (output s))
  else faulted pcOutOfRange.

Definition advance (P : list instr) (s : state) : outcome :=
  jump_to P s (Z.of_nat (pc s) + 1).

Definition binary (P : list instr) (s : state) (f : Z -> Z -> Z) : outcome :=
  match stack s with
  | b :: a :: r => advance P (with_stack s (f a b :: r))
  | _ => faulted stackUnderflow
  end.

Definition div_like (P : list instr) (s : state) (f : Z -> Z -> Z) : outcome :=
  match stack s with
  | b :: a :: r =>
    if b =? 0 then faulted divisionByZero else advance P (with_stack s (f a b :: r))
  | _ => faulted stackUnderflow
  end.

Definition b2z (b : bool) : Z := if b then 1 else 0.

(* Z.quot truncates toward zero, Z.rem takes the sign of the dividend. *)
Definition exec (P : list instr) (s : state) (i : instr) : outcome :=
  match i with
  | i_push n => advance P (with_stack s (Z.of_nat (sym_index n) :: stack s))
  | i_dup =>
    match stack s with
    | a :: r => advance P (with_stack s (a :: a :: r))
    | _ => faulted stackUnderflow
    end
  | i_drop =>
    match stack s with
    | _ :: r => advance P (with_stack s r)
    | _ => faulted stackUnderflow
    end
  | i_swap =>
    match stack s with
    | b :: a :: r => advance P (with_stack s (a :: b :: r))
    | _ => faulted stackUnderflow
    end
  | i_over =>
    match stack s with
    | b :: a :: r => advance P (with_stack s (a :: b :: a :: r))
    | _ => faulted stackUnderflow
    end
  | i_rot =>
    match stack s with
    | c :: b :: a :: r => advance P (with_stack s (a :: c :: b :: r))
    | _ => faulted stackUnderflow
    end
  | i_add => binary P s Z.add
  | i_sub => binary P s Z.sub
  | i_mul => binary P s Z.mul
  | i_div => div_like P s Z.quot
  | i_mod => div_like P s Z.rem
  | i_load =>
    match stack s with
    | a :: r =>
      if a <? 0 then faulted negativeAddress
      else advance P (with_stack s (mem s (Z.to_nat a) :: r))
    | _ => faulted stackUnderflow
    end
  | i_store =>
    match stack s with
    | a :: v :: r =>
      if a <? 0 then faulted negativeAddress
      else advance P (mkState (pc s) r
                        (fun k => if Nat.eqb k (Z.to_nat a) then v else mem s k)
                        (input s) (output s))
    | _ => faulted stackUnderflow
    end
  | i_jmp =>
    match stack s with
    | off :: r => jump_to P (with_stack s r) (Z.of_nat (pc s) + off)
    | _ => faulted stackUnderflow
    end
  | i_jz =>
    match stack s with
    | off :: c :: r =>
      if c =? 0 then jump_to P (with_stack s r) (Z.of_nat (pc s) + off)
      else advance P (with_stack s r)
    | _ => faulted stackUnderflow
    end
  | i_jnz =>
    match stack s with
    | off :: c :: r =>
      if negb (c =? 0) then jump_to P (with_stack s r) (Z.of_nat (pc s) + off)
      else advance P (with_stack s r)
    | _ => faulted stackUnderflow
    end
  | i_halt => halted s
  | i_call =>
    match stack s with
    | off :: r => jump_to P (with_stack s ((Z.of_nat (pc s) + 1) :: r)) (Z.of_nat (pc s) + off)
    | _ => faulted stackUnderflow
    end
  | i_ret =>
    match stack s with
    | a :: r => jump_to P (with_stack s r) a
    | _ => faulted stackUnderflow
    end
  | i_read =>
    match input s with
    | b :: rest => advance P (mkState (pc s) (Z.of_nat b :: stack s) (mem s) rest (output s))
    | [] => advance P (with_stack s (-1 :: stack s))
    end
  | i_write =>
    match stack s with
    | v :: r =>
      if (0 <=? v) && (v <=? 255)
      then advance P (mkState (pc s) r (mem s) (input s) (output s ++ [Z.to_nat v]))
      else faulted invalidByte
    | _ => faulted stackUnderflow
    end
  | i_eq => binary P s (fun a b => b2z (a =? b))
  | i_lt => binary P s (fun a b => b2z (a <? b))
  | i_gt => binary P s (fun a b => b2z (b <? a))
  | i_not =>
    match stack s with
    | a :: r => advance P (with_stack s (b2z (a =? 0) :: r))
    | _ => faulted stackUnderflow
    end
  end.

Definition step (P : list instr) (s : state) : outcome :=
  match nth_error P (pc s) with
  | Some i => exec P s i
  | None => faulted pcOutOfRange
  end.

Definition Step (P : list instr) (s s' : state) : Prop := step P s = next s'.

Theorem step_det : forall P s s1 s2, Step P s s1 -> Step P s s2 -> s1 = s2.
Proof.
  unfold Step. intros P s s1 s2 H1 H2. rewrite H1 in H2. injection H2. auto.
Qed.

Fixpoint run (P : list instr) (fuel : nat) (s : state) : outcome :=
  match fuel with
  | O => next s
  | S n =>
    match step P s with
    | next s' => run P n s'
    | o => o
    end
  end.

Definition example1 : list instr := [i_push S1; i_push S2; i_add; i_halt].

Theorem example1_halts_with_3 :
  exists s, run example1 10 (init []) = halted s /\ stack s = [3].
Proof. eexists. split; reflexivity. Qed.

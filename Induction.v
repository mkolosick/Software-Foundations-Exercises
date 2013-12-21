(* Exercise: 2 stars (andb_true_elim2) *)
Theorem andb_true_elim2 :
  forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intros H.
  destruct b.
  (* CASE: b = true *)
    destruct c.
    (* CASE: c = true *)
      rewrite <- H.
      reflexivity.
    (* CASE: c = false *)
      rewrite <- H.
      reflexivity.
  (* CASE: b = false *)
    destruct c.
    (* CASE: c = true *)
      rewrite <- H.
      reflexivity.
    (* CASE: c = false *)
      rewrite <- H.
      reflexivity.
Qed.

(* Exercise: 2 stars (basic_induction) *)
Theorem mult_0_r :
  forall n : nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n'].
  (* CASE: n = 0 *)
    reflexivity.
  (* CASE: n = S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Lemma plus_r_0 :
  forall n : nat,
  n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  (* CASE: n = 0 *)
    reflexivity.
  (* CASE: n = S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Lemma s_is_add1 :
  forall n : nat,
  S n = n + 1.
Proof.
  intros n.
  induction n as [| n'].
  (* CASE: n = 0 *)
    reflexivity.
  (* CASE: n = S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm :
  forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n'].
  (* CASE: n = 0 *)
    reflexivity.
  (* CASE: n = S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm :
  forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n'].
  (* CASE: n = 0 *)
    rewrite -> plus_r_0.
    reflexivity.
  (* CASE: n = S n' *)
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc :
  forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  (* CASE: n = 0 *)
    reflexivity.
  (* CASE: n = S n' *)
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* Exercise: 2 stars (double_plus) *)
Fixpoint double (n : nat) :=
  match n with
    | 0 => 0
    | S n' => S (S (double n'))
  end.

Lemma double_plus :
  forall n : nat,
  double n = n + n.
Proof.
  intros n.
  induction n as [| n'].
  (* CASE: n = 0 *)
    reflexivity.
  (* CASE: n = S n' *)
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

(* Exercise: 1 star (destruct_induction) *)
(*
induction provides a hypothesis that it is true for the previous case
*)
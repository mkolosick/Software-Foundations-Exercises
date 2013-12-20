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
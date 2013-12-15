(* Exercise: 1 star (nandb) *)
Definition nandb (b1 : bool) (b2 : bool) : bool :=
	match b1 with
		| false => true
		| true => negb b2
	end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

(* Exercise: 1 star (andb3) *)
Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
	match b1 with
		| true => match b2 with
								| true => b3
								| false => false
							end
		| false => false
	end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

(* Exercise: 1 star (factorial) *)
Fixpoint factorial (n : nat) : nat :=
	match n with
		| 0 => 1
		| S n' => (S n') * (factorial n')
	end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

(* Exercise: 2 star (blt_nat) *)
Fixpoint ble_nat (n m : nat) : bool :=
	match n with
		| 0 =>	true
		| S n' =>	match m with
								| 0 => false
								| S m' => ble_nat n' m'
							end
	end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool := ble_nat (n + 1) m.

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.
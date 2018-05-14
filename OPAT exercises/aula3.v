Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 13 2).

(*  plus (S (S (S O))) (S (S O))
==> S (plus (S (S O)) (S (S O)))
      by the second clause of the match
==> S (S (plus (S O) (S (S O))))
      by the second clause of the match
==> S (S (S (plus O (S (S O)))))
      by the second clause of the match
==> S (S (S (S (S O))))
      by the first clause of the match
*)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
  
Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
  
End NatPlayground2.


Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Check ((0 + 1) + 1).


Fixpoint factorial (n:nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_factorial1: (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2: (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.

Fixpoint beq_nat (n m : nat) : bool :=
 match n with
 | O => match m with
        | O => true
        | S m' => false
        end
 | S n' => match m with
           | O => false
           | S m' => beq_nat n' m'
           end
 end.

Fixpoint leb_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb_nat n' m'
      end
  end.
  
Example test_leb1: (leb_nat 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb_nat (n m : nat) : bool :=
  leb_nat (S n) m.


Example test_ltb_nat1: (ltb_nat 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_ltb_nat2: (ltb_nat 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_ltb_nat3: (ltb_nat 4 2) = false.
(* FILL IN HERE *) Admitted.

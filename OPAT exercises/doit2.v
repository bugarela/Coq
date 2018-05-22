Require Import aula3 aula4.
(** Prove the following claim, marking cases (and subcases) with
    bullets when you use [destruct]. *)

(** **** Exercise: 2 stars (andb_true_elim2)  *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  - reflexivity.
  - rewrite <- H. destruct b. 
    + reflexivity.
    + reflexivity.
Qed.

(** **** Exercise: 1 star (zero_nbeq_plus_1)  *)
Theorem zero_nbeq_plus_1 : forall n : nat,
  nat_beq 0 (n + 1) = false.
Proof.
  intros [|n'].
  - reflexivity.
  - reflexivity.
Qed.

(** **** Exercise: 2 stars (boolean_functions)  *)
(** Use the tactics you have learned so far to prove the following
    theorem about boolean functions. *)

Theorem identity_fn_applied_twice :
  forall(f : bool -> bool), (forall(x : bool), f x = x) ->
  forall(b : bool), f (f b) = b.
Proof.
  intros f a b.
  -destruct b.
    +rewrite -> a. rewrite -> a. reflexivity.
    +rewrite -> a. rewrite -> a. reflexivity.
Qed.


(** **** Exercise: 3 stars, optional (andb_eq_orb)  *)
(** Prove the following theorem.  (Hint: This one can be a bit tricky,
    depending on how you approach it.  You will probably need both
    [destruct] and [rewrite], but destructing everything in sight is
    not the best way.) *)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros [] [].
  -intros h. reflexivity.
  -simpl. intros h. rewrite -> h. reflexivity.
  -simpl. intros h. rewrite -> h. reflexivity.
  -intros h. reflexivity.
Qed.

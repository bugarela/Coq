Add LoadPath "." as OPAT.
Require Import OPAT.doit1 OPAT.doit3 OPAT.doit7 OPAT.aula3 OPAT.aula9 OPAT.aula10 OPAT.aula11.
(** adicione outros arquivos que você achar necessário, porém cuidado para não gerar conflito de nomes *)

(** **** Exercise: 3 stars (apply_exercise1)  *)
(** (_Hint_: You can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [Search] is
    your friend.) *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.
(** [] *)

(** **** Exercise: 1 star, optional (apply_rewrite)  *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  What are the situations where both can usefully be
    applied?

(* O apply serve para aplicar hipóteses quantificadas, que vem de premissas em implicações. Em uma umplicação sem quantificação, as duas poderiam ser usadas obtendo o mesmo resultado. *)
*)
(** [] *)

(** **** Exercise: 3 stars, optional (apply_with_exercise)  *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2. rewrite eq2. rewrite eq1. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star (inversion_ex3)  *)
Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1.
  inversion eq2.
  rewrite <- H0.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star (inversion_ex6)  *)
Example inversion_ex6 : forall (X : Type)
                          (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros X x y z l j eq1 eq2.
  inversion eq1.
Qed.
(** [] *)

(** Dois teoremas que foram esquecidos de estar no doit3 (3 Star)!!! *)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n.
  -reflexivity.
  -simpl. rewrite IHn.  rewrite plus_assoc. reflexivity.
Qed.
(** [] *)

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n.
  -reflexivity.
  -simpl. rewrite IHn. rewrite mult_plus_distr_r. reflexivity.
Qed.
   


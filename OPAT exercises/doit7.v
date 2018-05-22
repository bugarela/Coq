Add LoadPath "." as OPAT.
Require Import OPAT.aula9.

(** **** Exercise: 2 stars each one, optional (poly_exercises)  *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Complete the proofs below. *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [ | n l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [ | n' l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [ | n l IHl].
  - reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars each one, optional (more_poly_exercises)  *)
(** Here are some slightly more interesting ones... *)

(** Obs.: Mudei a ordem pra usar essa na próxima =) **)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [ | l l1' IHl1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.
  
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  simpl. induction l as [ | n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite IHl1'. reflexivity.
Qed.
  
(** [] *)

(** **** Exercise: 2 stars, recommended (split)  *)
(** The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
  : (list X) * (list Y) :=
  match l with
  | (x,y) :: ts => (x :: fst (split ts), y :: snd (split ts))
  | [] => ([],[])
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity. Qed.
(** [] *)


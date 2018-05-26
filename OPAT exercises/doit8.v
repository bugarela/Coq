Add LoadPath "." as OPAT.
Require Import OPAT.aula3 OPAT.aula8 OPAT.aula9 OPAT.aula10 OPAT.doit6.

(** **** Exercise: 2 stars (filter_even_gt7)  *)
(** Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] that takes a list of natural numbers as input
    and returns a list of just those that are even and greater than
    7. *)
Fixpoint gt7b (n:nat) : bool :=
  match n with
  | 0 => false
  | 8 => true
  | S n' => gt7b n'
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter evenb (filter gt7b l).

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars (partition)  *)
(** Use [filter] to write a Coq function [partition]:

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list. *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
  : list X * list X :=
(filter test l, filter (fun x => negb (test x)) l). 

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 3 stars (map_rev)  *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)

Lemma distr_map : forall {X Y: Type} (f : X -> Y) (l1 l2 : list X),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2. induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.
  
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [ | n l' IHl'].
  -reflexivity.
  -simpl. rewrite distr_map. simpl. rewrite IHl'. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 2 stars, recommended (flat_map)  *)
(** The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:

        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
  : (list Y) :=
  match l with
  | [] => []
  | x :: t => (f x) ++ (flat_map f t)
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars (fold_length)  *)
(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternative definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** Prove the correctness of [fold_length]. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l. induction l.
  - reflexivity.
  - simpl. rewrite <- IHl. unfold fold_length. simpl. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars (fold_map)  *)
(** We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => f x :: y) l [].

Example test_fold_map : fold_map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Require Import doit3 doit5 aula3 aula5 aula6 aula7 aula8.

(** **** Exercise: 3 stars (list_exercises)  *)
(** More practice with lists: *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [ | l l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [ | l l1' IHl1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.
  

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. simpl. induction l as [ | n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite IHl1'. reflexivity.
Qed.

(** There is a short solution to the next one.  If you find yourself
    getting tangled up, step back and try to look for a simpler
    way. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite app_assoc. rewrite app_assoc. reflexivity.
Qed.

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [ | n l1' IHl1'].
  - reflexivity.
  - destruct n.
      + simpl. rewrite IHl1'. reflexivity.
      + simpl. rewrite IHl1'. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 2 stars (beq_natlist)  *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. *)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Check nat_beq.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | nil => match l2 with
           | nil => true
           | n :: t => false
           end
  | n1 :: t1 => match l2 with
                | nil => false
                | n2 :: t2 => nat_beq n1 n2 && beq_natlist t1 t2
                end
  end.


Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
reflexivity. Qed.

Lemma nat_beq_refl : forall n:nat,
  true = nat_beq n n.
Proof.
   intros n. induction n.
   - reflexivity.
   - simpl. rewrite IHn. reflexivity.
Qed. 

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l as [ | n l1' IHl1'].
  - reflexivity. 
  - simpl. rewrite <- nat_beq_refl. rewrite <- IHl1'. reflexivity.
Qed.

  
(** [] *)

(** **** Exercise: 4 stars, advanced (rev_injective)  *)
(** Prove that the [rev] function is injective -- that is,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

(There is a hard way and an easy way to do this.) *)

(* FILL IN HERE *)
(** [] *)


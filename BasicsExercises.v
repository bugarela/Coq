Fixpoint fatorial (n:nat) : nat :=
  match n with
    | 0 => 1
    | S n => S n * fatorial (n)
  end.
  
Example test_fatorial1: (fatorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_fatorial2: (fatorial 5) = 10*12.
Proof. simpl. reflexivity. Qed.

Fixpoint eq_nat (n m : nat) : bool :=
  match n with
    | 0 => match m with
            | 0 => true
            | S m => false
            end
    | S n => match m with
            | 0 => true
            | S m => eq_nat n m
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
    | 0 => true
    | S n => match m with
               | 0 => false
               | S m => leb n m
             end
  end.

Definition blt_nat (n m : nat) : bool :=
  match leb n m with
    | false => false
    | true => match eq_nat n m with
                | true => false
                | false => true
              end
  end.

Example test_bn1: blt_nat 2 2 = false.
Proof. simpl. reflexivity. Qed.
Example test_bn2: blt_nat 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_bn3: blt_nat 4 2 = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n : forall n:nat, n + 0 = n.
Proof. 
  intros n. simpl.
  Abort.

Theorem plus_n_0 :forall n:nat, n = 0 + n.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

Theorem puls_id_exercise : forall n m o : nat, 
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  rewrite -> H1.
  intros H2.
  rewrite -> H2.
  reflexivity. Qed.


Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  simpl. reflexivity. Qed.

Theorem andb_true : forall b c : bool,
  c = true -> b = true -> andb b c = true.
Proof.
  intros b c.
  intros H1.
  rewrite -> H1.
  intros H2.
  rewrite -> H2.
  reflexivity. Qed.

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

Theorem zero_nbeq_plus_1 : forall n : nat,
  eq_nat 0 (n + 1) = false.
Proof.
  intros [|n'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall(f : bool -> bool), (forall(x : bool), f x = x) ->
  forall(b : bool), f (f b) = b.
Proof.
  intros f a b.
  -destruct b.
    +rewrite -> a. rewrite -> a. reflexivity.
    +rewrite -> a. rewrite -> a. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall(b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros [] [].
  -intros h. reflexivity.
  -simpl. intros h. rewrite -> h. reflexivity.
  -simpl. intros h. rewrite -> h. reflexivity.
  -intros h. reflexivity.
Qed.

Inductive bin : Type :=
  | O' : bin
  | T' : bin -> bin
  | S' : bin -> bin.

Fixpoint incr (n : bin) : bin :=
  match n with
    | O' => S' n
    | T' n => S' (T' n)
    | S' a => T' (S' a)
  end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
    | O'=> 0
    | T' n => 2 * (bin_to_nat n)
    | S' a => 1 + (bin_to_nat a)
  end.

Example test_btn1: bin_to_nat (T'(S' O')) = 2.
Proof. simpl. reflexivity. Qed.

Example test_btn2: bin_to_nat (S'(T'(S' O'))) = 3.
Proof. simpl. reflexivity. Qed.

Example test_incr1: incr (T'(S' O')) = S'(T'(S' O')).
Proof. simpl. reflexivity. Qed.

Example test_incr2: incr O' = S' O'.
Proof. simpl. reflexivity. Qed.

Example test_incr3: incr (S' O') = T' (S' O').
Proof. simpl. reflexivity. Qed.



  
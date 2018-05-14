Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Theorem fridayIsFriday : friday = friday.
Proof.
  reflexivity.
Qed.

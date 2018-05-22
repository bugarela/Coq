Add LoadPath "." as OPAT.
(*** Exercício de Programação Funcional**)

(** Defina um programa que compute o antecessor do antecessor de um dado número n **)

Definition minustwo (n : nat) : nat :=
  match n with
    | 0 => 0
    | S(0) => 0
    | S(S(n)) => n
  end.

(** Teste a função minustwo **)

Example test_minustwo_1 : minustwo 4 = 2.
  Proof. reflexivity. Qed.

Example test_minustwo_2 : minustwo 1 = 0.
  Proof. reflexivity. Qed.

Example test_minustwo_3 : minustwo 0 = 0.
  Proof. reflexivity. Qed.

(** Defina uma função que some 2 **)

Definition plustwo (n : nat) : nat :=
  S(S(n)).

(** Teste a função plustwo **)

Example test_plustwo_1 : plustwo 2 = 4.
  Proof. reflexivity. Qed.

Example test_plustwo_2 : plustwo 0 = 2.
  Proof. reflexivity. Qed.

(** Defina o tipo fruta (morango, uva e laranja) **)
Inductive fruta : Type :=
  | morango : fruta
  | uva : fruta
  | laranja :fruta.

(** Defina o tipo salada, onde uma salada é formada pela combinação de até três frutas **)

Inductive salada : Type :=
  | salada1 : fruta -> salada
  | salada2 : fruta -> fruta -> salada
  | salada3 : fruta -> fruta -> fruta -> salada.

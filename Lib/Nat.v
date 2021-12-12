Require Import Datatypes.
From MyCoq.Lib Require Export Bool.

Inductive nat : Type :=
  | O
  | S (n : nat).


Fixpoint num (n : Datatypes.nat) : nat :=
match n with
| 0 => O
| Datatypes.S m => S (num m)
end.


Fixpoint evenb (n : nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => evenb n'
end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).


Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
          | O => true
          | _ => false
          end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => match m with
          | O => false
          | _ => true
          end
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.


Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | _, O => n
  | S n', S m' => minus n' m'
  end.

Fixpoint mult (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S n', m => plus m (mult n' m)
  end.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S power' => mult base (exp base power')
  end.


Notation "x =? y" := (eqb x y) (at level 70, no associativity).

Notation "x <? y" := (leb x y) (at level 70, no associativity).


Notation "x + y" := (plus x y) (at level 50, left associativity).

Notation "x - y" := (minus x y) (at level 50, left associativity).

Notation "x * y" := (mult x y) (at level 40, left associativity).


Theorem plus_O_n: forall n : nat,
  O + n = n.
Proof.
  reflexivity.
Qed.

Theorem plus_n_O: forall n : nat,
  n + O = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem n_plus_Sm: forall n m : nat,
  n + S m = S (n + m) .
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  (* + 的定义 *)
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

(* 加法交换律 *)
Theorem plus_comm: forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite plus_O_n.
    rewrite plus_n_O.
    reflexivity.
  - simpl.
    rewrite n_plus_Sm.
    rewrite IHn'.
    reflexivity.
Qed.

(* 加法结合律 *)
Theorem plus_assoc: forall a b c : nat,
  a + b + c = a + (b + c).
Proof.
  intros a b c.
  induction a as [| a' IHa'].
  - reflexivity.
  (* 两次应用 + 的定义 *)
  - simpl.
    rewrite IHa'.
    reflexivity.
Qed.

Theorem mult_O_n: forall n : nat,
  O * n = O.
Proof.
  reflexivity.
Qed.

Theorem mult_n_O: forall n : nat,
  n * O = O.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem mult_n_Sm: forall n m : nat,
  n * m + n = n * S m.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  (* * 的定义以及 + 的定义 *)
  - simpl.
    rewrite <- IHn'.
    rewrite -> n_plus_Sm.
    rewrite <- plus_assoc.
    reflexivity.
Qed.

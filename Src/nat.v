Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Inductive nat' : Type :=
  | stop
  | tick (foo : nat').

Definition pred (n : nat) := 
  match n with
  | O => O
  | S (n') => n'
  end.

Check S (S (O)).

Compute pred (S (S (O))).

End NatPlayground.


Check NatPlayground.S (NatPlayground.S (NatPlayground.O)).
Check S (S 0).

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Compute minustwo 4.

(* S 可作用于参数，但不同于函数 *)
Check NatPlayground.S.
Check S.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Compute evenb 2.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.

(* 注意这里的 nat 是标准库中的 *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute plus 2 3.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | _, O => n
  | S n', S m' => minus n' m'
  end.

Compute minus 3 4.
Compute minus 55 4.

Fixpoint mult (n m : nat) : nat :=
  match n, m with
  | O, _ => O
  | S n', m => plus m (mult n' m)
  end.

Compute mult 2 3.

End NatPlayground2.


Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S power' => mult base (exp base power')
  end.

Compute exp 2 3.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Compute 1 + 2.

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

(* at level 代表优先级 *)
(* associativity 代表结合性 *)
Notation "x =? y" := (eqb x y) (at level 50, left associativity).

Example test_eqb1: eqb 2 3 = false.
Proof. simpl. reflexivity. Qed.
Example test_eqb2: 2 =? 3 = false.
Proof. simpl. reflexivity. Qed.
Example test_eqb3: eqb 2 2 = true.
Proof. simpl. reflexivity. Qed.

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

Example test_leb1: leb 0 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 0 0 = false.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 1 0 = false.
Proof. simpl. reflexivity. Qed.

Notation "x <? y" := (leb x y) (at level 50).

Compute 2 <? 3.

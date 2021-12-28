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

Fixpoint ltb (n m : nat) : bool :=
  match n with
  | O => match m with
          | O => false
          | _ => true
          end
  | S n' => match m with
            | O => false
            | S m' => ltb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Example test_leb1: leb 0 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 0 0 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 1 0 = false.
Proof. simpl. reflexivity. Qed.

Notation "x <? y" := (ltb x y) (at level 50).

Notation "x <=? y" := (leb x y) (at level 50).

Compute 2 <? 3.

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (n : bin) : bin :=
  match n with
  | Z => B Z
  | A n' => B n'
  | B n' => A (incr n')
  end.

Fixpoint bin_to_nat (n : bin) : nat :=
  match n with
  | Z => O
  | A n' => 2 * (bin_to_nat n')
  | B n' => 1 + 2 * (bin_to_nat n')
  end.

Example test_bin_incr1: (incr (B Z)) = A (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2: (incr (A (B Z))) = B (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3: (incr (B (B Z))) = A (A (B Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4: bin_to_nat (A (B Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5:
  bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6:
  bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
Proof. simpl. reflexivity. Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Example nat_to_bin1: nat_to_bin 0 = Z.
Proof. simpl. reflexivity. Qed.
Example nat_to_bin2:
  nat_to_bin 5 = B (A (B Z)).
Proof. simpl. reflexivity. Qed.

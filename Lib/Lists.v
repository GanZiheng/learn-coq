From MyCoq.Lib Require Export Nat.

Inductive natprod : Type :=
| pair (n_1 n_2 : nat).


Notation "( x , y )" := (pair x y).
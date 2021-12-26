From MyCoq.Lib Require Export Nat.
From MyCoq.Lib Require Export Poly.


(* apply *)
Theorem silly2: forall (n m o p : nat),
  n = m -> (n = m -> [n; o] = [m; p]) -> [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a: forall (n m : nat),
  (n, n) = (m, m) -> (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) -> [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex: (forall n, evenb n = true -> oddb (S n) = true) -> evenb (N 4) = true -> oddb (N 3) = true.
Proof.
  intros H.
  apply H.
Qed.

Theorem silly3_firsttry: forall (n : nat),
  true = (n =? (N 5)) -> (S (S n)) =? (N 7) = true.
Proof.
  intros n H.
  symmetry.
  apply H.
Qed.

Search rev.
Theorem rev_exercise1: forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l'.
  intros H.
  rewrite H.
  rewrite rev_involutive .
  reflexivity.
Qed.


(* apply with *)
Theorem trans_eq: forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example: forall (a b c d e f : nat),
  [a; b] = [c; d] -> [c; d] = [e; f] -> [a; b] = [e; f].
Proof.
  intros a b c d e f eq1 eq2.
  (* 根据引理结论对证明目标进行匹配的过程中并没有为 m 确定实例 *)
  apply trans_eq with (m := [c; d]).
  - apply eq1.
  - apply eq2.
Qed.

Example trans_eq_exercise: forall (n m o p : nat),
  m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros n m o p.
  intros eq1 eq2.
  apply trans_eq with (m := m).
  - apply eq2.
  - apply eq1.
Qed.


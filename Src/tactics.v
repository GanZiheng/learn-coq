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


(* The injection and discriminate Tactics *)
Theorem S_injective: forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)).
  { 
    reflexivity.
  }
  rewrite H2.
  rewrite H1.
  reflexivity.
Qed.

Theorem S_injective': forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1: forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Theorem injection_ex2: forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H.
  injection H.
  intros H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Example injection_ex3: forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j.
  intros H1 H2.
  injection H1 as H11 H12.
  rewrite H2 in H12.
  injection H12 as H3.
  rewrite H11.
  rewrite H3.
  reflexivity.
Qed.

Theorem eqb_0_l: forall n,
   O =? n = true -> n = O.
Proof.
  intros [| n'].
  - reflexivity.
  - intros H.
    discriminate.
Qed.

Theorem discriminate_ex1: forall (n : nat),
  S n = O -> N 2 + N 2 = N 5.
Proof.
  intros n.
  intros contra.
  discriminate contra.
Qed.

Example discriminate_ex3: forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] -> x = z.
Proof.
  intros x y z l j.
  intros contra.
  discriminate.
Qed.

Theorem f_equal: forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros  A B f x y.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal': forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m H.
  apply f_equal.
  apply H.
Qed.


(* 对假设使用策略 *)
Theorem S_inj: forall (n m : nat) (b : bool),
  (S n) =? (S m) = b -> n =? m = b.
Proof.
  intros n m b.
  intros H.
  simpl in H.
  apply H.
Qed.

Theorem silly3': forall (n : nat),
  (n =? N 5 = true -> (S (S n)) =? N 7 = true) ->
  true = (n =? N 5) ->
  true = ((S (S n)) =? N 7).
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.


(* 变换归纳假设 *)
Theorem double_injective: forall (n m : nat),
  double n = double m -> n = m.
Proof.
  induction n as [| n' IHn'] .
  - simpl.
    intros [| m'] H.
    + reflexivity.
    + discriminate H.
  - simpl.
    intros [| m'] H.
    + discriminate.
    + apply f_equal.
      apply IHn'.
      injection H as goal.
      apply goal.
Qed.

Theorem eqb_true: forall n m,
  n =? m = true -> n = m.
Proof.
  induction n as [| n' IHn'].
  - intros [| m'] H.
    + reflexivity.
    + discriminate.
  - intros [| m'] H.
    + discriminate.
    + apply f_equal.
      apply IHn'.
      simpl in H.
      apply H.
Qed.

Theorem plus_n_n_injective: forall n m,
  n + n = m + m -> n = m.
Proof.
  induction n as [| n'].
  - intros [| m'] H.
    + reflexivity.
    + discriminate.
  - intros [| m'] H.
    + discriminate.
    + apply f_equal.
      apply IHn'.
      simpl in H.
      rewrite plus_n_Sm in H.
      rewrite plus_n_Sm in H.
      injection H as H'.
      apply H'.
Qed.

Theorem double_injective_take2: forall (n m : nat),
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' IHm'] .
  - simpl.
    intros [| n'] H.
    + reflexivity.
    + discriminate H.
  - simpl.
    intros [| n'] H.
    + discriminate.
    + apply f_equal.
      apply IHm'.
      injection H as goal.
      apply goal.
Qed.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X.
  induction n as [| n'].
  - destruct l as [| n l']. 
    + reflexivity.
    + intros H.
      discriminate H.
  - intros [| n l'] H.
    + reflexivity.
    + apply IHn'.
      injection H as H'.
      apply H'.
Qed.


(* 展开定义 *)
Definition square n := n * n.

Lemma square_mult: forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  rewrite mult_assoc.
  assert (H: n * m * n = n * n * m).
  {
    rewrite mult_comm.
    rewrite mult_assoc.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => N 5
  | S _ => N 5
  end.

Fact silly_fact: forall m, bar m + N 1 = bar (m + N 1) + N 1.
Proof.
  intros m.
  unfold bar.
  destruct m as [| m'].
  - reflexivity.
  - reflexivity.
Qed.


(* 对复合表达式使用 destruct *)
Definition sillyfun (n : nat) : bool :=
  if n =? N 3 then false
  else if n =? N 5 then false
  else false.

Theorem sillyfun_false: forall (n : nat),
  sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (n =? N 3) eqn : E1.
  - reflexivity.
  - destruct (n =? N 5) eqn : E2.
    + reflexivity.
    + reflexivity.
Qed.

Theorem combine_split: forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y.
  intros l.
  (* induction 后加 eqn : E 会产生矛盾的假设 *)
  induction l as [| n l' IHl'].
  - intros l1 l2 H.
    injection H as H1 H2.
    rewrite <- H1.
    rewrite <- H2.
    reflexivity.
  - destruct n as [n1 n2].
    simpl.
    destruct (split l') as [l1' l2'].
    intros l1 l2 H.
    injection H as H1 H2.
    rewrite <- H1.
    rewrite <- H2.
    simpl. 
    assert (Hc: combine l1' l2' = l').
    { 
      apply IHl'.
      - reflexivity.
    }
    rewrite Hc.
    reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? N 3 then true
  else if n =? N 5 then true
  else false.

Theorem sillyfun1_odd_FAILED: forall (n : nat),
  sillyfun1 n = true -> oddb n = true.
Proof.
  intros n.
  intros H.
  unfold sillyfun1 in H.
  destruct (n =? N 3) eqn : Heq3.
  - apply eqb_true in Heq3.
    rewrite Heq3.
    reflexivity.
  - destruct (n =? N 5) eqn : Heq5.
    + apply eqb_true in Heq5.
      rewrite Heq5.
      reflexivity.
    + discriminate.
Qed.

Theorem bool_fn_applied_thrice: forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f.
  intros b.
  destruct b eqn : Eb.
  - destruct (f true) eqn : Et.
    + rewrite Et, Et.
      reflexivity.
    + destruct (f false) eqn : Ef.
      * apply Et.
      * apply Ef.
  - destruct (f true) eqn : Et.
    + destruct (f false) eqn : Ef.
      * rewrite Et, Et.
        reflexivity.
      * rewrite Ef, Ef.
        reflexivity.
    + destruct (f false) eqn : Ef.
      * rewrite Et, Ef.
        reflexivity.
      * rewrite Ef, Ef.
        reflexivity.
Qed.


(* exercises *)
Theorem eqb_sym: forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  induction n as [| n'].
  - intros [| m'].
    + reflexivity.
    + simpl.
      reflexivity.
  - intros [| m'].
    + simpl.
      reflexivity.
    + simpl.
      apply IHn'.
Qed.

Theorem eqb_trans: forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p.
  intros H1 H2.
  apply eqb_true in H1.
  apply eqb_true in H2.
  rewrite -> H1.
  rewrite <- H2.
  apply self_eq.
Qed.

Definition split_combine_statement : Prop :=
  forall (X Y : Type) (l1 : list X) (l2 : list Y) (l : list (X * Y)),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).

Theorem split_combine: split_combine_statement.
Proof.
  unfold split_combine_statement.
  intros X Y.
  induction l1 as [| n1 l1' IHl1'].
  - intros l2 l.
    intros H1 H2.
    destruct l2 as [| n2 l2'].
    + rewrite <- H2.
      simpl.
      reflexivity.
    + discriminate H1.
  - intros l2 l.
    intros H1 H2.
    destruct l2 as [| n2 l2'].
    + discriminate H1.
    + simpl in H2.
      rewrite <- H2.
      simpl.
      assert (Hsc: split (combine l1' l2') = (l1', l2')).
      {
        apply IHl1'.
        - simpl in H1.
          injection H1 as H1'.
          apply H1'.
        - reflexivity.
      }
      rewrite Hsc.
      reflexivity.
Qed.

Theorem filter_exercise: forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros X.
  intros test.
  intros x.
  induction l as [| n l'].
  - intros lf.
    intros H.
    simpl in H.
    discriminate H.
  - intros lf.
    intros H.
    simpl in H.
    destruct (test n) eqn : E.
    + injection H as H' H''.
      rewrite <- H'.
      apply E.
    + apply IHl' with (lf := lf).
      apply H.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: y => (test x) && forallb test y
  end.

Example test_forallb1: forallb oddb [N 1; N 3; N 5; N 7; N 9] = true.
Proof. simpl. reflexivity. Qed.
Example test_forallb2: forallb (eqb (N 5)) [] = true.
Proof. simpl. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | x :: y => (test x) || existsb test y
  end.

Example test_existsb1: existsb (andb true) [true; true; false] = true.
Proof. simpl. reflexivity. Qed.
Example test_existsb2: existsb (eqb (N 5)) [] = false.
Proof. simpl. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun (x : X) => negb (test x)) l).

Example test_existsb'1: existsb (andb true) [true; true; false] = true.
Proof. simpl. reflexivity. Qed.
Example test_existsb'2: existsb (eqb (N 5)) [] = false.
Proof. simpl. reflexivity. Qed.

Theorem existsb_existsb': forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X.
  intros test.
  unfold existsb'.
  induction l as [| n l'].
  - simpl.
    reflexivity.
  - simpl.
    destruct (test n) eqn : E.
    + simpl.
      reflexivity. 
    + simpl.
      apply IHl'.
Qed.

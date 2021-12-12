From MyCoq.Src Require Export nat.

(* simpl 来化简, reflexivity 来检查两边*)
Theorem plus_0_n: forall n : nat, O + n = n.
Proof.
  intros n. simpl. reflexivity.
Qed.

(* reflexivity 自动做一些化简 *)
Theorem plus_0_n': forall n : nat, O + n = n.
Proof.
  intros n. reflexivity.
Qed.

(* intros 将量词从证明目标转移到当前假设的上下文中 *)
Theorem plus_0_n'': forall n : nat, O + n = n.
Proof.
  intros m. simpl. reflexivity.
Qed.

Theorem plus_1_l: forall n : nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem mult_0_l: forall n : nat, O * n = O.
Proof.
  intros n. simpl. reflexivity.
Qed.


(* 基于改写 *)

Theorem plus_id_example: forall n m : nat, 
  n = m ->
  n + n = m + m.
Proof.
  (* 将两个量词移到上下文中 *)
  intros n m.
  (* 将前提移到上下文中 *)
  intros H.
  (* 用前提改写目标 *)
  rewrite -> H.
  (* 箭头不代表蕴含, 只指明改写方向 *)
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_id_exercise_not_proved: forall n m O : nat,
  n = m -> m = O -> n + m = m + O.
Proof.
Admitted.

(* Admitted 不加证明地接受事实 *)
Check plus_id_exercise_not_proved.

Theorem plus_id_exercise: forall n m O : nat,
  n = m -> m = O -> n + m = m + O.
Proof.
  intros n m O.
  intros H_1 H_2.
  rewrite -> H_1.
  rewrite -> H_2.
  reflexivity.
Qed.

Check plus_id_exercise.

(* 下面是几个标准库中的定理 *)
(* 注意是大写 O *)
Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0: forall n m : nat,
  (n * 0) + (m * 0) = 0.
Proof.
  intros n m.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem mult_n_1: forall n : nat,
  n * 1 = n.
Proof.
  intros n.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem mult_O_n: forall n : nat,
  O * n = O.
Proof.
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

Check plus_O_n.

(* 加法交换律 *)
Theorem plus_comm: forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite -> plus_O_n.
    rewrite <- plus_n_O.
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


(* 基于情况分析 *)

Theorem plus_1_neq_0: forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  destruct n as [| n'] eqn : E.
  - reflexivity.
  - reflexivity.
Qed.

Check andb.

(* 可以加上 as [] *)

Theorem andb_commutative: forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b eqn : Eb.
  - destruct c eqn : Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn : Ec.
    + reflexivity.
    + reflexivity.
Qed.

(* 一种简便写法, 代价是无法标记每个子目标中的假设 *)
Theorem plus_1_neq_0': forall n : nat,
  (n + 1) =? 0 = false.
Proof. 
  intros [| n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'': forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2: forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intro H.
  destruct b as [] eqn : Eb.
  - destruct c as [] eqn : Ec.
    + reflexivity.
    (* 将 true 改写 *)
    + rewrite <- H.
      reflexivity.
  - destruct c as [] eqn : Ec.
    + reflexivity.
    + rewrite <- H.
      reflexivity. 
Qed.

Theorem zero_nbeq_plus_1: forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [| n].
  - reflexivity.
  - reflexivity. 
Qed.


(* 归纳证明 *)

Theorem plus_n_O: forall n : nat,
  n = n + 0.
Proof.
  intros n.
  induction n as [| n' IHn'].
  (* n = 0 *)
  - reflexivity.
  (* n = S n' *) 
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

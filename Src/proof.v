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

Theorem plus_n_Sm: forall n m : nat,
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
    rewrite plus_n_Sm.
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
    rewrite -> plus_n_Sm.
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

(* 未必要同时引入所有前提 *)
Theorem andb_eq_orb:
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros [] [].
  - reflexivity.
  - simpl.
    (* 先简化后引入 *)
    intros H.
    rewrite H.
    reflexivity.
  - simpl.
    intros H.
    rewrite H.
    reflexivity.
  - reflexivity.
Qed.


(* 证明里的证明 *)

Theorem mult_0_plus': forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  {
    reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange: forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  {
    rewrite plus_comm.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.


(* more exercise *)

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  assert (H: n + m = m + n).
  {
    rewrite plus_comm.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction m as [| m' IHm'].
  - rewrite <- mult_n_O.
    reflexivity.
  - rewrite <- mult_n_Sm.
    simpl.
    rewrite IHm'.
    rewrite plus_comm.
    reflexivity.
Qed.

(* 需要归纳 *)
Theorem leb_refl: forall n : nat,
  true = (n <=? n).
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

(* 直接化简 *)
Theorem zero_nbeq_S: forall n : nat,
  0 =? (S n) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(* 需要分类 *)
Theorem andb_false_r: forall b : bool,
  andb b false = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

(* 需要归纳 *)
Theorem plus_ble_compat_l: forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [| p' IHp'].
  - simpl.
    rewrite H.
    reflexivity.
  - simpl.
    rewrite IHp'.
    reflexivity.
Qed.

(* 直接计算 *)
Theorem S_nbeq_0: forall n:nat,
  (S n) =? 0 = false.
Proof.
  simpl.
  reflexivity.
Qed.

(* 计算加改写 *)
Theorem mult_1_l: forall n : nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

(* 需要分类 *)
Theorem all3_spec: forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* 需要归纳 *)
Theorem mult_plus_distr_r: forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [| n IHn'].
  - induction p as [| p IHp'].
    + reflexivity.
    + reflexivity.
  - simpl.
    assert (H: p + n * p + m * p = p + (n * p + m * p)).
    {
      rewrite -> plus_assoc.
      reflexivity.
    }
    rewrite -> H.
    rewrite <- IHn'.
    reflexivity.
Qed.

(* 需要归纳 *)
Theorem mult_assoc: forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> mult_plus_distr_r.
    rewrite IHn'.
    reflexivity.
Qed.

Lemma bin_to_nat_incr_helper: forall n : nat,
  S (S (n)) + S (S (n)) = S (S (S (n + S(n)))).
Proof.
  intros n.
  simpl.
  rewrite plus_n_Sm.
  reflexivity.
Qed.

Lemma bin_to_nat_incr: forall n : bin,
  bin_to_nat (incr n) = S (bin_to_nat n).
Proof.
  intros [| n' | n''].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - induction n'' as [| m'| m''].
    + simpl.
      reflexivity.
    + simpl.
      rewrite <- plus_n_O.
      rewrite <- plus_n_O.
      rewrite -> plus_n_Sm.
      reflexivity.
    + simpl.
      simpl in IHm''.
      rewrite <- plus_n_O in IHm''.
      rewrite <- plus_n_O in IHm''.
      rewrite <- plus_n_O.
      rewrite <- plus_n_O.
      rewrite <- plus_n_O.
      rewrite <- plus_n_O.
      rewrite -> IHm''.
      rewrite bin_to_nat_incr_helper.
      reflexivity.
Qed.

(* 可以不用指明 n 的类型 *)
Theorem nat_bin_nat: forall n,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> bin_to_nat_incr.
    rewrite IHn'.
    reflexivity.
Qed.

Definition double_bin (n : bin) : bin :=
  match n with
  | Z => Z
  | _ => A n
  end.

Fixpoint normalize (n : bin) : bin :=
  match n with
  | Z => Z
  | A n' => double_bin (normalize n')
  | B n' => B (normalize n')
  end.

Example test_normalize1: normalize (A (A Z)) = Z.
Proof. simpl. reflexivity. Qed.
Example test_normalize2: normalize (B (A Z)) = B Z.
Proof. simpl. reflexivity. Qed.
Example test_normalize3: normalize (B (A (A Z))) = B Z.
Proof. simpl. reflexivity. Qed.
Example test_normalize4: normalize (A (B (A Z))) = A (B Z).
Proof. simpl. reflexivity. Qed.

Lemma nat_to_bin_Sn: forall n : nat,
  nat_to_bin (S n) = incr (nat_to_bin n).
Proof.
  intros [| n'].
  - reflexivity.
  - reflexivity.
Qed.

Lemma double_incr: forall n : bin,
  double_bin (incr n) = incr (incr (double_bin n)).
Proof.
  intros [| n' | n''].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma nat_to_bin_double : forall n,
  nat_to_bin (n + n) = double_bin (nat_to_bin n).
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite plus_n_Sm.
    rewrite nat_to_bin_Sn.
    rewrite IHn'.
    rewrite double_incr.
    reflexivity.
Qed.

Lemma incr_double: forall n,
  incr (double_bin n) = B n.
Proof.
  intros [| n' | n''].
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem bin_nat_bin: forall n,
  nat_to_bin (bin_to_nat n) = normalize n.
Proof.
  induction n as [| n' | n''].
  - reflexivity.
  - simpl.
    rewrite <- plus_n_O.
    rewrite nat_to_bin_double.
    rewrite IHn'.
    reflexivity.
  - simpl.
    rewrite <- plus_n_O.
    rewrite nat_to_bin_double.
    rewrite IHn''.
    rewrite incr_double.
    reflexivity.
Qed.

Theorem incr_norm: forall n : bin,
  incr (normalize n) = normalize (incr n).
Proof.
  induction n as [| n' | n''].
  - reflexivity.
  - simpl.
    destruct (normalize n') as [| m' | m''].
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - simpl.
    rewrite -> IHn''.
    destruct n'' as [| m' | m''].
    + reflexivity.
    + reflexivity.
    + destruct (incr (B m'')) eqn : E.
      * discriminate E.
      * rewrite <- IHn''.
        reflexivity.
      * reflexivity. 
Qed.

Theorem incr_norm': forall n : bin,
  incr (normalize n) = normalize (incr n).
Proof.
  induction n as [| n' | n''].
  - reflexivity.
  - simpl.
    destruct (normalize n') as [| m' | m''].
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - simpl.
    destruct (n'') as [| m' | m''].
    + reflexivity.
    + rewrite IHn''.
      reflexivity.
    (* 顺序相关
       消去可能递归的情况 *)
    + rewrite <- IHn''.
      reflexivity. 
Qed.

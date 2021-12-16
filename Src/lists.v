From MyCoq.Lib Require Export Nat.


(* 数值序对 *)

Inductive natprod : Type :=
| pair (n_1 n_2 : nat).

Check pair (N 1) (N 2).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Compute (fst (pair (N 1) (N 2))).

Notation "( x , y )" := (pair x y).

Compute (fst ((N 1), (N 2))).

Definition snd (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x, y) => (y, x)
  end.

Compute swap_pair (N 1, N 2).

Theorem surjective_pairing : forall p : natprod,
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall p : natprod,
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.


(* 数值列表 *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: y" := (cons x y) (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Compute N 1 :: (N 2 :: nil).
Compute [].
Compute [N 1; N 2; N 3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Compute repeat (N 2).

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Compute length (N 1 :: (N 2 :: nil)).
Compute length [].
Compute length [N 1; N 2; N 3].

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Compute [N 1] ++ [N 1; N 2; N 3].

Definition hd (default : nat) (l : natlist) : nat := 
  match l with
  | nil => default
  | cons n _ => n
  end.

(* 除去首个元素的其余部分 *)
Definition tl (l : natlist) : natlist := 
  match l with
  | nil => nil
  | cons n m => m
  end.

Compute hd (N 0) (N 2 :: nil).
Compute hd (N 0) (nil).
Compute tl (N 2 :: nil).

(* 获取最后一个元素 *)
Fixpoint last (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | x :: y => last x y
  end.

Compute last O [N 1; N 3].
Compute last O [].

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil => nil
  | x :: y => match x with
              | O => nonzeros y
              | S _ => x :: (nonzeros y)
              end
  end.

Compute nonzeros [N 0; N 1; N 0; N 2; N 3; N 0; N 0].

Example test_nonzeros:
  nonzeros [N 0; N 1; N 0; N 2; N 3; N 0; N 0] = [N 1; N 2; N 3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | nil => nil
  | x :: y => match oddb x with
              | true => x :: oddmembers y
              | false => oddmembers y
              end
  end.

Example test_oddmembers:
  oddmembers [N 0; N 1; N 0; N 2; N 3; N 0; N 0] = [N 1; N 3].
Proof. simpl. reflexivity. Qed.

Fixpoint countoddmembers (l : natlist) : nat :=
  match l with
  | nil => O
  | x :: y => match oddb x with
              | true => N 1 + countoddmembers y
              | false => countoddmembers y
              end
  end.

Example test_countoddmembers1:
  countoddmembers [N 1; N 0; N 3; N 1; N 4; N 5] = N 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [N 0; N 2; N 4] = N 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = N 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l_1 l_2 : natlist) : natlist :=
  match l_1 with
  | nil => l_2
  | x :: y => match l_2 with
              | nil => l_1
              | m :: n => [x; m] ++ alternate y n
              end
  end.

Example test_alternate1:
  alternate [N 1; N 2; N 3] [N 4; N 5; N 6] = [N 1; N 4; N 2; N 5; N 3; N 6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [N 1] [N 4; N 5; N 6] = [N 1; N 4; N 5; N 6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [N 1; N 2; N 3] [N 4] = [N 1; N 4; N 2; N 3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [N 20; N 30] = [N 20; N 30].
Proof. simpl. reflexivity. Qed.


Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => O
  | x :: y => match x =? v with
              | true => N 1 + count v y
              | false => count v y
              end
  end.

Example test_count1:
  count (N 1) [N 1; N 2; N 3; N 1; N 4; N 1] = N 3.
Proof. simpl. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  v :: s.

Example test_add1: count (N 1) (add (N 1) [N 1; N 4; N 1]) = N 3.
Proof. simpl. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | nil => false
  | x :: y => (x =? v) || (member v y)
  end.

Example test_member1: member (N 1) [N 1; N 4; N 1] = true.
Proof. simpl. reflexivity. Qed.

Example test_member2: member (N 2) [N 1; N 4; N 1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | x :: y => match x =? v with
              | true => y
              | false => x :: remove_one v y
              end
  end.

Example test_remove_one1: remove_one (N 5) [N 2; N 1; N 5; N 4; N 1] = [N 2; N 1; N 4; N 1].
Proof. simpl. reflexivity. Qed.
Example test_remove_one2: remove_one (N 5) [N 2; N 1; N 5; N 4; N 1; N 5] = [N 2; N 1; N 4; N 1; N 5].
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
  | nil => nil
  | x :: y => match x =? v with
              | true => remove_all v y
              | false => x :: remove_all v y
              end
  end.

Example test_remove_all1: remove_all (N 5) [N 2; N 1; N 5; N 4; N 1] = [N 2; N 1; N 4; N 1].
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: remove_all (N 5) [N 2; N 1; N 5; N 4; N 1; N 5] = [N 2; N 1; N 4; N 1].
Proof. simpl. reflexivity. Qed.


(* 有关列表的论证 *)
Theorem nil_app: forall l : natlist,
  [] ++ l = l.
Proof.
  reflexivity.
Qed.

Theorem tl_length_pred: forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros [| n l'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem app_assoc: forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n1 l1'].
  - reflexivity.
  - simpl.
    (* 注意结合性 *)
    rewrite IHl1'.
    reflexivity.
Qed.

(* 性质不随记号变化 *)
Theorem app_assoc': forall l1 l2 l3 : natlist,
  app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n1 l1'].
  - reflexivity.
  - simpl.
    (* 注意结合性 *)
    rewrite IHl1'.
    reflexivity.
Qed.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Lemma app_length: forall l1 l2 : natlist,
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  - reflexivity.
  - simpl.
    rewrite IHl1'.
    reflexivity.
Qed. 

Theorem rev_length_firsttry: forall l : natlist,
  length (rev l) = length l.
Proof.
  induction l as [| n l'].
  - reflexivity.
  - simpl.
    rewrite app_length.
    rewrite IHl'.
    simpl.
    rewrite plus_n_Sm.
    rewrite plus_n_O.
    reflexivity.
Qed.

Theorem app_nil_r: forall l : natlist,
  l ++ [] = l.
Proof.
  induction l as [| n l'].
  - reflexivity.
  - simpl.
    rewrite IHl'.
    reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl.
    rewrite <- app_assoc.
    rewrite IHl1'.
    reflexivity.
Qed.

Theorem rev_involutive: forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l as [| n l'].
  - reflexivity.
  - simpl.
    rewrite rev_app_distr.
    rewrite IHl'.
    reflexivity.
Qed.

Theorem app_assoc4: forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite app_assoc.
  rewrite app_assoc.
  reflexivity.
Qed.

Lemma nonzeros_app: forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| n l1'].
  - reflexivity.
  - simpl.
    destruct n as [| n'].
    + rewrite IHl1'.
      reflexivity.
    + simpl.
      rewrite IHl1'.
      reflexivity.
Qed.

Theorem eq_sym: forall n m,
  (n =? m) = (m =? n).
Proof.
  (* 不可同时引入 n 和 m *)
  (* 否则 m 会被当作一个常数 *)
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

Lemma leb_n_n: forall n : nat,
  n <=? S n = true.
Proof.
  induction n as [| n'].
  - reflexivity.
  - simpl.
    apply IHn'.
Qed. 

Theorem remove_does_not_increase_count: forall (s : bag),
  (count (N 0) (remove_one (N 0) s)) <=? (count (N 0) s) = true.
Proof.
  induction s as [| n s'].
  - reflexivity.
  - simpl in IHs'.
    destruct n as [| n'].
    + simpl.
      apply leb_n_n.
    + simpl.
      apply IHs'.
Qed.  

Theorem rev_injective: forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intros H.
  assert (H': rev (rev l1) = rev (rev l2)).
  {
    (* TODO: why apply invalid *)
    rewrite H.
    reflexivity.
  }
  rewrite rev_involutive in H'.
  rewrite rev_involutive in H'.
  apply H'.
Qed.


(* Options *)

Fixpoint nth_bad (l : natlist) (n : nat) : nat :=
  match l with
  | nil => N 42
  | a :: l' => match n with
               | O => a
               | S n' => nth_bad l' n'
               end
  end.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
                | O => Some a
                | S n' => nth_error l' n'
                end
  end.

Example test_nth_error1: nth_error [N 4; N 5; N 6; N 7] (N 0) = Some (N 4).
Proof. simpl. reflexivity. Qed.
Example test_nth_error2: nth_error [N 4; N 5; N 6; N 7] (N 3) = Some (N 7).
Proof. simpl. reflexivity. Qed.
Example test_nth_error3: nth_error [N 4; N 5; N 6; N 7] (N 9) = None.
Proof. simpl. reflexivity. Qed.

Fixpoint nth_error' (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? O then Some a
               else nth_error' l' (pred n)
  end.

Example test_nth_error': nth_error' [N 4; N 5; N 6; N 7] (N 0) = Some (N 4).
Proof. simpl. reflexivity. Qed.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | x :: _ => Some x
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. simpl. reflexivity. Qed.
Example test_hd_error2 : hd_error [N 1] = Some (N 1).
Proof. simpl. reflexivity. Qed.
Example test_hd_error3 : hd_error [N 5; N 6] = Some (N 5).
Proof. simpl. reflexivity. Qed.


(* Partial Maps *)

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) := 
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl: forall x, true = eqb_id x x.
Proof.
  intros [x'].
  simpl.
  rewrite self_eq.
  reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
  record x value d.

Fixpoint find(x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record key value d' => if eqb_id x key
                           then Some value
                           else find x d'
  end.

Theorem update_eq: forall (d : partial_map) (x : id) (v: nat),
  find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl.
  rewrite <- eqb_id_refl.
  reflexivity.
Qed.

Theorem update_neq: forall (d : partial_map) (x y : id) (o: nat),
  eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o.
  intros H.
  simpl.
  rewrite H.
  reflexivity.
Qed.

(* 构造不出 baz 类型 *)
Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

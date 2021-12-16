From MyCoq.Lib Require Export Nat.


(* 多态 *)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list.
Check (nil nat).
Check (cons nat (N 3) (nil nat)).

Check nil.
Check cons.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1:
  repeat nat (N 4) (N 2) = cons nat (N 4) (cons nat (N 4) (nil nat)).
Proof. simpl. reflexivity. Qed.

Example test_repeat2:
  repeat bool false (N 1) = cons bool false (nil bool).
Proof. simpl. reflexivity. Qed.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(* Check d (b a (N 5)). *)
Check d mumble (b a (N 5)).
Check d bool (b a (N 5)).
Check e bool true.
Check e mumble (b c O).
(* Check e bool (b c O). *)
(* Check c. *)

(* 类型标注的推断 *)
Fixpoint repeat' X x count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat.
Check repeat'.

(* 类型参数的推断 *)
Fixpoint repeat'' X x count : list X :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(* 隐式参数 *)
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list_nat := cons (N 1) nil.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat''' x count')
  end.

Check repeat'''.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | cons _ l' => S (length l')
  end.

(* 显式提供类型参数 *)
Fail Definition mynil := nil nat.
Definition mynil := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list_nat' := [true; false; false].

Theorem app_nil_r: forall (X : Type), forall l : list X,
  l ++ [] = l.
Proof.
  induction l as [| n l'].
  - reflexivity.
  - simpl.
    rewrite IHl'.
    reflexivity.
Qed.

Theorem app_assoc: forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  induction l as [| x l'].
  - reflexivity.
  - simpl.
    intros m n.
    rewrite IHl'.
    reflexivity.
Qed.

Lemma app_length: forall (X : Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1 as [| n1 l1'].
  - reflexivity.
  - simpl.
    intros l2.
    rewrite IHl1'.
    reflexivity.
Qed.


Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1 as [| n1 l1'].
  - simpl.
    intros l2.
    rewrite app_nil_r.
    reflexivity.
  - simpl.
    intros l2.
    rewrite IHl1'.
    rewrite app_assoc.
    reflexivity.
Qed. 

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  induction l as [| n l'].
  - reflexivity.
  - simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite IHl'.
    reflexivity.
Qed.

(* 多态序对 *)
Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).
Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).

(* 积类型 Product Types *)
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y :Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y :Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Check @combine.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil => (nil, nil)
  | x :: y => match x with
              | (m, n) => match split y with
                              | (l1, l2) => (m :: l1, n :: l2)
                              end
              end
  end.

Example test_split:
  split [(N 1,false);(N 2,false)] = ([N 1; N 2],[false;false]).
Proof. simpl. reflexivity. Qed.

(* 多态候选 *)
Inductive option (X : Type) : Type :=
  | Some (x : X)
  | None.
Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | x :: y => if n =? O
              then Some x
              else nth_error y (pred n)
  end.

Example test_nth_error1: nth_error [N 4; N 5; N 6; N 7] (N 0) = Some (N 4).
Proof. simpl. reflexivity. Qed.
Example test_nth_error2: nth_error [[N 1];[N 2]] (N 1) = Some [N 2].
Proof. simpl. reflexivity. Qed.
Example test_nth_error3: nth_error [true] (N 2) = None.
Proof. simpl. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | x :: y => Some x
  end.

Check @hd_error.
Example test_hd_error1: hd_error [N 1; N 2] = Some (N 1).
Proof. simpl. reflexivity. Qed.
Example test_hd_error2: hd_error [[N 1]; [N 2]] = Some [N 1].
Proof. simpl. reflexivity. Qed.


(* 函数作为数据 *)

(* 高阶函数 *)
Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times.
Example test_doit3times': doit3times negb true = false.
Proof. simpl. reflexivity. Qed.

(* 过滤器 *)
Fixpoint filter {X : Type} (test: X -> bool) (l : list X) : (list X) :=
  match l with
  | [] => []
  | x :: y => if test x
              then x :: filter test y
              else filter test y
  end.

Example test_filter1: filter evenb [N 1; N 2; N 3; N 4] = [N 2; N 4].
Proof. simpl. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  length l =? N 1.

(* 匿名函数 *)
Example test_anon_fun':
  doit3times (fun n => n * n) (N 2) = N 256.
Proof. simpl. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => evenb n && ((N 7) <=? n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [N 1; N 2; N 6; N 9; N 10; N 3; N 12; N 8] = [N 10; N 12; N 8].
Proof. simpl. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [N 5; N 2; N 6; N 19; N 129] = [].
Proof. simpl. reflexivity. Qed.

Fixpoint partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  match l with
  | [] => ([], [])
  | x :: y => if test x
              then match partition test y with
                   | (l1, l2) => (x :: l1, l2)
                   end
              else match partition test y with
                   | (l1, l2) => (l1, x :: l2)
                   end
  end.

Example test_partition1: partition oddb [N 1; N 2; N 3; N 4; N 5] = ([N 1; N 3; N 5], [N 2; N 4]).
Proof. simpl. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [N 5; N 9; N 0] = ([], [N 5; N 9; N 0]).
Proof. simpl. reflexivity. Qed.


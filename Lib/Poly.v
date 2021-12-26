From MyCoq.Lib Require Export Nat.


Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
Arguments nil {X}.
Arguments cons {X} _ _.


Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat x count')
  end.

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


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


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


Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).
Arguments pair {X} {Y} _ _.


Notation "( x , y )" := (pair x y).
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

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | nil => (nil, nil)
  | x :: y => match x with
              | (m, n) => match split y with
                              | (l1, l2) => (m :: l1, n :: l2)
                              end
              end
  end.


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

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | x :: y => Some x
  end.


Fixpoint filter {X : Type} (test: X -> bool) (l : list X) : (list X) :=
  match l with
  | [] => []
  | x :: y => if test x
              then x :: filter test y
              else filter test y
  end.


Fixpoint map {X Y: Type} (f : X -> Y) (l : list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Lemma map_app: forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  induction l1 as [| n1 l1'].
  - reflexivity.
  - simpl.
    intros l2.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Theorem map_rev: forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  induction l as [| n l'].
  - reflexivity.
  - simpl.
    rewrite map_app.
    simpl.
    rewrite <- IHl'.
    reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f : X -> list Y) (l : list X) : (list Y) :=
  match l with
  | [] => []
  | x :: y => (f x) ++ flat_map f y
  end.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.


Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  (* 需要一个起始元素 *)
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l O.

Theorem fold_length_correct: forall X (l : list X),
  fold_length l = length l.
Proof.
  induction l as [| n l'].
  - reflexivity.
  - simpl.
    rewrite <- IHl'.
    reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l : list X) : list Y :=
  fold (fun x y => (f x) :: y) l [].

Theorem fold_map_correct: forall (X Y : Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  induction l as [| n l'].
  - reflexivity.
  - simpl.
    rewrite <- IHl'.
    (* reflexivity 化简力度比 simpl 更强 *)
    reflexivity.
Qed.


Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z :=
  f (x, y).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).

Theorem uncurry_curry: forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  reflexivity.
Qed.

Theorem curry_uncurry: forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z.
  intros f.
  intros [x y].
  reflexivity.
Qed.

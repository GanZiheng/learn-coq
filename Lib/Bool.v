Inductive bool : Type :=
  | true
  | false.


Definition negb (b : bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b_1 : bool) (b_2 : bool) : bool := 
  match b_1 with
  | true => b_2
  | false => false
  end.

Definition orb (b_1 : bool) (b_2 : bool) : bool := 
  match b_1 with
  | true => true
  | false => b_2
  end.

Notation "~ x" := (negb x) (at level 75, right associativity).

Notation "x && y" := (andb x y) (at level 40, left associativity).

Notation "x || y" := (orb x y) (at level 50, left associativity).

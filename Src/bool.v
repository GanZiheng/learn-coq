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

Compute negb true.
Compute andb true false.

Example test_orb1: orb true false = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: orb false false = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: orb false true = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: orb true true = true.
Proof. simpl. reflexivity. Qed.

(* Notation "! x" := (negb x). *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Compute true && false.

Definition andb3 (b_1 : bool) (b_2 : bool) (b_3 : bool) : bool := 
  andb b_1 (andb b_2 b_3).

Example test_andb31: andb3 true true true = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: andb3 false true true = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: andb3 true false true = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: andb3 true true false = false.
Proof. simpl. reflexivity. Qed.

Check andb3.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary _ => false
  end.

Compute monochrome (primary blue).

Inductive nat : Type :=
  | O
  | S (n : nat).

Check S.

Inductive bit : Type :=
  | B_0
  | B_1.

Inductive nybble : Type :=
  | bits (b_0 b_1 b_2 b_3 : bit).

Check bits B_0 B_0 B_0 B_0.

Definition all_zero (bits : nybble) : bool := 
  match bits with
  | bits B_0 B_0 B_0 B_0 => true
  | bits _ _ _ _ => false
  end.

Compute all_zero (bits B_0 B_0 B_0 B_0).
Compute all_zero (bits B_0 B_0 B_0 B_1).

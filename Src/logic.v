From MyCoq.Lib Require Export Nat.
From MyCoq.Lib Require Export Poly.

Check 3 = 3.
Check forall n m : nat, n + m = m + n.

Definition plus_claim : Prop := N 2 + N 2 = N 4.

Theorem plus_claim_is_true: plus_claim.
Proof.
  unfold plus_claim.
  reflexivity.
Qed.

Definition is_three (n : nat) : Prop :=
  n = N 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj: injective S.
Proof.
  unfold injective.
  intros x y H.
  injection H as H'.
  apply H'.
Qed.

Locate eq.
Check @eq.


(* 逻辑联结词 *)
Example and_example: (N 3 + N 4 = N 7) /\ (N 2 * N 2 = N 4).
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro: forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B H1 H2.
  split.
  - apply H1.
  - apply H2.
Qed.

Example and_exercise:
  forall n m : nat, n + m = O -> n = O /\ m = O.
Proof.
  intros n m H.
  assert (H1: n = O).
  {
    destruct n as [| n'].
    - reflexivity.
    - discriminate H.
  }
  assert (H2: m = O).
  {
    destruct m as [| m'].
    - reflexivity.
    - rewrite plus_comm in H.
      discriminate H.
  }
  split.
  - apply H1.
  - apply H2.
Qed.

Lemma and_example2:
  forall n m : nat, n = O /\ m = O -> n + m = O.
Proof.
  intros n m H.
  destruct H as [Hn Hm] eqn : HE.
  rewrite Hn.
  rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2':
  forall n m : nat, n = O /\ m = O -> n + m = O.
Proof.
  intros n m [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3:
  forall n m : nat, n + m = O -> n * m = O.
Proof.
  intros n m H.
  assert (H': n = O /\ m = O).
  {
    apply and_exercise.
    apply H. 
  }
  destruct H' as [Hn Hm].
  rewrite Hn.
  reflexivity.
Qed.

Lemma proj1: forall P Q : Prop, P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.
Qed.

Lemma proj2: forall P Q : Prop, P /\ Q -> Q.
Proof.
  intros P Q HPQ.
  destruct HPQ as [_ HQ].
  apply HQ.
Qed.

Theorem and_commut: forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

Theorem and_assoc: forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split.
    + apply HP.
    + apply HQ.
  - apply HR.
Qed.

Lemma eq_mult_O:
  forall n m : nat, n = O \/ m = O -> n * m = O.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn.
    reflexivity.
  - rewrite Hm.
    rewrite -> mult_n_O.
    reflexivity.
Qed.

Lemma or_intro_l: forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Module MyNot.
Definition not (P : Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.
End MyNot.

Theorem ex_falso_quodlibet: forall P : Prop,
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not: forall P : Prop,
  ~ P -> (forall Q : Prop, P -> Q).
Proof.
  intros P HNP.
  unfold not in HNP.
  intros Q HP.
  apply HNP in HP.
  destruct HP.
Qed.

Notation "x <> y" := (~ (x = y)).

Theorem zero_not_one: O <> N 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False:
  ~ False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.

Theorem contradiction_implies_anything: forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros P Q [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  destruct HP.
Qed.

Theorem double_neg: forall P : Prop,
  P -> ~ ~ P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.

Theorem contrapositive: forall (P Q : Prop),
  (P -> Q) -> (~ Q -> ~P).
Proof.
  intros P Q H HNQ.
  unfold not in HNQ.
  unfold not.
  intros HP.
  apply H in HP.
  apply HNQ in HP.
  apply HP.
Qed.

Theorem not_both_true_and_false: forall P : Prop,
  ~ (P /\ ~ P).
Proof.
  intros P.
  unfold not.
  intros [HP HNP].
  apply HNP in HP.
  apply HP.
Qed.

Theorem not_true_is_false: forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn : HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false': forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H.
    reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Check I.

Lemma True_is_true: True.
Proof.
  apply I.
Qed.

Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.

Theorem iff_sym: forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - (* -> *) 
    apply HBA.
  - (* <- *)
    apply HAB.
Qed.

Lemma not_true_iff_false: forall b,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  - (* -> *) 
    apply not_true_is_false.
  - (* <- *)
    intros H.
    rewrite H.
    intros H'.
    discriminate H'.
Qed.

Theorem or_distributes_over_and: forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [H1 | H2].
    + split.
      * left.
        apply H1.
      * left.
        apply H1.
    + destruct H2 as [H21 H22].
      split.
      * right.
        apply H21.
      * right.
        apply H22.
  - intros [H1 H2].
    destruct H1 as [H11 | H12].
    + left.
      apply H11.
    + destruct H2 as [H21 | H22].
      * left.
        apply H21.
      * right.
        split.
        -- apply H12.
        -- apply H22.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mult_eq_O: forall n m, n * m = O -> n = O \/ m = O.
Proof.
  intros n m H.
  destruct n as [| n'].
  - left.
    reflexivity.
  - destruct m as [| m'].
    + right.
      reflexivity.
    + discriminate H.
Qed.

Lemma mult_O: forall n m, n * m = O <-> n = O \/ m = O.
Proof.
  split.
  - apply mult_eq_O.
  - apply eq_mult_O.
Qed.

Lemma or_assoc:
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H | [H | H]].
    + left.
      left.
      apply H.
    + left.
      right.
      apply H.
    + right.
      apply H.
  - intros [[H | H] | H].
    + left.
      apply H.
    + right.
      left.
      apply H.
    + right.
      right.
      apply H.
Qed.

Lemma mult_O_3:
  forall n m p, n * m * p = O <-> n = O \/ m = O \/ p = O.
Proof.
  intros n m p.
  rewrite mult_O.
  rewrite mult_O.
  rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example:
  forall n m : nat, n * m = O -> n = O \/ m = O.
Proof.
  intros n m H.
  apply mult_O.
  apply H.
Qed.

Definition even x := exists n : nat, x = double n.

Lemma four_is_even: even (N 4).
Proof.
  unfold even.
  exists (N 2).
  reflexivity.
Qed.

Theorem exists_example_2: forall n,
  (exists m, n = (N 4) + m) ->
  (exists o, n = (N 2) + o).
Proof.
  intros n [m Hm].
  exists ((N 2) + m).
  apply Hm.
Qed.

Theorem dist_not_exists: forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> not (exists x, not (P x)).
Proof.
  intros X P.
  intros H1 H2.
  destruct H2 as [x H2'].
  unfold not in H2'.
  apply H2'.
  apply H1.
Qed.

Theorem dist_exists_or: forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [H1 | H2]].
    + left.
      exists x. 
      apply H1.
    + right.
      exists x.
      apply H2.
  - intros [[x H1] | [x H2]].
    + exists x.
      left.
      apply H1.
    + exists x.
      right.
      apply H2.
Qed.

(*
Generic Typeclass for equality, plus some instances.

Authors:  Adam Petz, ampetz@ku.edu
          Will Thomas, 30wthomas@ku.edu
 *)

 Require Import Setoid.

Class EqClass (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true <-> x = y }.

Theorem EqClass_impl_DecEq: forall (A : Type) `{H : EqClass A},
    forall (x y : A), {x = y} + {x <> y}.
Proof.
  intros.
  destruct H.
  destruct (eqb0 x y) eqn:E.
  - left; eapply eqb_leibniz0; eauto.
  - right; erewrite <- eqb_leibniz0; intros HC; congruence.
Qed.

Theorem eqb_refl : forall {A : Type} `{EqClass A} a,
  eqb a a = true.
Proof.
  intros;
  erewrite eqb_leibniz; eauto.
Qed.

Theorem eqb_symm_true : forall {A : Type} `{EqClass A} a1 a2,
  eqb a1 a2 = true <->
  eqb a2 a1 = true.
Proof.
  intros; repeat erewrite eqb_leibniz; intuition.
Qed.

Theorem eqb_symm : forall {A : Type} `{EqClass A} a1 a2,
  eqb a1 a2 = eqb a2 a1.
Proof.
  intros.
  destruct (eqb a1 a2) eqn:E1, (eqb a2 a1) eqn:E2; eauto;
  erewrite eqb_leibniz in *; subst;
  erewrite eqb_refl in *; congruence.
Qed.

Theorem eqb_transitive : forall {A : Type} `{EqClass A} a1 a2 a3,
  eqb a1 a2 = true ->
  eqb a2 a3 = true ->
  eqb a1 a3 = true.
Proof.
  intros; repeat erewrite eqb_leibniz in *; subst; eauto.
Qed.

Fixpoint general_list_eq_class_eqb {A : Type} `{H : EqClass A} (l1 l2 : list A) : bool :=
  match l1, l2 with
  | nil, nil => true
  | cons h1 t1, cons h2 t2 => andb (eqb h1 h2) (general_list_eq_class_eqb t1 t2)
  | _, _ => false
  end.

Theorem general_list_eqb_leibniz : forall {A : Type} `{H : EqClass A},
  forall (a1 a2 : list A), general_list_eq_class_eqb a1 a2 = true <-> a1 = a2.
Proof.
  induction a1; destruct a2; split; intros; simpl in *; eauto; try congruence.
  - unfold andb in H0. destruct (eqb a a0) eqn:E.
    * rewrite eqb_leibniz in E; subst. rewrite IHa1 in H0. subst; eauto.
    * congruence.
  - inversion H0; subst.
    unfold andb. destruct (eqb a0 a0) eqn:E.
    * eapply IHa1. eauto.
    * pose proof (eqb_leibniz a0 a0). intuition. congruence.
Qed.

Global Instance EqClass_extends_to_list (A : Type) `{H : EqClass A} : EqClass (list A) := {
  eqb := general_list_eq_class_eqb ;
  eqb_leibniz := general_list_eqb_leibniz
}.

Lemma nat_eqb_eq : forall n1 n2 : nat,
  Nat.eqb n1 n2 = true <-> n1 = n2.
Proof.
  induction n1; destruct n2; 
  split; intros; eauto;
  inversion H.
  - rewrite IHn1 in H1. subst; eauto.
  - subst. simpl. rewrite IHn1; eauto.
Qed.

Global Instance nat_EqClass : EqClass nat :=
  { eqb:= Nat.eqb;
    eqb_leibniz := nat_eqb_eq }.

Definition eqbPair{A B:Type}`{H:EqClass A}`{H':EqClass B} (p1:A*B) (p2:A*B) : bool :=
  match (p1,p2) with
  | ((a1,b1), (a2,b2)) => andb (eqb a1 a2) (eqb b1 b2)
  end.

Lemma beq_pair_true{A B:Type}`{H:EqClass A}`{H':EqClass B} : forall (p1 p2:(A*B)),
    eqbPair p1 p2 = true -> p1 = p2.
Proof.
  intros.
  unfold eqbPair in *.
  destruct p1, p2.
  assert (a = a0).
  {
    assert (eqb a a0 = true).
    {
      destruct (eqb a a0); eauto.
    }
    eapply eqb_leibniz; eauto.
  }
  
  assert (b = b0).
  {
    assert (eqb b b0 = true).
    {
      destruct (eqb b b0); eauto; subst;
      unfold andb in H0; destruct (eqb a0 a0); congruence.
    }
    eapply eqb_leibniz; eauto.
  }
  subst.
  reflexivity.
Defined.

Require Import StructTactics.

Lemma pair_eqb_eq{A B:Type}`{H:EqClass A}`{H':EqClass B} : forall (p1 p2:(A*B)),
    eqbPair p1 p2 = true <-> p1 = p2.
Proof.
  intros.
  split.
  -
    eapply beq_pair_true; eauto.
  -
    intros.
    subst.
    unfold eqbPair.
    break_let.
    repeat rewrite eqb_refl in *.
    trivial.
Qed.

Global Instance pair_EqClass{A B:Type}`{H:EqClass A}`{H':EqClass B} : EqClass (A*B) :=
  { eqb:= eqbPair;
    eqb_leibniz := pair_eqb_eq }.
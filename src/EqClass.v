(*
Generic Typeclass for equality, plus some instances.

Author:  Adam Petz, ampetz@ku.edu
 *)

Require Import StructTactics.

Require Import Coq.Arith.EqNat.

Class EqClass (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, eqb x y = true <-> x = y }.

Theorem EqClass_impl_DecEq: forall (A : Type) `{H : EqClass A},
    forall (x y : A), {x = y} + {x <> y}.
Proof.
  intros.
  destruct (eqb x y) eqn:E.
  - left; eapply eqb_leibniz; eauto.
  - right; erewrite <- eqb_leibniz; intros HC; congruence.
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
  - eapply Bool.andb_true_iff in H0. destruct H0.
    erewrite eqb_leibniz in H0; subst. 
    rewrite IHa1 in H1; subst; eauto.
  - inv H0.
    eapply Bool.andb_true_iff; split; eauto.
    * eapply eqb_leibniz; eauto.
    * erewrite IHa1; eauto.
Qed.

Global Instance EqClass_extends_to_list (A : Type) `{H : EqClass A} : EqClass (list A) := {
  eqb := general_list_eq_class_eqb ;
  eqb_leibniz := general_list_eqb_leibniz
}.

Global Instance nat_EqClass : EqClass nat :=
  { eqb:= PeanoNat.Nat.eqb;
    eqb_leibniz := PeanoNat.Nat.eqb_eq }.

Definition eqbPair{A B:Type}`{H:EqClass A}`{H':EqClass B} (p1:A*B) (p2:A*B) : bool :=
  match (p1,p2) with
  | ((a1,b1), (a2,b2)) => andb (eqb a1 a2) (eqb b1 b2)
  end.

Lemma beq_pair_true{A B:Type}`{H:EqClass A}`{H':EqClass B} : forall (p1 p2:(A*B)),
    eqbPair p1 p2 = true -> p1 = p2.
Proof.
  intros.
  unfold eqbPair in *.
  repeat break_let.
  assert (a = a0).
  {
    assert (eqb a a0 = true).
    {
      destruct (eqb a a0); try solve_by_inversion.
    }
    eapply eqb_leibniz; eauto.
  }
  
  assert (b = b0).
  {
        assert (eqb b b0 = true).
        {
          destruct (eqb b b0); try reflexivity.
          cbv in *.
          repeat break_let.
          break_if; solve_by_inversion.     
        }
    eapply eqb_leibniz; eauto.
  }
  subst.
  reflexivity.
Defined.

                                                             

(*
#[global]
Instance pair_EqClass{A B:Type}`{H:EqClass A}`{H':EqClass B} : EqClass (A*B) :=
  { eqb:= eqbPair;
    eqb_leibniz := beq_pair_true }.
*)

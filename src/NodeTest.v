Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.ProofIrrelevance Coq.Program.Equality.

Require Import List.
Import ListNotations.

Require Import Lia.

(*
Require Import StructTact.StructTactics.
*)

Set Nested Proofs Allowed.

Section NodeTest.

  Variable num_Nodes : nat.

  Definition Name := {n:nat | n < num_Nodes}.

  Definition Name_eq_dec : forall a b : Name, {a = b} + {a <> b}.
    intros.
    unfold Name in *.
    destruct a; destruct b.
    destruct (Nat.eq_dec x x0).
    -
      subst.
      assert (l = l0).
      {
        eapply proof_irrelevance.
      }
      subst.
      left.
      reflexivity.
    -
      subst.
      right.
      unfold not.
      intros.
      inversion H.
      congruence.
  Defined.

  (* NOTE:  I want the equivalent of:  [0; 1; ... (num_Nodes - 1)], a.k.a. (seq 0 num_Nodes), 
     but instead a list of dependent pairs, where each element has an accompanying
     proof saying: " this element is less than num_Nodes". *)

  Definition list_Nodes_dep : {l:list Name | map (@proj1_sig _ _) l = (seq 0 num_Nodes)}.
  Admitted.

  Definition Nodes : list Name := proj1_sig list_Nodes_dep.

  Lemma sig_map :
      forall A (x0:A) (l:list A) (P:A -> Prop) (x: list {n:A | P n}) (pf:P x0),
        map (proj1_sig (P:=P)) x = l ->
        In x0 l ->
        In (exist P x0 pf) x.
  Proof.
    intros.
    rewrite <- H in H0.
    rewrite in_map_iff in H0.
    destruct H0.
    destruct x1.
    destruct H0.

    unfold proj1_sig in H0.
    subst.
    assert (pf = p).
    {
      eapply proof_irrelevance.
    }
    subst.
    eassumption.
  Defined.
  
  Lemma sig_nodup :
      forall A (*(x0:A)*) (l:list A) (P:A -> Prop) (x: list {n:A | P n}) (*(pf:P x0)*),
        map (proj1_sig (P:=P)) x = l ->
        NoDup l ->
        NoDup x.
  Proof.
    intros.
    rewrite <- H in H0.
    eapply NoDup_map_inv.
    eassumption.
  Defined.

  Lemma seq_fact: forall n n',
      n < n' ->
      In n (seq 0 n').
  Proof.   
  Admitted.
  
  Theorem In_n_Nodes :
    forall n : Name, In n Nodes.
  Proof using.
    intros.
    unfold Nodes, Name in *.
    destruct list_Nodes_dep.
    simpl.
    unfold Name in *.

    destruct n as [x0 pf].

    assert (In x0 (seq 0 num_Nodes)).
    {
      eapply seq_fact; eauto.
    }
    eapply sig_map; eauto.
  Defined.

  Theorem nodup :
    NoDup Nodes.
  Proof using.
    unfold Nodes, Name in *.
    destruct list_Nodes_dep.
    simpl.
    unfold Name in *.

    assert (NoDup (seq 0 num_Nodes)).
    {
      eapply seq_NoDup.
    }
    eapply sig_nodup; eauto.
  Defined.



End NodeTest.

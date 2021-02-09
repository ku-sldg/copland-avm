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

  Variable num_Servers : nat.

  Definition Server_index := {n:nat | n < num_Servers}.

  Definition Name := Server_index.

  
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

  (* TODO:  I want the equivalent of:  [0; 1; ... (num_Servers - 1)], 
     but instead a list of dependent pairs, each with an element and a
     proof saying that "element is less than num_Servers". *)



(*
  Definition sumbool_wrap_nat (n:nat):  (n < num_Servers) + (n >= num_Servers).
  Admitted.

  Definition wrap_nat (n:nat): (n < num_Servers).
  Admitted.
*)

  Definition list_Servers_dep : {l:list Name | map (@proj1_sig _ _) l = (seq 0 num_Servers)}.
  Admitted.

  Definition list_Servers : list Name := proj1_sig list_Servers_dep.


  Definition Nodes := list_Servers.

  Lemma seq_fact: forall n n',
    S n < S n' ->
    In (S n) (seq 1 n').
  Proof.
  Admitted.
  

  Theorem In_n_Nodes :
    forall n : Name, In n Nodes.
  Proof using.
    intros.
    unfold Nodes, list_Servers.
    destruct list_Servers_dep.
    unfold Name in *.
    unfold Server_index in *. 
    simpl.
    destruct n.

    assert (In x0 (seq 0 num_Servers)).
    {
      destruct num_Servers;
        destruct x0;
        try lia.
      +
        simpl.
        eauto.
      +
        simpl.
        right.
        eapply seq_fact; eauto.
    }
  (* NOW WHAT?? *)
  Abort.

  Theorem nodup :
    NoDup Nodes.
  Proof using.
    unfold Nodes, list_Servers.
    destruct list_Servers_dep.
    simpl.
    unfold Name in *.
    unfold Server_index in *.

    assert (NoDup (seq 0 num_Servers)).
    {
      eapply seq_NoDup.
    }
  (* NOW WHAT?? *)
  Abort.



End NodeTest.

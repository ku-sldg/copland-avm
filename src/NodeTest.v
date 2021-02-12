Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.ProofIrrelevance Coq.Program.Equality Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Require Import Lia.

(*

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype.

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype.

Definition f (n : {n | 2 < n}) : nat :=
  val n - 3.

Definition finv (m : nat) : {n | 2 < n} :=
  Sub (3 + m) erefl.

Lemma fK : cancel f finv.
Proof.
move=> [n Pn] /=; apply/val_inj=> /=.
by rewrite /f /= addnC subnK.
Qed.

Lemma finvK : cancel finv f.
Proof.
by move=> n; rewrite /finv /f /= addnC addnK.
Qed.

*)

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

  (*
  Lemma list_Nodes_dep' : exists l: list Name, map (@proj1_sig _ _) l = (seq 0 num_Nodes).
  Proof.
  Admitted.
   *)
  

  (*
 Lemma in_seq len start n :
    In n (seq start len) <-> start <= n < start+len.

   *)

  Definition list_proj_In_seq: {l:list {n:nat | In n (seq 0 num_Nodes)} | length l = num_Nodes /\ NoDup l }.
  Admitted.

  Definition list_proj2_In_seq: list {n:nat | In n (seq 0 num_Nodes)} :=
    @proj1_sig _ _ list_proj_In_seq.

  Check list_proj2_In_seq.

  Check @proj2_sig.

  Check map.

  Definition asdff : list (nat -> Prop).
    refine (map (fun x => @proj2_sig _ _ x) list_proj2_In_seq).

  Definition list_Nodes_dep_fun{n:nat} (p: In n (seq 0 num_Nodes)) : {m:nat | m < num_Nodes}.
    unfold Name.
    assert (0 <= n < 0 + num_Nodes).
    {
      eapply in_seq; eauto.
    }
    assert (n < num_Nodes) by lia.
    econstructor.
    eassumption.
  Defined.

  (*
Inductive sig (A:Type) (P:A -> Prop) : Type :=
    exist : forall x:A, P x -> sig P.
   *)
  
    
  

  (* NOTE:  I want the equivalent of:  [0; 1; ... (num_Nodes - 1)], a.k.a. (seq 0 num_Nodes), 
     but instead a list of dependent pairs, where each element has an accompanying
     proof saying: " this element is less than num_Nodes". *)

  Definition list_Nodes_dep : {l:list Name | map (@proj1_sig _ _) l = (seq 0 num_Nodes)}.
    unfold Name in *.
    refine (exist _ (map (list_Nodes_dep_fun) (_)) _).

    Check in_map_iff.

    
    exact (exist (map (list_Nodes_dep_fun _) (seq 0 num_Nodes))).










    
    assert (exists l : list Name, map (proj1_sig (P:=fun n : nat => n < num_Nodes)) l = seq 0 num_Nodes).
    assert (exists n:nat, n = 0). admit.
    destruct H as [af afa].
    
    eapply list_Nodes_dep'.
    unfold Name in *.
    simpl in *.

    destruct H.

    
    econstructor.
    
    
    dependent destruction H.
    destruct_conjs.
    destruct H.
    
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

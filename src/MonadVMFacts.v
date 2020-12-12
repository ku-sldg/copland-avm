(*
Lemmas and LTAC scripts to leverage facts about the CVM Monad.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term ConcreteEvidence MonadVM Maps.
Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Require Import StructTactics.

Ltac vmsts :=
  simpl in *;
  repeat
    match goal with
    | [H: cvm_st |- _] => destruct H
    end.

Ltac amsts :=
  repeat match goal with
         | H:cvm_st |- _ => destruct H
         end.
(*
Lemma get_store_at_determ : forall e0' e e' e2 e2' tr tr' tr2 tr2' p p' p2 p2'
                              store1 store1' store2' n,
    get_store_at n {| st_ev := e; st_trace := tr; st_pl := p; st_store := store1 |} =
    (Some e0', {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := store1' |}) ->

    get_store_at n  {| st_ev := e2; st_trace := tr2; st_pl := p2; st_store := store1 |} =
    (None, {| st_ev := e2'; st_trace := tr2'; st_pl := p2'; st_store := store2' |}) ->
    False.
Proof.
  intros.
  unfold get_store_at in *. monad_unfold.
  repeat break_match.
  invc H. inv Heqp0. invc H0.
  invc H. (* invc Heqp1. *)
Defined.

Lemma get_store_at_facts : forall st_ev st_ev0 (st_trace:list Ev) (st_trace0:list Ev)
                              st_trace st_trace0 st_ev' p p' o o' n,
    get_store_at n {| st_ev := st_ev; st_trace := st_trace; st_pl := p; st_store := o |} = 
    (Some st_ev', {| st_ev := st_ev0; st_trace := st_trace0; st_pl := p'; st_store := o' |})  ->
    st_ev = st_ev0 /\ st_trace = st_trace0 /\ p = p' /\ o = o' /\ bound_to o n st_ev'.
Proof.
  intros.
  unfold get_store_at in *.
  monad_unfold.
  repeat break_match.
  invc Heqo1. invc Heqp0. invc H.
  repeat split; eauto.
  invc H. invc Heqp0.
Defined.

Ltac do_get_store_at_facts :=
  vmsts;
  match goal with
  | [H: get_store_at _ _ = (Some _,_) |- _ ] =>
    apply get_store_at_facts in H
  end; destruct_conjs.

Lemma bound_and_deterministic : forall (s:ev_store) n (e1 e2:EvidenceC),
    Maps_Class.bound_to s n e1 ->
    Maps_Class.bound_to s n e2 ->
    e1 = e2.
Proof.
  intros.
  inv H. inv H0.
  congruence.
Defined.

Ltac do_bd :=
  match goal with
  | [ H: Maps_Class.bound_to ?s ?n ?e1,
         G: Maps_Class.bound_to ?s ?n ?e2  |- _ ] =>
    assert (e1 = e2)
      by (eapply bound_and_deterministic; eauto);
    clear H; clear G
  end.

Lemma get_store_at_facts_fail : forall st_ev st_ev0 (st_trace:list Ev) (st_trace0:list Ev)
                             st_trace st_trace0 p p' o o' n,
    get_store_at n {| st_ev := st_ev; st_trace := st_trace; st_pl := p; st_store := o |} = 
    (None, {| st_ev := st_ev0; st_trace := st_trace0; st_pl := p'; st_store := o' |}) ->
    st_ev = st_ev0 /\ st_trace = st_trace0 /\ p = p' /\ o = o'.
Proof.
  intros.
  unfold get_store_at in *.
  monad_unfold.
  repeat break_match.
  invc Heqp0. invc H.
  invc H. invc Heqp0.
  repeat split; eauto.
Defined.

Ltac do_get_store_at_facts_fail :=
  vmsts;
  match goal with
  | [H: get_store_at _ _ = (None,_) |- _ ] =>
    apply get_store_at_facts_fail in H
  end; destruct_conjs.

Ltac get_store_some :=
  vmsts;
    match goal with                                        
    | [ H: get_store_at ?n _ = (Some _,_),
           G: get_store_at ?n _ = (Some,_) |- _ ] =>
      (*idtac "matched get_store_some" ; *)
      rewrite get_store_at_facts in H;
      rewrite get_store_at_facts in G                                 
    end; destruct_conjs.


Ltac bogus :=
  vmsts;
  repeat
    match goal with                                        
    | [H: (Some _, _) =
          (None, _) |- _ ] => inv H
                                 
    | [ H: get_store_at ?n _ = (Some _,_),
           G: get_store_at ?n _ = (None,_) |- _ ] =>
      (*idtac "matched get_store_at_determ" ; *)
      elimtype False; eapply get_store_at_determ;
      [apply H | apply G]
    | [ H: get_store_at ?n _ = (Some _,_),
           G: get_store_at ?n _ = (Some _,_) |- _ ] =>
      (*idtac "matched get_store_at_bogus" ; *)
      apply get_store_at_facts in H; eauto;
      apply get_store_at_facts in G; eauto;
      repeat do_bd;
      destruct_conjs;
      subst;
      bogus; reflexivity
    end.

Ltac get_store_at_bogus :=
  vmsts;
 (* repeat *)
    match goal with                                        
    | [ H: get_store_at ?n _ = (Some _,_),
           G: get_store_at ?n _ = (Some _,_) |- _ ] =>
      (*idtac "matched get_store_at_bogus" ; *)
      apply get_store_at_facts in H; eauto;
      apply get_store_at_facts in G; eauto;
      repeat do_bd;
      destruct_conjs;
      subst;
      bogus; reflexivity
    end.
*)

Ltac pairs :=
  simpl in *;
  vmsts;
  repeat
    match goal with
    | [H: (Some _, _) =
          (Some _, _) |- _ ] => invc H; monad_unfold
                                                          
    | [H: {| st_ev := _; st_trace := _; st_pl := _; st_store := _ |} =
          {| st_ev := _; st_trace := _; st_pl := _; st_store := _ |} |- _ ] =>
      invc H; monad_unfold
    end; destruct_conjs; monad_unfold.

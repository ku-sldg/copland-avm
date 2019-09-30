Require Import Term MyStack MonadVM.
Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.

Lemma pop_stackm_fail : forall e e' s s' tr tr',
    (None, {| st_ev := e'; st_stack := s'; st_trace := tr' |}) =
    pop_stackm {| st_ev := e; st_stack := s; st_trace := tr |} ->
    e = e' /\ s = s' /\ tr = tr'.
Proof.
    intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as p.
  destruct p. destruct p.
  inv H.
  monad_unfold. inv H.
  split; eauto.
Defined.

Lemma push_stackm_succeeds : forall e st st',
    push_stackm e st = (None, st') -> False.
Proof.
  intros.
  destruct st. destruct st'.
  
  unfold push_stackm in *. monad_unfold.
  inv H.
Defined.

Lemma double_pop : forall e e' e0 e1 st_ev st_ev0 st_stack st_stack0
                     st_trace st_trace' st_trace0 st_trace0' s,
    (Some e1,
     {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |}) =
    pop_stackm {| st_ev := e'; st_stack := s; st_trace := st_trace' |} ->
    
    (Some e0,
     {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0 |}) =
    pop_stackm {| st_ev := e; st_stack := s; st_trace := st_trace0' |} ->

    (st_stack0 = st_stack /\ e0 = e1).
Proof.
  intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as p.
  destruct p. destruct p.
  invc H. invc H0.
  split; eauto.
  monad_unfold.
  inv H.
Defined.

Lemma double_pop_none :
  forall (e e' st_ev st_ev0 : EvidenceC)
    (st_stack st_stack0 : ev_stack)
    (st_trace st_trace' st_trace0 st_trace0' : list Ev) 
    (s : ev_stack),
    (None,
     {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |}) =
    pop_stackm {| st_ev := e'; st_stack := s; st_trace := st_trace' |} ->
    (None,
     {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0 |}) =
    pop_stackm {| st_ev := e; st_stack := s; st_trace := st_trace0' |} ->
    st_stack0 = st_stack.
Proof.
Admitted.

Ltac vmsts :=
  simpl in *;
  repeat
    match goal with
    | [H: vm_st |- _] => destruct H
    end.

Ltac do_double_pop :=
  vmsts;
  match goal with
  | [H: (Some ?e1,
         {| st_ev := ?st_ev; st_stack := ?st_stack; st_trace := ?st_trace |}) =
        pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?trx |},
        G:  (Some ?e0,
             {| st_ev := ?st_ev0; st_stack := ?st_stack0; st_trace := ?st_trace0 |}) =
            pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?m |} |- _ ] =>
    assert (st_stack0 = st_stack /\ e0 = e1) by (eapply double_pop; eauto)
  end; destruct_conjs.

Lemma pop_stackm_facts : forall e' e1 st_ev st_stack
                     st_trace st_trace' s,
    (Some e1,
     {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |}) =
    pop_stackm {| st_ev := e'; st_stack := s; st_trace := st_trace' |} ->
    (e' = st_ev /\ st_trace' = st_trace /\ (exists e, s = e::st_stack)).
Proof.
Admitted.

Lemma pop_stackm_facts_none : forall e' st_ev st_stack
                     st_trace st_trace' s,
    (None,
     {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |}) =
    pop_stackm {| st_ev := e'; st_stack := s; st_trace := st_trace' |} ->
    (e' = st_ev /\ st_trace' = st_trace /\ s = [] /\ st_stack = []).
Proof.
Admitted.

Lemma push_stackm_pure : forall o e st_ev st_ev0 st_stack st_stack0 st_trace st_trace0,
    (o, {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0 |}) =
    push_stackm e
                {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |} ->
    st_trace0 = st_trace /\ st_ev = st_ev0.
Proof.
  intros.
  destruct o.
  - simpl in *.
    monad_unfold.
    unfold push_stackm in *. monad_unfold. inv H.
    split; eauto.
  - unfold push_stackm in *. monad_unfold. inv H.
Defined.

Lemma pop_stackm_pure : forall o st_ev st_ev0 st_stack st_stack0 st_trace st_trace0,
    (o, {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0 |}) =
    pop_stackm {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |} ->
    st_trace0 = st_trace /\ st_ev = st_ev0.
Proof.
  intros.
    destruct o.
  - unfold pop_stackm in *. monad_unfold.
    remember (pop_stack EvidenceC st_stack) as p.
    destruct p. destruct p. invc H.
    split; eauto.
    monad_unfold. inv H.
  - unfold pop_stackm in *. monad_unfold.
    remember (pop_stack EvidenceC st_stack) as p.
    destruct p. destruct p. invc H. monad_unfold.
    inv H.
    split; eauto.
Defined.

Lemma pop_stackm_determ_none : forall e0' e e' e2 e2' s s' s2' tr tr' tr2 tr2',
    (Some e0', {| st_ev := e'; st_stack := s'; st_trace := tr' |}) =
    pop_stackm {| st_ev := e; st_stack := s; st_trace := tr |} ->
    (None, {| st_ev := e2'; st_stack := s2'; st_trace := tr2' |}) =
    pop_stackm {| st_ev := e2; st_stack := s; st_trace := tr2 |} ->
    False.
Proof.
    intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as p.
  destruct p. destruct p.
  invc H. invc H0.
  monad_unfold. inv H.
Defined.

Lemma push_stackm_facts : forall st_ev st_ev0 (st_trace:list Ev) (st_trace0:list Ev)
                            st_stack st_stack0 st_trace st_trace0 H0 u,
    (Some u, {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0 |}) =
    push_stackm H0 {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |} ->
    st_ev = st_ev0 /\ st_trace = st_trace0 /\ st_stack0 = H0 :: st_stack.
Proof.
Admitted.


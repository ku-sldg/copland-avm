Require Import Term ConcreteEvidence MyStack MonadVM.
Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Require Import StructTactics.

Lemma pop_stackm_fail_facts : forall e e' s s' p p'
                     tr tr' o o',
    (None,
     {| st_ev := e'; st_stack := s'; st_trace := tr'; st_pl := p'; st_store := o |}) =
    pop_stackm {| st_ev := e; st_stack := s; st_trace := tr; st_pl := p; st_store := o' |} ->
    (e = e' /\ tr = tr' /\ p = p' /\ s = [] /\ s' = [] /\ o = o').
Proof.
  intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as pp.
  destruct pp. destruct p0.
  inv H.
  monad_unfold. inv H.
  split; eauto.
  split; eauto.
  invc H.
  destruct s.
  eauto.
  unfold pop_stack in *. inv Heqpp.
Defined.

Ltac do_pop_stackm_fail:=
  match goal with
  | [H: (None,_) =
    pop_stackm _ |- _ ] =>
    (*idtac "invoking do_pop_stackm_fail"; *)
    apply pop_stackm_fail_facts in H
  end; destruct_conjs.

Lemma pop_stackm_facts : forall e' e1 st_ev st_stack
                     st_trace st_trace' s p p' o o',
    (Some e1,
     {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace; st_pl := p'; st_store := o' |}) =
    pop_stackm {| st_ev := e'; st_stack := s; st_trace := st_trace'; st_pl := p; st_store := o |} ->
    (e' = st_ev /\ st_trace' = st_trace /\ p = p' /\ o = o' /\ (exists e, s = e::st_stack)).
Proof.
  intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as pp.
  destruct pp. destruct p0.
  invc H.
  repeat split; eauto.
  exists e.
  destruct s; unfold pop_stack in *; congruence.
  simpl in *. inv H.
Defined.

Ltac do_pop_stackm_facts :=
  match goal with
  | [H: (Some ?e1, _) =
        pop_stackm _ |- _ ] =>
    (*assert (e = e' /\ tr = tr' /\ exists evd, s = evd::s')
      by (eapply pop_stackm_facts; eauto); clear H *)
    apply pop_stackm_facts in H
  end; destruct_conjs.

Lemma push_stackm_succeeds : forall e st st',
    push_stackm e st = (None, st') -> False.
Proof.
  intros.
  destruct st. destruct st'.
  unfold push_stackm in *. monad_unfold.
  inv H.
Defined.

Lemma double_pop : forall e e' e0 e1 p p' p2 p2' st_ev st_ev0 st_stack st_stack0
                     st_trace st_trace' st_trace0 st_trace0' s o o' o2 o2',
    (Some e1,
     {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace; st_pl := p'; st_store := o' |}) =
    pop_stackm {| st_ev := e'; st_stack := s; st_trace := st_trace'; st_pl := p; st_store := o |} ->
    
    (Some e0,
     {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0; st_pl := p2'; st_store := o2' |}) =
    pop_stackm {| st_ev := e; st_stack := s; st_trace := st_trace0'; st_pl := p2; st_store := o2 |} ->

    (st_stack0 = st_stack /\ e0 = e1).
Proof.
  intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as pp.
  destruct pp. destruct p0.
  invc H. invc H0.
  split; eauto.
  monad_unfold.
  inv H.
Defined.

Ltac do_double_pop :=
  match goal with
  | [H: (Some ?e1,
         {| st_ev := _; st_stack := ?st_stack; st_trace := _; st_pl := _; st_store := _ |}) =
        pop_stackm {| st_ev := _; st_stack := ?s; st_trace := _; st_pl := _; st_store := _ |},
        G:  (Some ?e0,
             {| st_ev := _; st_stack := ?st_stack0; st_trace := _; st_pl := _; st_store := _ |}) =
            pop_stackm {| st_ev := _; st_stack := ?s; st_trace := _; st_pl := _; st_store := _ |} |- _ ] =>
    assert (st_stack0 = st_stack /\ e0 = e1) by (eapply double_pop; eauto)
  end; destruct_conjs.

Lemma double_pop_none :
  forall (e e' st_ev st_ev0 : EvidenceC)
    (st_stack st_stack0 : ev_stack)
    (st_trace st_trace' st_trace0 st_trace0' : list Ev) 
    (s : ev_stack) p p' p2 p2' o o' o2 o2',
    (None,
     {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace; st_pl := p'; st_store := o' |}) =
    pop_stackm {| st_ev := e'; st_stack := s; st_trace := st_trace'; st_pl := p; st_store := o |} ->
    (None,
     {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0; st_pl := p2'; st_store := o2' |}) =
    pop_stackm {| st_ev := e; st_stack := s; st_trace := st_trace0'; st_pl := p2; st_store := o2 |} ->
    st_stack0 = st_stack.
Proof.
  intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as pp.
  destruct pp. destruct p0.
  invc H. invc H0.
  monad_unfold. invc H.
  auto.
Defined.

Ltac do_double_pop_none :=
  match goal with
  | [H: (None,
         {| st_ev := ?st_ev; st_stack := ?st_stack; st_trace := ?st_trace; st_pl := _; st_store := _ |}) =
        pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?trx; st_pl := _; st_store := _ |},
        G:  (None,
             {| st_ev := ?st_ev0; st_stack := ?st_stack0; st_trace := ?st_trace0; st_pl := _; st_store := _ |}) =
            pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?m; st_pl := _; st_store := _ |} |- _ ] =>
    assert (st_stack0 = st_stack) by (eapply double_pop_none; eauto)
  end; destruct_conjs.

Ltac vmsts :=
  simpl in *;
  repeat
    match goal with
    | [H: vm_st |- _] => destruct H
    end.

Ltac try_pop_all :=
  vmsts;
  try do_double_pop;
  try do_double_pop_none;
  destruct_conjs;
  subst; 
  eauto.

Lemma push_stackm_pure : forall o e st_ev st_ev0 st_stack st_stack0 st_trace st_trace0 p p' store store',
    (o, {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0; st_pl := p'; st_store := store' |}) =
    push_stackm e
                {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace; st_pl := p; st_store := store |} ->
    st_trace0 = st_trace /\ st_ev = st_ev0 /\ store = store'.
Proof.
  intros.
  destruct o.
  - simpl in *.
    monad_unfold.
    unfold push_stackm in *. monad_unfold. inv H.
    split; eauto.
  - unfold push_stackm in *. monad_unfold. inv H.
Defined.

Lemma pop_stackm_pure : forall o st_ev st_ev0 st_stack st_stack0 st_trace st_trace0 p p' store store',
    (o, {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0; st_pl := p'; st_store := store' |}) =
    pop_stackm {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace; st_pl := p; st_store := store |} ->
    st_trace0 = st_trace /\ st_ev = st_ev0 /\ store = store'.
Proof.
  intros.
    destruct o.
  - unfold pop_stackm in *. monad_unfold.
    remember (pop_stack EvidenceC st_stack) as pp.
    destruct pp. destruct p0. invc H.
    split; eauto.
    monad_unfold. inv H.
  - unfold pop_stackm in *. monad_unfold.
    remember (pop_stack EvidenceC st_stack) as pp.
    destruct pp. destruct p0. invc H. monad_unfold.
    inv H.
    split; eauto.
Defined.

Lemma pop_stackm_determ_none : forall e0' e e' e2 e2' s s' s2' tr tr' tr2 tr2' p p' p2 p2'
                                 store1 store1' store2 store2',
    (Some e0', {| st_ev := e'; st_stack := s'; st_trace := tr'; st_pl := p'; st_store := store1' |}) =
    pop_stackm {| st_ev := e; st_stack := s; st_trace := tr; st_pl := p; st_store := store1 |} ->
    (None, {| st_ev := e2'; st_stack := s2'; st_trace := tr2'; st_pl := p2'; st_store := store2' |}) =
    pop_stackm {| st_ev := e2; st_stack := s; st_trace := tr2; st_pl := p2; st_store := store2 |} ->
    False.
Proof.
  intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as pp.
  destruct pp. destruct p0.
  invc H. invc H0.
  monad_unfold. inv H.
Defined.

Lemma get_store_at_determ : forall e0' e e' e2 e2' s s' s2 s2' tr tr' tr2 tr2' p p' p2 p2'
                              store1 store1' store2' n,
    get_store_at n {| st_ev := e; st_stack := s; st_trace := tr; st_pl := p; st_store := store1 |} =
    (Some e0', {| st_ev := e'; st_stack := s'; st_trace := tr'; st_pl := p'; st_store := store1' |})
    (*pop_stackm {| st_ev := e; st_stack := s; st_trace := tr; st_pl := p; st_store := store1 |}*) ->

    get_store_at n  {| st_ev := e2; st_stack := s2; st_trace := tr2; st_pl := p2; st_store := store1 |} =
    (None, {| st_ev := e2'; st_stack := s2'; st_trace := tr2'; st_pl := p2'; st_store := store2' |})
    (*pop_stackm {| st_ev := e2; st_stack := s; st_trace := tr2; st_pl := p2; st_store := store2 |}*) ->
    False.
Proof.
  intros.
  unfold get_store_at in *. monad_unfold.
  repeat break_match.
  invc H. inv Heqp0. invc H0.
  invc H. (* invc Heqp1. *)
Defined.

Lemma push_stackm_facts : forall st_ev st_ev0 (st_trace:list Ev) (st_trace0:list Ev)
                            st_stack st_stack0 st_trace st_trace0 H0 u p p' o o',
    (Some u, {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0; st_pl := p'; st_store := o' |}) =
    push_stackm H0 {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace; st_pl := p; st_store := o |} ->
    st_ev = st_ev0 /\ st_trace = st_trace0 /\ st_stack0 = H0 :: st_stack /\ o = o'.
Proof.
  intros.
  unfold push_stackm in *.
  monad_unfold.
  inv H.
  split; eauto.
Defined.

Require Import Maps.

Lemma get_store_at_facts : forall st_ev st_ev0 (st_trace:list Ev) (st_trace0:list Ev)
                             st_stack st_stack0 st_trace st_trace0 st_ev' p p' o o' n,
    get_store_at n {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace; st_pl := p; st_store := o |} = 
    (Some st_ev', {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0; st_pl := p'; st_store := o' |})  ->
    st_ev = st_ev0 /\ st_trace = st_trace0 /\ st_stack = st_stack0 /\ p = p' /\ o = o' /\ bound_to o n st_ev'.
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
    Maps.bound_to s n e1 ->
    Maps.bound_to s n e2 ->
    e1 = e2.
Proof.
  intros.
  inv H. inv H0.
  congruence.
Defined.

Ltac do_bd :=
  match goal with
  | [ H: Maps.bound_to ?s ?n ?e1,
         G: Maps.bound_to ?s ?n ?e2  |- _ ] =>
    assert (e1 = e2)
      by (eapply bound_and_deterministic; eauto);
    clear H; clear G
  end.

Lemma get_store_at_facts_fail : forall st_ev st_ev0 (st_trace:list Ev) (st_trace0:list Ev)
                             st_stack st_stack0 st_trace st_trace0 p p' o o' n,
    get_store_at n {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace; st_pl := p; st_store := o |} = 
    (None, {| st_ev := st_ev0; st_stack := st_stack0; st_trace := st_trace0; st_pl := p'; st_store := o' |}) (*=
    push_stackm H0 {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace; st_pl := p; st_store := o |}*) ->
    st_ev = st_ev0 /\ st_trace = st_trace0 /\ st_stack = st_stack0 /\ p = p' /\ o = o'.
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



(* 
 snd
          (let
           '(b, s'') :=
            match
              pop_stackm {| st_ev := H3; st_stack := H4; st_trace := x0 |}
            with
            | (Some v, s') =>
                (Some tt,
                {|
                st_ev := ssc v H3;
                st_stack := MonadVM.st_stack s';
                st_trace := MonadVM.st_trace s' ++
                            [join (Init.Nat.pred (snd r))] |})
            | (None, s') => (None, s')
            end in (b, s'')) =
        {| st_ev := e'; st_stack := s'; st_trace := x0 ++ H7 |}
      *)

(*
run_vm (instr_compiler t2 ++ [ajoins (Init.Nat.pred (snd r))])
         (snd
            (let
             '(b, s'') :=
              match
                pop_stackm {| st_ev := H0; st_stack := H; st_trace := x |}
              with
              | (Some v, s') =>
                  let
                  '(b, s'') :=
                   match push_stackm H0 s' with
                   | (Some _, s'0) =>
                       (Some tt,
                       {|
                       st_ev := v;
                       st_stack := st_stack s'0;
                       st_trace := st_trace s'0 |})
                   | (None, s'0) => (None, s'0)
                   end in (b, s'')
              | (None, s') => (None, s')
              end in (b, s''))) =
       {| st_ev := e'; st_stack := s0; st_trace := x ++ H2 |}
 *)

(*
Ltac desp :=
  match goal with
  | [ H: context
           [pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?m |}] |- _] =>
    remember (pop_stackm {| st_ev := e; st_stack := s; st_trace := m |}) as p; 
    destruct p as [o];
    destruct o
(*  | [ H: context
           [match pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?m |} with | _ => (let _ := _ in _) |(None,_) => _ end] |- _ ] =>
    remember (pop_stackm {| st_ev := e; st_stack := s; st_trace := m |}) as p; 
    destruct p as [o];
    destruct o *)
  | |- context [match pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?m |} with | _ => _ end] =>
    remember (pop_stackm {| st_ev := e; st_stack := s; st_trace := m |}) as p; 
    destruct p as [o];
    destruct o        
           
  | [ H: context
           [match push_stackm _ {| st_ev := ?e; st_stack := ?s; st_trace := ?m |} with |_ => _ end] |- _ ] =>
    remember (pop_stackm {| st_ev := e; st_stack := s; st_trace := m |}) as p; 
    destruct p as [o];
    destruct o
  | |- context
        [match push_stackm _ {| st_ev := ?e; st_stack := ?s; st_trace := ?m |} with |_ => _ end] =>
    remember (pop_stackm {| st_ev := e; st_stack := s; st_trace := m |}) as p; 
    destruct p as [o];
    destruct o
  end; monad_unfold; vmsts.
*)

Ltac desp :=
  (*expand_let_pairs; *)
  match goal with
  | [ H: context
           [match pop_stackm ?v with |_ => _ end] |- _ ] =>
    remember (pop_stackm v) as ppp; 
    destruct ppp as [oo]; (* TODO: use "fresh" tactic here and throughout *)
    destruct oo
  | |- context [match pop_stackm ?v with | _ => _ end] =>
    remember (pop_stackm v) as ppp; 
    destruct ppp as [oo];
    destruct oo       
           
  | [ H: context
           [match push_stackm ?e' ?v with |_ => _ end] |- _ ] =>
    remember (push_stackm e' v) as ppp; 
    destruct ppp as [oo];
    destruct oo
  | |- context
        [match push_stackm ?e' ?v with |_ => _ end] =>
    remember (push_stackm e' v) as ppp; 
    destruct ppp as [oo];
    destruct oo
  end; (*monad_unfold; *) vmsts.

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
                                 
    | [H: (None, _) = push_stackm _ _ |- _] =>
      elimtype (False); eapply push_stackm_succeeds; eauto; contradiction

    | [ H: (Some _,
            _) =
           pop_stackm _,
           G:  (None,
                _) =
               pop_stackm _ |- _ ] =>
      elimtype False; eapply pop_stackm_determ_none; eauto; contradiction
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

Ltac pairs :=
  simpl in *;
  vmsts;
  repeat
    match goal with
    | [H: (Some _, _) =
          (Some _, _) |- _ ] => invc H; monad_unfold
                                                          
    | [H: (None, {| st_ev := _; st_stack := _; st_trace := _; st_pl := _; st_store := _|}) =
          pop_stackm {| st_ev := _; st_stack := _; st_trace := _; st_pl := _; st_store := _|} |- _ ] =>
      edestruct (pop_stackm_fail_facts); eauto; clear H
                                                      (* TODO: simplify record match ^ *)
    | [H: {| st_ev := _; st_stack:= _; st_trace := _; st_pl := _; st_store := _ |} =
          {| st_ev := _; st_stack:= _; st_trace := _; st_pl := _; st_store := _ |} |- _ ] =>
      invc H; monad_unfold
                                                           
    end; destruct_conjs; monad_unfold.


(*
Ltac do_pop_stackm_fail:=
  match goal with
  | [H: (None,
     {| st_ev := ?e'; st_stack := ?s'; st_trace := ?tr' |}) =
    pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?tr |} |- _ ] =>
    idtac "invoking do_pop_stackm_fail";
    assert (e = e' /\ tr = tr' /\ s = [] /\ s' = []) by
        (eapply pop_stackm_fail_facts; eauto); clear H
  end; destruct_conjs.
*)

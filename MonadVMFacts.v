Require Import Term MyStack MonadVM.
Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.

Lemma pop_stackm_fail_facts : forall e e' s s'
                     tr tr',
    (None,
     {| st_ev := e'; st_stack := s'; st_trace := tr' |}) =
    pop_stackm {| st_ev := e; st_stack := s; st_trace := tr |} ->
    (e = e' /\ tr = tr' /\ s = [] /\ s' = []).
Proof.
  intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as p.
  destruct p. destruct p.
  inv H.
  monad_unfold. inv H.
  split; eauto.
  split; eauto.
  invc H.
  destruct s.
  eauto.
  unfold pop_stack in *. inv Heqp.
Defined.

Ltac do_pop_stackm_fail:=
  match goal with
  | [H: (None,_) =
    pop_stackm _ |- _ ] =>
    idtac "invoking do_pop_stackm_fail";
    apply pop_stackm_fail_facts in H
  end; destruct_conjs.

Lemma pop_stackm_facts : forall e' e1 st_ev st_stack
                     st_trace st_trace' s,
    (Some e1,
     {| st_ev := st_ev; st_stack := st_stack; st_trace := st_trace |}) =
    pop_stackm {| st_ev := e'; st_stack := s; st_trace := st_trace' |} ->
    (e' = st_ev /\ st_trace' = st_trace /\ (exists e, s = e::st_stack)).
Proof.
  intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as p.
  destruct p. destruct p.
  invc H.
  split; eauto.
  split; eauto.
  exists e.
  destruct s; unfold pop_stack in *; congruence.
  simpl in *. inv H.
Defined.

Ltac do_pop_stackm_facts :=
  match goal with
  | [H: (Some ?e1,
         {| st_ev := ?e'; st_stack := ?s'; st_trace := ?tr' |}) =
        pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?tr |}  |- _ ] =>
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

Ltac do_double_pop :=
  match goal with
  | [H: (Some ?e1,
         {| st_ev := ?st_ev; st_stack := ?st_stack; st_trace := ?st_trace |}) =
        pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?trx |},
        G:  (Some ?e0,
             {| st_ev := ?st_ev0; st_stack := ?st_stack0; st_trace := ?st_trace0 |}) =
            pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?m |} |- _ ] =>
    assert (st_stack0 = st_stack /\ e0 = e1) by (eapply double_pop; eauto)
  end; destruct_conjs.

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
  intros.
  unfold pop_stackm in *. monad_unfold.
  remember (pop_stack EvidenceC s) as p.
  destruct p. destruct p.
  invc H. invc H0.
  monad_unfold. invc H.
  auto.
Defined.

Ltac do_double_pop_none :=
  match goal with
  | [H: (None,
         {| st_ev := ?st_ev; st_stack := ?st_stack; st_trace := ?st_trace |}) =
        pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?trx |},
        G:  (None,
             {| st_ev := ?st_ev0; st_stack := ?st_stack0; st_trace := ?st_trace0 |}) =
            pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?m |} |- _ ] =>
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
  intros.
  unfold push_stackm in *.
  monad_unfold.
  inv H.
  split; eauto.
Defined.

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
           [match pop_stackm {| st_ev := ?e; st_stack := ?s; st_trace := ?m |} (*with _ end*) with |_ => _ end] |- _ ] =>
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

Ltac bogus :=
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
    end.

Ltac pairs :=
  simpl in *;
  vmsts;
  repeat
    match goal with
    | [H: (Some _, _) =
          (Some _, _) |- _ ] => invc H; monad_unfold
                                                          
    | [H: (None, {| st_ev := _; st_stack := _; st_trace := _|}) =
          pop_stackm {| st_ev := _; st_stack := _; st_trace := _|} |- _ ] =>
      edestruct (pop_stackm_fail_facts); eauto; clear H
                                                           
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

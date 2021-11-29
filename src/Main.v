(* Main theorems *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** This chapter contains the proof that traces generated from the
    small-step semantics are compatible with the related event system.
    *)

Require Import Preamble More_lists Term_Defs Term LTS Event_system Term_system Trace Defs.

Require Import StructTactics.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Lia.

Set Nested Proofs Allowed.
(** The traces associated with a state. *)

Inductive traceS: St -> list Ev -> Prop :=
| tstop: forall p e,
    traceS (stop p e) []
| tconf: forall t tr p e,
    trace t p e tr ->
    traceS (conf t p e) tr
| trem: forall st tr j p,
    traceS st tr ->
    traceS (rem j p st)
           (tr ++
               [(rpy (pred j) p (pl st) (seval st))])
| tls: forall st tr1 t tr2,
    traceS st tr1 ->
    trace t (pl st) (seval st) tr2 ->
    traceS (ls st t) (tr1 ++ tr2)
| tbsl: forall st tr1 t p e tr2 j,
    traceS st tr1 ->
    trace t p e tr2 ->
    traceS (bsl j st t p e)
           (tr1 ++ tr2 ++
                [(join (pred j) p )])
| tbsr: forall st tr j e,
    traceS st tr ->
    traceS (bsr j e st)
           (tr ++ [(join (pred j) (pl st) )])
 | tbp: forall st1 tr1 st2 tr2 tr3 j,
    traceS st1 tr1 -> traceS st2 tr2 ->
    shuffle tr1 tr2 tr3 ->
    traceS (bp j st1 st2)
           (tr3 ++ [(join (pred j) (pl st2))]).
Hint Constructors traceS : core.

Fixpoint esizeS s:=
  match s with
  | stop _ _ => 0
  | conf t _ _ => esize t
  | rem _ _ st => 1 + esizeS st
  | ls st t => esizeS st + esize t
  | bsl _ st t _ _ => 1 + esizeS st + esize t
  | bsr _ _ st => 1 + esizeS st
  | bp _ st1 st2 => 1 + esizeS st1 + esizeS st2
  end.

Ltac inv_trace :=
  match goal with
  | H:trace (?C _) _ _ _ |- _ => inv H
  end.

Lemma esize_tr:
  forall t p e tr,
    trace t p e tr -> length tr = esize t.
Proof.
  induction t; intros; inv_trace; simpl;
    autorewrite with list; simpl; auto;
      try (
          try find_apply_lem_hyp shuffle_length;
          repeat find_apply_hyp_hyp;
          lia).
Defined.

Ltac inv_traceS :=
  match goal with
  | H:traceS (?C _) _ |- _ => inv H
  end.

Lemma esizeS_tr:
  forall st tr,
    traceS st tr -> length tr = esizeS st.
Proof.
  induction st; intros;
    inv_traceS; simpl; auto;
      try (destruct a; find_apply_lem_hyp esize_tr; tauto);
      repeat find_apply_lem_hyp esize_tr;
      repeat (rewrite app_length; simpl);
      repeat find_apply_hyp_hyp;
      repeat find_apply_lem_hyp shuffle_length;
      try lia.
Defined.

Ltac jkjk'e :=
  match goal with
  | [H: _ = ?X |-  context[?X] ] => erewrite <- H
  end.

(*
Lemma aeval_ev_determ: forall a p e e',
    aeval a p e = aeval a p e' ->
    e = e'.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    destruct a;
      cbn in *; auto;
        try solve_by_inversion.
    destruct a.
    try solve_by_inversion.
  -
    cbn in *; auto.
    eauto.
  -
    cbn in *; auto.
    eauto.
  -
    cbn in *; auto.
    invc H.
    destruct s.
    destruct s; destruct s0.
    +
      eauto.
    +
      eauto.
    +
      eauto.
    +
      ff.
Abort.  (* TODO:  can this be proven with assumptions about term split? *)
 *)



(*   
    assert ((splitEv_T_l s e) = (splitEv_T_l s e')) by eauto.
    destruct s; destruct s; destruct s0; eauto.
    destruct s; eauto.
  -
    cbn in *; auto.
    invc H.
    assert ((splitEv_T_l s e) = (splitEv_T_l s e')) by eauto.
    destruct s; eauto.
Defined.
*)

Lemma step_silent_tr:
  forall st st' tr,
    step st None st' ->
    traceS st' tr ->
    traceS st tr.
Proof.
  induction st; intros; inv H; inv H0.
  - constructor.
    constructor; auto.
    solve_by_inversion.
  -
    find_copy_apply_lem_hyp step_pl_eq.
    find_copy_apply_lem_hyp step_seval.
    jkjk'e.
    jkjk'e.
    eauto.
  -
    constructor.
    eauto.

    find_apply_lem_hyp step_pl_eq.
    find_copy_apply_lem_hyp step_seval.
    
    cbn in *.
    invc H.
    repeat find_rewrite.
    assert (traceS st tr1) by eauto.
    assert (seval st = seval st1).
    {
      eapply step_seval.
      eassumption.
    }
    repeat find_rewrite.
    eauto.
  -
    erewrite <- app_nil_l.
    constructor; auto.
  -
    eauto.
  -
    erewrite <- app_nil_l.
    apply tbsl; auto; simpl; auto.
    invc H.
    invc H5.
    eauto.
  -
    find_eapply_hyp_hyp; eauto.
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.
    jkjk'e; auto.
  -
    eauto.    
  -
    find_copy_apply_hyp_hyp; eauto.
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.
    jkjk'e; auto.
    eapply tbp; eauto.
Qed.

Lemma step_evt_tr:
  forall st st' ev tr,
    step st (Some ev) st' ->
    traceS st' tr ->
    traceS st (ev::tr).
Proof.
  induction st; intros; inv H; inv H0.
  - constructor.
    constructor.
  - constructor. apply tatt. simpl.
    solve_by_inversion.
  - constructor. apply tbseq; auto.
    solve_by_inversion.  
  - constructor.
    eapply tbpar; eauto; solve_by_inversion.
  -
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.
    jkjk'e.
    jkjk'e.
    rewrite app_comm_cons; eauto. 
  - rewrite <- app_nil_l; auto.
    apply trem; auto.
  -
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.
    rewrite app_comm_cons; auto.
    apply tls;
      try jkjk;
      eauto.
    repeat find_rewrite.
    eauto.    
  -
    find_copy_apply_lem_hyp step_seval.
    rewrite app_comm_cons; auto.
    eauto.
  -
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.
    rewrite app_comm_cons.
    jkjk'e.
    eauto.   
  - rewrite <- app_nil_l; constructor; auto.
  -
    find_copy_apply_lem_hyp step_seval.
    rewrite app_comm_cons.
    find_eapply_lem_hyp shuffle_left.
    eapply tbp; eauto.
  -
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.
    rewrite app_comm_cons.
    find_eapply_lem_hyp shuffle_right.
    jkjk'e.
    eapply tbp; eauto.
  -
    rewrite <- app_nil_l; auto.
    eapply tbp; eauto.
Qed.

Lemma nlstar_trace_helper:
  forall e p n st0 tr st1,
    step st0 e st1 ->
    nlstar n st1 tr (stop p (seval st0)) ->
    nlstar n st1 tr (stop p (seval st1)).
Proof.
  intros e p n st0 tr st1 H G.
  apply step_seval in H.
  rewrite <- H.
  auto.
Qed.

Lemma nlstar_trace:
  forall n p st tr,
    nlstar n st tr (stop p (seval st)) ->
    traceS st tr.
Proof.
  induction n; intros; inv H; auto;
    eapply nlstar_trace_helper in H2; eauto;
      apply IHn in H2; auto.
  - eapply step_evt_tr; eauto.
  - eapply step_silent_tr; eauto.
Qed.

(** A trace of the LTS is a trace of the big-step semantics. *)

Lemma lstar_trace:
  forall t p e tr,
    well_formed_r_annt t ->
    lstar (conf t p e) tr (stop p (aeval t p e)) ->
    trace t p e tr.
Proof.
  intros.
  apply lstar_nlstar in H0.
  destruct H0.
  apply nlstar_trace in H0.
  inv H0; auto.
Qed.

(** The key theorem. *)

Theorem ordered:
  forall t p e tr ev0 ev1,
    well_formed_r_annt t ->
    lstar (conf t p e) tr (stop p (aeval t p e)) ->
    prec (ev_sys t p e) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  apply lstar_trace in H0; auto.
  apply trace_order with (t:=t)(p:=p)(e:=e); auto.
Qed.

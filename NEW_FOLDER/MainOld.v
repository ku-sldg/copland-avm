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

Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Coq.micromega.Lia.
Require Import Preamble More_lists Term LTS Event_system Term_system Trace.

(** The traces associated with a state. *)

Inductive traceS: St -> list Ev -> Prop :=
| tstop: forall p e,
    traceS (stop p e) []
| tconf: forall t tr p e,
    trace t p tr ->
    traceS (conf t p e) tr
| trem: forall st tr j p,
    traceS st tr ->
    traceS (rem j p st)
           (tr ++
               [(rpy (pred j) p (pl st))])
| tls: forall st tr1 t tr2,
    traceS st tr1 ->
    trace t (pl st) tr2 ->
    traceS (ls st t) (tr1 ++ tr2)
| tbsl: forall st tr1 t p e tr2 j,
    traceS st tr1 ->
    trace t p tr2 ->
    traceS (bsl j st t p e)
           (tr1 ++ tr2 ++
                [(join (pred j) p)])
| tbsr: forall st tr j e,
    traceS st tr ->
    traceS (bsr j e st)
           (tr ++ [(join (pred j) (pl st))])
| tbp: forall st1 tr1 st2 tr2 tr3 j,
    traceS st1 tr1 -> traceS st2 tr2 ->
    shuffle tr1 tr2 tr3 ->
    traceS (bp j st1 st2)
           (tr3 ++ [(join (pred j) (pl st2))]).
Hint Constructors traceS.

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

Lemma esize_tr:
  forall t p tr,
    trace t p tr -> length tr = esize t.
Proof.
  induction t; intros; inv H; simpl;
    autorewrite with list; simpl; auto.
  apply IHt in H5. lia.
  apply IHt1 in H5.
  apply IHt2 in H6. lia.
  apply IHt1 in H6.
  apply IHt2 in H7. lia.
  apply shuffle_length in H8.
  apply IHt1 in H6.
  apply IHt2 in H7.
  lia.
Qed.

Lemma esizeS_tr:
  forall st tr,
    traceS st tr -> length tr = esizeS st.
Proof.
  induction st; intros; inv H; simpl; auto.
  - destruct a; apply esize_tr in H4; simpl in *; auto.
  - rewrite app_length; simpl.
    apply IHst in H4. lia.
  - rewrite app_length; simpl.
    apply IHst in H2. apply esize_tr in H4.
    lia.
  - repeat (rewrite app_length; simpl).
    apply IHst in H6.
    apply esize_tr in H7. lia.
  - rewrite app_length; simpl.
    apply IHst in H4. lia.
  - rewrite app_length; simpl.
    apply IHst1 in H3.
    apply IHst2 in H5.
    apply shuffle_length in H6.
    lia.
Qed.

Lemma step_silent_tr:
  forall st st' tr,
    step st None st' ->
    traceS st' tr ->
    traceS st tr.
Proof.
  induction st; intros; inv H; inv H0.
  - constructor.
    constructor; auto.
    inv H2; auto.
  - pose proof H6 as G.
    pose proof H6 as G1.
    apply step_pl_eq in G; auto.
    apply step_seval in G1; auto.
    rewrite <- G.
    eapply IHst in H6; eauto.
  - constructor; auto.
    eapply IHst in H2; eauto.
    pose proof H5 as G.
    apply step_pl_eq in H5.
    rewrite H5; auto.
  - rewrite <- app_nil_l with (l:=tr).
    constructor; auto.
  - pose proof H8 as G.
    eapply IHst in H8; eauto.
  - rewrite <- app_nil_l with (l:=tr0).
    rewrite <- app_assoc.
    apply tbsl; auto. simpl; auto.
    inv H4; auto.
  - pose proof H6 as G.
    pose proof H6 as G1.
    eapply IHst in H6; eauto.
    apply step_seval in G.
    apply step_pl_eq in G1.
    rewrite <- G1; auto.
  - pose proof H6 as G.
    eapply IHst1 in H6; eauto.
  - pose proof H6 as G.
    pose proof H6 as G1.
    eapply IHst2 in H6; eauto.
    apply step_seval in G.
    apply step_pl_eq in G1.
    rewrite <- G1; auto.
    apply tbp with (tr1:=tr1)(tr2:=tr2); auto.
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
    inv H4; auto.
  - constructor. apply tbseq; auto.
    inv H6; auto.
  - constructor. eapply tbpar; eauto.
    inv H3; auto. inv H5; auto.
  - pose proof H6 as G.
    apply step_seval in G.
    pose proof H6 as G1.
    apply step_pl_eq in G1.
    eapply IHst in H6; eauto.
    rewrite <- G1.
    rewrite app_comm_cons; auto.
  - rewrite <- app_nil_l; auto.
    apply trem; auto.
  - pose proof H5 as G.
    apply step_seval in G.
    pose proof H5 as G1.
    apply step_pl_eq in G1.
    eapply IHst in H5; eauto.
    rewrite app_comm_cons.
    apply tls; auto.
    rewrite G1; auto.
  - pose proof H8 as G.
    apply step_seval in G.
    eapply IHst in H8; eauto.
    rewrite app_comm_cons; auto.
  - pose proof H6 as G.
    apply step_seval in G.
    pose proof H6 as G1.
    apply step_pl_eq in G1.
    eapply IHst in H6; eauto.
    rewrite app_comm_cons;
      rewrite <- G1; auto.
  - rewrite <- app_nil_l; constructor; auto.
  - pose proof H6 as G.
    apply step_seval in G.
    eapply IHst1 in H6; eauto.
    apply shuffle_left with (e:=ev) in H7.
    rewrite app_comm_cons;
      auto.
    apply tbp with (tr1:=(ev::tr1))(tr2:=tr2); auto.
  - pose proof H6 as G.
    apply step_seval in G.
    pose proof H6 as G1.
    apply step_pl_eq in G1.
    apply shuffle_right with (e:=ev) in H7.
    eapply IHst2 in H6; eauto.
    rewrite app_comm_cons;
      rewrite <- G1; auto.
    apply tbp with (tr1:=tr1)(tr2:=(ev::tr2)); auto.
  - rewrite <- app_nil_l; auto.
    apply tbp with (tr1:=[])(tr2:=[]); auto.
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
    well_formed t ->
    lstar (conf t p e) tr (stop p (aeval t p e)) ->
    trace t p tr.
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
    well_formed t ->
    lstar (conf t p e) tr (stop p (aeval t p e)) ->
    prec (ev_sys t p) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  apply lstar_trace in H0; auto.
  apply trace_order with (t:=t)(p:=p); auto.
Qed.

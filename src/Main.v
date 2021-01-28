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
Require Import Lia.
Require Import Preamble More_lists Term_Defs Term LTS Event_system Term_system Trace.

(** The traces associated with a state. *)

Inductive traceS: St -> list Ev -> Prop :=
| tstop: forall p e,
    traceS (stop p e) []
| tconf: forall t tr p e,
    trace t p tr ->
    traceS (conf t p e) tr
| trem: forall st tr j loc p,
    traceS st tr ->
    traceS (rem j loc p st)
           (tr ++
               [(rpy (pred j) loc p (pl st))])
| tls: forall st tr1 t tr2,
    traceS st tr1 ->
    trace t (pl st) tr2 ->
    traceS (ls st t) (tr1 ++ tr2)
| tbsl: forall st tr1 t p e tr2 j,
    traceS st tr1 ->
    trace t p tr2 ->
    traceS (bsl j st t p e)
           (tr1 ++ tr2 ++
                [(join (pred j) p )])
| tbsr: forall st tr j e,
    traceS st tr ->
    traceS (bsr j e st)
           (tr ++ [(join (pred j) (pl st) )])
 | tbp: forall st1 tr1 st2 tr2 tr3 j xi yi,
    traceS st1 tr1 -> traceS st2 tr2 ->
    shuffle tr1 tr2 tr3 ->
    traceS (bp j xi yi st1 st2)
           (tr3 ++ [(joinp (pred j) xi yi (pl st2))]).
Hint Constructors traceS : core.

Fixpoint esizeS s:=
  match s with
  | stop _ _ => 0
  | conf t _ _ => esize t
  | rem _ _ _ st => 1 + esizeS st
  | ls st t => esizeS st + esize t
  | bsl _ st t _ _ => 1 + esizeS st + esize t
  | bsr _ _ st => 1 + esizeS st
  | bp _ _ _ st1 st2 => 1 + esizeS st1 + esizeS st2
  end.


Ltac inv_trace :=
  match goal with
  | H:trace (?C _) _ _ |- _ => inv H
  end.

Require Import StructTactics.

Lemma esize_tr:
  forall t p tr,
    trace t p tr -> length tr = esize t.
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
(*
  - destruct a;
      find_apply_lem_hyp esize_tr; auto.
    (*


      apply esize_tr in H4; simpl in *; auto. *)
  - rewrite app_length; simpl.
    find_apply_hyp_hyp; lia.
    (*
    apply IHst in H5; lia. *)
  - rewrite app_length; simpl.
    find_apply_hyp_hyp.
    find_apply_lem_hyp esize_tr.
    lia.
    (*
    apply IHst in H2. apply esize_tr in H4.
    lia. *)
    
  - repeat (rewrite app_length; simpl).
    find_apply_hyp_hyp.
    find_apply_lem_hyp esize_tr.
    lia.
    (*
    apply IHst in H6.
    apply esize_tr in H7. lia. *)
  - rewrite app_length; simpl.
    find_apply_hyp_hyp.
    lia.
    (*
    find_apply_lem_hyp esize_tr.
    lia.
    apply IHst in H4. lia. *)
    
  - rewrite app_length; simpl.
    repeat find_apply_hyp_hyp.
    find_apply_lem_hyp shuffle_length.
    lia.
    (*
    apply IHst1 in H6.
    apply IHst2 in H7.
    apply shuffle_length in H8.
    lia. *)
Qed.
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
    (*
    inv H2; auto. *)
  -

    (*
    find_apply_lem_hyp step_pl_eq; auto.
    find_apply_lem_hyp step_seval; auto.
    
    rewrite <- H7.
    inv H.
    
    find_apply_hyp_hyp; eauto.
    Check step_seval.
    find_apply_lem_hyp step_seval; auto. *)

    find_copy_apply_lem_hyp step_pl_eq.
    find_copy_apply_lem_hyp step_seval.

    Require Import Defs.

    Ltac jkjk'e :=
      match goal with
      | [H: _ = ?X |-  context[?X] ] => erewrite <- H
      end.

    jkjk'e.

    (*
    


    pose proof H7 as G.
    pose proof H7 as G1.
    apply step_pl_eq in G; auto.
    apply step_seval in G1; auto.
    rewrite <- G. (*rewrite <- G1. *)
     *)

    eauto.

  -

    constructor; auto.
    eauto.

    find_apply_lem_hyp step_pl_eq.
    find_rewrite; auto.

    (*

    (*
    
    eapply IHst in H3; eauto. *)
    pose proof H6 as G.
    apply step_pl_eq in H3.
    rewrite H5; auto.
    (* apply step_seval in G.
    rewrite G; auto. *) *)
  -
    erewrite <- app_nil_l.
    constructor; auto.
    (*

    rewrite <- app_nil_l with (l:=tr).
    constructor; auto. *)
    
  -
    eauto.

    (*

    pose proof H8 as G.
    eapply IHst in H8; eauto.
    (*apply step_seval in G.
    rewrite <- G; auto. *) *)
  -
    erewrite <- app_nil_l.

    (*

    rewrite <- app_nil_l with (l:=tr0). *)
    (*
    rewrite app_assoc.
    
    rewrite <- app_assoc. *)
   
    apply tbsl; auto; simpl; auto;
    solve_by_inversion.
    (*
    inv H; auto. *)
  -
    find_eapply_hyp_hyp; eauto.

    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.
    (*
    

    pose proof H6 as G.
    pose proof H6 as G1.
    eapply IHst in H6; eauto.
    apply step_seval in G. 
    (*rewrite <- G; auto. *)
    apply step_pl_eq in G1.
     *)

    jkjk'e; auto.
    
    (*
    rewrite <- G1; auto. *)
    
  -
    eauto.

    (*

    pose proof H6 as G.
    eapply IHst1 in H6; eauto.
    (* apply step_seval in G.
    rewrite <- G; auto. 
    apply tbp with (tr1:=tr1)(tr2:=tr2); auto. *)
     *)
    
  -
    find_copy_apply_hyp_hyp; eauto.
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.
    jkjk'e; auto.
    eapply tbp; eauto.

    (*

    pose proof H8 as G.
    pose proof H8 as G1.
    eapply IHst2 in H8; eauto.
    apply step_seval in G.
    (* rewrite <- G; auto. *)
    apply step_pl_eq in G1.
    rewrite <- G1; auto.
    apply tbp with (tr1:=tr1)(tr2:=tr2); auto. *)
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
    (*
    inv H6; auto. *)
    
  - constructor. apply tbseq; auto.
    solve_by_inversion.
    (*
    inv H6; auto. *)
    
  - constructor. eapply tbpar; eauto; solve_by_inversion.
    
(*
    inv H6; auto. inv H7; auto. *)
  -
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.

    jkjk'e.
    rewrite app_comm_cons; eauto.

    (*

    find_eapply_hyp_hyp.

    pose proof H7 as G.
    apply step_seval in G.
    pose proof H7 as G1.
    apply step_pl_eq in G1.
    eapply IHst in H7; eauto.
    (* rewrite <- G. *) rewrite <- G1.
    rewrite app_comm_cons; auto. *)
  - rewrite <- app_nil_l; auto.
    apply trem; auto.
  -
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.

    (*

    pose proof H5 as G.
    apply step_seval in G.
    pose proof H5 as G1.
    apply step_pl_eq in G1. *)

    rewrite app_comm_cons; auto.

    apply tls;
      try jkjk;
      eauto.

    
(*
    
    eapply IHst in H3; eauto.

    (*

    
    eapply IHst in H5; eauto. *)
    rewrite app_comm_cons.
    apply tls; auto.
    jkjk; auto.
 *)
    

    (*
    (*rewrite G. *) rewrite G1; auto. *)
    
  -
    find_copy_apply_lem_hyp step_seval.

    rewrite app_comm_cons; auto.
    eauto.

    (*

   (*

    pose proof H8 as G.
    apply step_seval in G. *)
    eapply IHst in H8; eauto.
    (*rewrite <- G. *)
    rewrite app_comm_cons; auto. *)
  -

    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.

    rewrite app_comm_cons.
    jkjk'e.
    eauto.

    (*


    pose proof H6 as G.
    apply step_seval in G.
    pose proof H6 as G1.
    apply step_pl_eq in G1.
    eapply IHst in H6; eauto.
    rewrite app_comm_cons;
      (*rewrite <- G; *) rewrite <- G1; auto.
     *)
    
  - rewrite <- app_nil_l; constructor; auto.
    
  -
    find_copy_apply_lem_hyp step_seval.
    rewrite app_comm_cons.

    find_eapply_lem_hyp shuffle_left.

    eapply tbp; eauto.

    (*
    


    pose proof H8 as G.
    apply step_seval in G.
    eapply IHst1 in H8; eauto.
    apply shuffle_left with (e:=ev) in H9.
    rewrite app_comm_cons;
      (*rewrite <- G; *) auto.
    apply tbp with (tr1:=(ev::tr1))(tr2:=tr2); auto. *)
  -
    find_copy_apply_lem_hyp step_seval.
    find_copy_apply_lem_hyp step_pl_eq.


    (*
    find_eapply_lem_hyp shuffle_right.
    rewrite app_comm_cons.

    eapply tbp.
     *)
    


(*
    pose proof H8 as G.
    apply step_seval in G.
    pose proof H8 as G1.
    apply step_pl_eq in G1.
 *)
    rewrite app_comm_cons.

    find_eapply_lem_hyp shuffle_right.

    (*
    
    apply shuffle_right with (e:=ev) in H10. 
    
   
    eapply IHst2 in H9; eauto. *)

    jkjk'e.
    eapply tbp; eauto.

    (*

    (*
    
    rewrite app_comm_cons;
      (*rewrite <- G; *) rewrite <- G1; auto. *)
    apply tbp with (tr1:=tr1)(tr2:=(ev::tr2)); auto.
     *)
    
  - rewrite <- app_nil_l; auto.
    eapply tbp; eauto.
    (*
    apply tbp with (tr1:=[])(tr2:=[]); auto. *)
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
    well_formed_r t ->
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
    well_formed_r t ->
    lstar (conf t p e) tr (stop p (aeval t p e)) ->
    prec (ev_sys t p) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  apply lstar_trace in H0; auto.
  apply trace_order with (t:=t)(p:=p); auto.
Qed.

(* Traces and their relation to event systems *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** Traces and their relation to event systems. *)

Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import Lia.
Require Import Preamble More_lists Term Event_system Term_system.

(** * Shuffles

    A trace is a list of events.  [shuffle] merges two traces as is
    done by parallel execution.  The order of events in the traces to
    be merged does not change, but all other interleavings are
    allowed.  *)

Inductive shuffle: list Ev -> list Ev -> list Ev -> Prop :=
| shuffle_nil_left: forall es, shuffle [] es es
| shuffle_nil_right: forall es, shuffle es [] es
| shuffle_left:
    forall e es0 es1 es2,
      shuffle es0 es1 es2 ->
      shuffle (e :: es0) es1 (e :: es2)
| shuffle_right:
    forall e es0 es1 es2,
      shuffle es0 es1 es2 ->
      shuffle es0 (e :: es1) (e :: es2).
Hint Constructors shuffle : core.

Lemma shuffle_length:
  forall es0 es1 es2,
    shuffle es0 es1 es2 ->
    length es0 + length es1 = length es2.
Proof.
  intros.
  induction H; simpl; auto; lia.
Qed.

Lemma shuffle_in_left:
  forall e es0 es1 es2,
    shuffle es0 es1 es2 ->
    In e es0 ->
    In e es2.
Proof.
  intros.
  induction H; auto.
  - inv H0; tauto.
  - destruct H0.
    + subst; simpl; auto.
    + simpl; auto.
  - apply IHshuffle in H0.
    simpl; auto.
Qed.

Lemma shuffle_in_right:
  forall e es0 es1 es2,
    shuffle es0 es1 es2 ->
    In e es1 ->
    In e es2.
Proof.
  intros.
  induction H; auto.
  - inv H0; tauto.
  - apply IHshuffle in H0.
    simpl; auto.
  - destruct H0.
    subst; simpl; auto.
    apply IHshuffle in H0.
    simpl; auto.
Qed.

Lemma shuffle_in:
  forall e es0 es1 es2,
    shuffle es0 es1 es2 ->
    In e es2 <-> In e es0 \/ In e es1.
Proof.
  split; intros.
  - induction H; simpl; auto;
    simpl in H0; destruct H0; auto;
      apply IHshuffle in H0; tauto.
  - destruct H0; auto.
    + eapply shuffle_in_left in H; eauto.
    + eapply shuffle_in_right in H; eauto.
Qed.

Lemma shuffle_in_skipn_left:
  forall i e es0 es1 es2,
    shuffle es0 es1 es2 ->
    In e (skipn i es0) ->
    In e (skipn i es2).
Proof.
  intros.
  revert H0.
  revert e.
  revert i.
  induction H; intros; auto.
  - rewrite skipn_nil in H0.
    inv H0.
  - destruct i.
    + simpl in *; auto; destruct H0; auto.
      specialize IHshuffle with (i:=0).
      simpl in IHshuffle; auto.
    + simpl in *; auto.
  - apply IHshuffle in H0.
    apply in_skipn_cons; auto.
Qed.

Lemma shuffle_in_skipn_right:
  forall i e es0 es1 es2,
    shuffle es0 es1 es2 ->
    In e (skipn i es1) ->
    In e (skipn i es2).
Proof.
  intros.
  revert H0.
  revert e.
  revert i.
  induction H; intros; auto.
  - rewrite skipn_nil in H0.
    inv H0.
  - apply IHshuffle in H0.
    apply in_skipn_cons; auto.
  - destruct i; simpl in *; auto.
    destruct H0; auto; right.
    specialize IHshuffle with (i:=0).
    simpl in *; auto.
Qed.

Lemma shuffle_earlier_left:
  forall es0 es1 es2 e0 e1,
    earlier es0 e0 e1 ->
    shuffle es0 es1 es2 ->
    earlier es2 e0 e1.
Proof.
  intros.
  destruct H as [i H].
  destruct H.
  unfold earlier.
  revert H.
  revert H1.
  revert i.
  induction H0; intros.
  - rewrite firstn_nil in H; inv H.
  - exists i; auto.
  - destruct i.
    + simpl in *; tauto.
    + simpl in H, H1.
      destruct H; subst.
      * exists (S i); simpl; auto.
        split; auto.
        eapply shuffle_in_skipn_left; eauto.
      * eapply IHshuffle in H1; eauto.
        destruct H1 as [n].
        destruct H1.
        exists (S n); simpl; auto.
  - eapply IHshuffle in H1; eauto.
    destruct H1 as [n].
    destruct H1.
    exists (S n); simpl; auto.
Qed.

Lemma shuffle_earlier_right:
  forall es0 es1 es2 e0 e1,
    earlier es1 e0 e1 ->
    shuffle es0 es1 es2 ->
    earlier es2 e0 e1.
Proof.
  intros.
  destruct H as [i H].
  destruct H.
  unfold earlier.
  revert H.
  revert H1.
  revert i.
  induction H0; intros.
  - exists i; auto.
  - rewrite firstn_nil in H; inv H.
  - eapply IHshuffle in H1; eauto.
    destruct H1 as [n].
    destruct H1.
    exists (S n); simpl; auto.
  - destruct i.
    + simpl in *; tauto.
    + simpl in H, H1.
      destruct H; subst.
      * exists (S i); simpl; auto.
        split; auto.
        eapply shuffle_in_skipn_right; eauto.
      * eapply IHshuffle in H1; eauto.
        destruct H1 as [n].
        destruct H1.
        exists (S n); simpl; auto.
Qed.

Lemma shuffle_nodup_append:
  forall tr0 tr1 tr2,
    NoDup tr0 -> NoDup tr1 ->
    disjoint_lists tr0 tr1 ->
    shuffle tr0 tr1 tr2 ->
    NoDup tr2.
Proof.
  intros.
  induction H2; auto.
  - apply NoDup_cons.
    + intro.
      eapply shuffle_in in H2.
      apply H2 in H3.
      destruct H3.
      * inv H; tauto.
      * apply H1 in H3; simpl; auto.
    + apply IHshuffle; auto.
      * inv H; auto.
      * unfold disjoint_lists; intros.
        apply H1 in H4; auto.
        simpl; auto.
  - apply NoDup_cons.
    + intro.
      eapply shuffle_in in H2.
      apply H2 in H3.
      destruct H3.
      * apply H1 in H3; simpl in H3; auto.
      * inv H0; tauto.
    + apply IHshuffle; auto.
      * inv H0; auto.
      * unfold disjoint_lists; intros.
        apply H1 in H3; auto.
        simpl in H3; auto.
Qed.

(** * Big-Step Semantics

    The traces associated with an annotated term are defined
    inductively. *)

Inductive trace: AnnoTerm -> Plc ->
                 list Ev -> Prop :=
| tasp: forall r x p,
    trace (aasp r x) p [(asp_event (fst r) x p)]
| tatt: forall r x p q tr1,
    trace x q tr1 ->
    trace (aatt r q x) p
          ((req (fst r) p q (unanno x) )
             :: tr1 ++
             [(rpy (pred (snd r)) p q)])
| tlseq: forall r x y p tr0 tr1,
    trace x p tr0 ->
    trace y p tr1 ->
    trace (alseq r x y) p (tr0 ++ tr1)
| tbseq: forall r s x y p tr0 tr1,
    trace x p tr0 ->
    trace y p tr1 ->
    trace (abseq r s x y) p
          ((split (fst r) p)
             :: tr0 ++ tr1 ++
             [(join (pred (snd r)) p)])
| tbpar: forall r s x y p tr0 tr1 tr2,
    trace x p tr0 ->
    trace y p tr1 ->
    shuffle tr0 tr1 tr2 ->
    trace (abpar r s x y) p
          ((split (fst r) p)
             :: tr2 ++
             [(join (pred (snd r)) p)]).
Hint Resolve tasp : core.

Lemma trace_length:
  forall t p tr,
    trace t p tr -> esize t = length tr.
Proof.
  induction t; intros; inv H;
    simpl; auto; rewrite app_length; simpl; auto.
  - apply IHt in H5; lia.
  - apply IHt1 in H5.
    apply IHt2 in H6. lia.
    
  - apply IHt1 in H6.
    apply IHt2 in H7.
    rewrite app_length. simpl in *. lia.
    
  - apply IHt1 in H6.
    apply IHt2 in H7.
    apply shuffle_length in H8. lia. 
Qed.

(** The events in a trace correspond to the events associated with an
    annotated term, a place, and some evidence. *)

Lemma trace_events:
  forall t p tr v,
    well_formed t ->
    trace t p tr ->
    In v tr <-> events t p v.
Proof.
  split; intros.
  - induction H0; inv H.
    + inv H1; try inv H.
      destruct x; constructor; auto.
    + inv H1.
      constructor; auto.
      rewrite in_app_iff in H.
      destruct H.
      apply evtsatt; auto.
      inv H; try inv H1.
      rewrite H7; simpl.
      apply evtsattrpy; auto.
    + rewrite in_app_iff in H1.
      destruct H1.
      * apply evtslseql; auto.
      * apply evtslseqr; auto.
        
    + destruct H1; subst.
      apply evtsbseqsplit; auto.
      apply in_app_iff in H; destruct H.
      apply evtsbseql; auto.
      apply in_app_iff in H; destruct H.
      apply evtsbseqr; auto.
      destruct H; subst.
      rewrite H9.
      apply evtsbseqjoin; auto.
      inv H.
    + destruct H1; subst.
      apply evtsbparsplit; auto.
      apply in_app_iff in H; destruct H.
      apply shuffle_in with (e:=v) in H0.
      apply H0 in H.
      destruct H.
      apply evtsbparl; auto.
      apply evtsbparr; auto.
      rewrite H10 in H; simpl in H.
      destruct H; try tauto; subst.
      apply evtsbparjoin; auto.
  - induction H0; inv H.
    + inv H1; destruct r as [i j]; simpl in *; auto.
    + simpl; rewrite in_app_iff; simpl.
      inv H1; auto.
      right; right.
      Require Import StructTactics.
      repeat find_rewrite; simpl; auto.
    + rewrite in_app_iff.
      inv H1; auto.
      
    + simpl.
      rewrite in_app_iff.
      rewrite in_app_iff.
      simpl.
      inv H1; auto.
      rewrite H11 in *.
      auto.
      
    + simpl.
      rewrite in_app_iff.
      simpl.
      inv H1; auto.
      * apply IHtrace1 in H13; auto.
        eapply shuffle_in_left in H0; eauto.
      * apply IHtrace2 in H13; auto.
        eapply shuffle_in_right in H0; eauto.
      * repeat find_rewrite; simpl; auto.
Qed.

Lemma trace_range:
  forall t p tr v,
    well_formed t ->
    trace t p tr ->
    In v tr ->
    fst (range t) <= ev v < snd (range t).
Proof.
  intros.
  rewrite trace_events in H1; eauto.
  eapply events_range; eauto.
Qed.

Lemma trace_range_event:
  forall t p tr i,
    well_formed t ->
    trace t p tr ->
    fst (range t) <= i < snd (range t) ->
    exists v, In v tr /\ ev v = i.
Proof.
  intros.
  eapply events_range_event in H1; eauto.
  destruct H1 as [v G]; destruct G as [G]; subst.
  rewrite <- trace_events in G; eauto.
Qed.

Lemma trace_injective_events:
  forall t p tr v0 v1,
    well_formed t ->
    trace t p tr ->
    In v0 tr -> In v1 tr ->
    ev v0 = ev v1 ->
    v0 = v1.
Proof.
  intros.
  rewrite trace_events in H1; eauto.
  rewrite trace_events in H2; eauto.
  eapply events_injective; eauto.
Qed.

Lemma nodup_trace:
  forall t p tr,
    well_formed t ->
    trace t p tr ->
    NoDup tr.
Proof.
  induction t; intros; inv H; inv H0.
  - constructor; auto; constructor.
  - destruct r as [i j]; simpl in *; subst; simpl.
    apply NoDup_cons.
    + intro.
      apply in_app_iff in H1.
      destruct H1.
      * eapply trace_range in H9; eauto.
        simpl in *.
        lia.
      * inv H1.
        discriminate H2.
        inv H2.
    + apply nodup_append; unfold disjoint_lists; auto; intros.
      * eapply IHt; eauto.
      * constructor; auto; constructor.
      * inv H2.
        eapply trace_range in H9; eauto.
        simpl in *.
        lia.
        solve_by_inversion.
  - apply nodup_append; unfold disjoint_lists; auto; intros.
    eapply IHt1; eauto.
    eapply IHt2; eauto.
    eapply trace_range in H11; eauto.
    eapply trace_range in H12; eauto.
    lia.
    
  - destruct r as [i j]; simpl in *; subst; simpl.
    apply NoDup_cons.
    + intro.
      repeat rewrite in_app_iff in H1.
      repeat destruct_disjunct.
      * eapply trace_range in H12; eauto.
        simpl in H12.
        lia.
      * eapply trace_range in H13; eauto.
        simpl in H13.
        apply well_formed_range in H5; auto.
        lia.
      * inv H1.
        discriminate H2.
        solve_by_inversion.
    + apply nodup_append; unfold disjoint_lists; auto; intros.
      * eapply IHt1; eauto.
      * apply nodup_append; unfold disjoint_lists; auto; intros.
        -- eapply IHt2; eauto.
        -- apply NoDup_cons.
           intro HH; inv HH.
           constructor.
        -- inv H2.
           eapply trace_range in H13; eauto.
           simpl in H13.
           lia.
           solve_by_inversion.
      * apply in_app_iff in H2; destruct H2.
        eapply trace_range in H12; eauto.
        eapply trace_range in H13; eauto.
        lia.
        inv H2.
        eapply trace_range in H12; eauto.
        simpl in H12.
        apply well_formed_range in H6; auto.
        lia.
        solve_by_inversion.
        
  - destruct r as [i j]; simpl in *; subst; simpl.
    apply NoDup_cons.
    + intro HH.
      rewrite in_app_iff in HH; destruct HH.
      * eapply shuffle_in in H1; eauto.
        destruct H1.
        -- eapply trace_range in H13; eauto.
           simpl in H13.
           lia.
        -- eapply trace_range in H14; eauto.
           simpl in H14.
           apply well_formed_range in H6; auto.
           lia.
      * inv H1.
        discriminate H2.
        solve_by_inversion.
    + apply nodup_append; unfold disjoint_lists; auto; intros.
      * apply shuffle_nodup_append in H15;
          unfold disjoint_lists; auto; intros.
        eapply IHt1; eauto.
        eapply IHt2; eauto.
        eapply trace_range in H13; eauto.
        eapply trace_range in H14; eauto.
        lia.
      * apply NoDup_cons.
        intro HH.
        solve_by_inversion.
        constructor.
      * inv H2.
        -- eapply shuffle_in in H1; eauto.
           destruct H1.
           eapply trace_range in H13; eauto.
           simpl in H13.
           apply well_formed_range in H6; auto.
           lia.
           eapply trace_range in H14; eauto.
           simpl in H14.
           lia.
     
    

        -- solve_by_inversion.
Qed.

(** * Event Systems and Traces *)

Lemma evsys_tr_in:
  forall t p tr ev0,
    well_formed t ->
    trace t p tr ->
    ev_in ev0 (ev_sys t p) ->
    In ev0 tr.
Proof.
  intros.
  (*
  induction H0.
  inv H.
  simpl in H1.
  expand_let_pairs. inv H1. simpl. auto. *)
  
 
  induction H0; inv H; simpl in H1;
    try expand_let_pairs; inv H1; simpl; auto.
  - left. solve_by_inversion.
  - right. inv H4; auto.
    + apply IHtrace in H8; auto.
      rewrite in_app_iff; auto.
    + inv H8. rewrite in_app_iff.
      right. simpl. left. auto.
  - apply IHtrace1 in H4; auto.
    rewrite in_app_iff; auto.
  - apply IHtrace2 in H5; auto.
    rewrite in_app_iff; auto.
    
  - left. solve_by_inversion.
  - right. inv H3; auto.
    + inv H4; auto.
      * apply IHtrace1 in H5; auto.
        rewrite in_app_iff; auto.
      * apply IHtrace2 in H6; auto.
        rewrite in_app_iff.
        right; rewrite in_app_iff; auto.
    + inv H4; auto.
      repeat (rewrite in_app_iff; right).
      simpl; left; auto.
      
  - left. solve_by_inversion.
  - right. inv H4; auto.
    + inv H5; auto.
      * apply IHtrace1 in H6; auto.
        eapply shuffle_in_left in H0; eauto.
        rewrite in_app_iff; auto.
      * apply IHtrace2 in H7; auto.
        eapply shuffle_in_right in H0; eauto.
        rewrite in_app_iff; auto.
    + inv H5.
      apply in_app_iff; right; simpl; auto.
Qed.

(** The traces associated with an annotated term are compatible with
    its event system. *)

Theorem trace_order:
  forall t p tr ev0 ev1,
    well_formed t ->
    trace t p tr ->
    prec (ev_sys t p) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  induction H0; inv H; simpl in H1;
    try expand_let_pairs; inv H1; simpl; auto.
  - inv H11; inv H10.
    + eapply evsys_tr_in in H4; eauto.
      apply earlier_cons; auto.
      apply in_app_iff; auto.
    + inv H4.
      apply earlier_cons; auto.
      apply in_app_iff; auto. right; simpl; auto.
  - solve_by_inversion.
  - inv H10.
    + inv H12.
      eapply evsys_tr_in in H11; eauto.
      apply earlier_cons_shift; auto.
      apply earlier_append; auto; simpl; auto.
    + eapply IHtrace in H5; eauto.
      apply earlier_cons_shift; auto.
      apply earlier_left; auto.
    + solve_by_inversion.
  - eapply evsys_tr_in in H11; eauto.
    eapply evsys_tr_in in H12; eauto.
    apply earlier_append; auto.
  - apply IHtrace1 in H11; auto.
    apply earlier_left; auto.
  - apply IHtrace2 in H11; auto.
    apply earlier_right; auto.
    
  - inv H12; inv H11.
    + inv H3.
      * eapply evsys_tr_in in H4; eauto.
        apply earlier_cons; auto.
        apply in_app_iff; auto.
      * eapply evsys_tr_in in H4; eauto.
        apply earlier_cons; auto.
        apply in_app_iff; right;
          apply in_app_iff; simpl; auto.
    + inv H3.
      apply earlier_cons; auto.
      repeat (apply in_app_iff; right).
      simpl; auto.
  - solve_by_inversion.
    
  - inv H11.
    + inv H13. inv H12.
      * eapply evsys_tr_in in H3; eauto.
        apply earlier_cons_shift; auto.
        apply earlier_append; auto.
        apply in_app_iff; right; simpl; auto.
      * eapply evsys_tr_in in H3; eauto.
        apply earlier_cons_shift; auto.
        apply earlier_right; auto.
        apply earlier_append; simpl; auto.
    + inv H12.
      * eapply evsys_tr_in in H14; eauto.
        eapply evsys_tr_in in H13; eauto.
        apply earlier_cons_shift; auto.
        apply earlier_append; auto.
        apply in_app_iff; left; auto.
      * apply IHtrace1 in H13; auto.
        apply earlier_cons_shift; auto.
        apply earlier_left; auto.
      * apply IHtrace2 in H13; auto.
        apply earlier_cons_shift; auto.
        apply earlier_right; auto.
        apply earlier_left; auto.
    + solve_by_inversion.
      
  - inv H13. inv H14.
    + inv H4; eapply evsys_tr_in in H5; eauto.
      * apply earlier_cons; auto.
        apply shuffle_in_left with (es1:=tr1)(es2:=tr2) in H5; auto.
        apply in_app_iff; left; auto.
      * apply earlier_cons; auto.
        apply shuffle_in_right with (e:=ev1) in H0; auto.
        apply in_app_iff; left; auto.
    + inv H4.
      apply earlier_cons; auto.
      apply in_app_iff; right; simpl; auto.
  - solve_by_inversion.
  - inv H13.
    + inv H15. inv H14.
      * eapply evsys_tr_in in H4; eauto.
        apply shuffle_in_left with (e:= ev0) in H0; auto.
        apply earlier_cons_shift; auto.
        apply earlier_append; simpl; auto.
      * eapply evsys_tr_in in H4; eauto.
        apply shuffle_in_right with (e:=ev0) in H0; auto.
        apply earlier_cons_shift; auto.
        apply earlier_append; simpl; auto.
    + inv H14.
      * apply IHtrace1 in H6; auto.
        apply shuffle_earlier_left
          with (e0:=ev0)(e1:=ev1) in H0; auto.
        apply earlier_cons_shift; auto.
        apply earlier_left; auto.
      * apply IHtrace2 in H7; auto.
        apply shuffle_earlier_right
          with (e0:=ev0)(e1:=ev1) in H0; auto.
        apply earlier_cons_shift; auto.
        apply earlier_left; auto.
    + solve_by_inversion.
Qed.

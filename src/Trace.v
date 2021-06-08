(* Traces and their relation to event systems *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** Traces and their relation to event systems. *)

Require Import Preamble More_lists Defs Term_Defs Term Event_system Term_system StructTactics.

Require Import Coq.Program.Tactics.

Require Import Lia.

Require Import List.
Import List.ListNotations.
Open Scope list_scope.


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
  intros es0 es1 es2 H.
  induction H; simpl; auto; lia.
Qed.

Lemma shuffle_in_left:
  forall e es0 es1 es2,
    shuffle es0 es1 es2 ->
    In e es0 ->
    In e es2.
Proof.
  intros e es0 es1 es2 H H0.
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
  intros e es0 es1 es2 H H0.
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
  intros e es0 es1 es2 H.
  split; intros H0.
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
  intros i e es0 es1 es2 H H0.
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
  intros  i e es0 es1 es2 H H0.
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
  intros es0 es1 es2 e0 e1 H H0.
  destruct H as [i H].
  destruct H as [H H1].
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

Inductive trace: AnnoTerm -> Plc -> Evidence ->
                 list Ev -> Prop :=
| tasp: forall r x p e,
    trace (aasp r x) p e [(asp_event (fst r) x p e)]
| tatt: forall r x p q e tr1,
    trace x q e tr1 ->
    trace (aatt r q x) p e
          ((req (fst r) p q (unanno x) e )
             :: tr1 ++
             [(rpy (pred (snd r)) p q)])
| tlseq: forall r x y p e tr0 tr1,
    trace x p e tr0 ->
    trace y p (aeval x p e) tr1 ->
    trace (alseq r x y) p e (tr0 ++ tr1)
| tbseq: forall r s x y p e tr0 tr1,
    trace x p (splitEv_T_l s e) tr0 ->
    trace y p (splitEv_T_r s e) tr1 ->
    trace (abseq r s x y) p e
          ((Term_Defs.split (fst r) p)
             :: tr0 ++ tr1 ++
             [(join (pred (snd r)) p)])
| tbpar: forall r s x y p e tr0 tr1 tr2,
    trace x p (splitEv_T_l s e) tr0 ->
    trace y p (splitEv_T_r s e) tr1 ->
    shuffle tr0 tr1 tr2 ->
    trace (abpar r s x y) p e
          ((Term_Defs.split (fst r) p)
             :: tr2 ++
             [(join (pred (snd r)) p)]).
Hint Resolve tasp : core.

Lemma trace_length:
  forall t p e tr,
    trace t p e tr -> esize t = length tr.
Proof.
  induction t; intros; inv H;
    simpl; auto; rewrite app_length; simpl; auto;
      try (repeat find_eapply_hyp_hyp;
           try rewrite app_length; simpl in *;
           try find_apply_lem_hyp shuffle_length;
           lia).
Defined.

(** The events in a trace correspond to the events associated with an
    annotated term, a place, and some evidence. *)


Ltac inv_in :=
  repeat
  match goal with
  | [H: In _ (?C _) |- _] =>
    invc H
  end.

Ltac nodup_inv :=
  repeat 
    match goal with
    | [H: NoDup (_::_) |- _] => invc H
    end.

Ltac do_nodup :=
  repeat (
      nodup_inv; inv_in;
      ff;
      nodup_inv; inv_in;
      unfold not in *; try intro;
      econstructor;
      try intro;
      inv_in;
      try (conclude_using ltac:(econstructor; eauto))).

Lemma trace_events:
  forall t p e tr v,
    well_formed_r t ->
    trace t p e tr ->
    In v tr <-> events t p e v.
Proof.
  split; intros.
  - induction H0; inv_wfr.
    +
      destruct x; do_nodup.
    +
      inv_in.
      constructor; auto.
      rewrite in_app_iff in *.
      destruct_disjunct.
      eauto.
      inv_in; try solve_by_inversion.
      apply evtsattrpy.
      lia.
      (*   
      eauto.
      eapply IHtrace.
      eassumption.
      repeat find_rewrite.
      Print evtsattrpy.

      
      econstructor.
      apply evtsattrpy; auto.
      econstructor.
      
      apply evtsatt; auto.
      inv H; try inv H1.
      rewrite H9; simpl.
      apply evtsattrpy; auto. *)
    +
      rewrite in_app_iff in *.
      destruct_disjunct.
      * apply evtslseql; auto.
      * apply evtslseqr; auto.
        
    +
      inv_in; subst; try solve_by_inversion.
      rewrite in_app_iff in *; destruct_disjunct.
      apply evtsbseql; auto.
      rewrite in_app_iff in *; destruct_disjunct.
      apply evtsbseqr; auto.
      inv_in; subst; try solve_by_inversion.
      repeat find_rewrite.
      apply evtsbseqjoin; auto. 
    +
      

      inv_in; subst; try solve_by_inversion.
      rewrite in_app_iff in *; destruct_disjunct.
      apply shuffle_in with (e:=v) in H0.
      destruct H0.
      repeat concludes.
      destruct_disjunct.
      
      apply evtsbparl; auto.
      apply evtsbparr; auto.
      inv_in.
      repeat find_rewrite.
      solve_by_inversion.

  - induction H0; inv H.
    + inv H1; destruct r as [i j]; simpl in *; auto.
    + simpl; rewrite in_app_iff; simpl.
      inv H1; auto.
      right; right.
      repeat find_rewrite; simpl; auto.
    + rewrite in_app_iff.
      inv H1; auto.

      
    + simpl.
      rewrite in_app_iff.
      rewrite in_app_iff.
      simpl.
      inv H1; auto.
      repeat find_rewrite.
      auto.
      
    + simpl.
      rewrite in_app_iff.
      simpl.
      inv_events; auto;
      (*
      inv H1; auto. *)
      
        try
          (find_apply_hyp_hyp; auto;
           try (find_eapply_lem_hyp shuffle_in_left; eauto; tauto);
           try find_eapply_lem_hyp shuffle_in_right; eauto; tauto);
        try
          (repeat find_rewrite; auto; tauto).
Qed.

Lemma trace_range:
  forall t p e tr v,
    well_formed_r t ->
    trace t p e tr ->
    In v tr ->
    fst (range t) <= ev v < snd (range t).
Proof.
  intros.
  rewrite trace_events in H1; eauto.
  eapply events_range; eauto.
Qed.

Lemma trace_range_event:
  forall t p e tr i,
    well_formed_r t ->
    trace t p e tr ->
    fst (range t) <= i < snd (range t) ->
    exists v, In v tr /\ ev v = i.
Proof.
  intros.
  eapply events_range_event in H1; eauto.
  destruct H1 as [v G]; destruct G as [G]; subst.
  rewrite <- trace_events in G; eauto.
Qed.

Lemma trace_injective_events:
  forall t p e tr v0 v1,
    well_formed_r t ->
    trace t p e tr ->
    In v0 tr -> In v1 tr ->
    ev v0 = ev v1 ->
    v0 = v1.
Proof.
  intros.
  rewrite trace_events in H1; eauto.
  rewrite trace_events in H2; eauto.
  eapply events_injective; eauto.
Qed.

Ltac tr_wf :=
  match goal with
  | [H: well_formed_r ?t,
        H': trace ?t _ _ ?tr,
            H'': In ?v ?tr |- _] =>
    assert_new_proof_by (fst (range t) <= ev v < snd (range t))
                        ltac:(eapply trace_range; [apply H | apply H' | apply H''])
  end.

Lemma nodup_trace:
  forall t p e tr,
    well_formed_r t ->
    trace t p e tr ->
    NoDup tr.
Proof.
  induction t; intros; inv_wfr; inv H0.
  - constructor; auto; constructor.
  - destruct r as [i j]; simpl in *; subst; simpl.
    apply NoDup_cons.
    + intro.
      rewrite in_app_iff in *. 
      destruct_disjunct.
      *
        find_eapply_lem_hyp trace_range; eauto.
        simpl in *.
        lia.
      *
        inv_in.
        solve_by_inversion.
    +
      apply nodup_append; unfold disjoint_lists; auto; intros.
      * eapply IHt; eauto.
      * constructor; auto; constructor.
      *
        inv_in.
        find_eapply_lem_hyp trace_range; eauto.
        simpl in *.
        lia.
  -
    apply nodup_append; unfold disjoint_lists; auto; intros; eauto.
    repeat tr_wf.
    lia.
  -
    dest_range'; simpl in *; subst; simpl.
      
    apply NoDup_cons.
    + intro.
      repeat rewrite in_app_iff in *;
      repeat destruct_disjunct;
        try solve_by_inversion.     
      *
        tr_wf.
        simpl in *.
        lia.
      *
        repeat tr_wf.
        simpl in *.
        repeat find_eapply_lem_hyp well_formed_range_r; auto.
        lia.
      * inv_in.
        solve_by_inversion.
    + apply nodup_append; unfold disjoint_lists; auto; intros.
      * eapply IHt1; eauto.
      * apply nodup_append; unfold disjoint_lists; auto; intros;
          try eauto;
          try do_nodup;
          try (inv_in; repeat tr_wf; simpl in *; lia).
      *
        rewrite in_app_iff in *; destruct_disjunct.
        repeat tr_wf.
        lia.

        inv_in.
        repeat tr_wf.
        repeat find_eapply_lem_hyp well_formed_range_r; auto.
        simpl in *.
        lia.   
  -
    dest_range'; simpl in *; subst; simpl.
    apply NoDup_cons.
    + intro HH.
      rewrite in_app_iff in *; destruct_disjunct;
        try (inv_in; solve_by_inversion; tauto).
      *
        find_eapply_lem_hyp shuffle_in; eauto.
        
        destruct_disjunct;
          try (inv_in; solve_by_inversion);
          try solve_by_inversion;
          try (tr_wf;
               simpl in * ;
               lia).
        
        --
          tr_wf.
          simpl in *.
          repeat find_eapply_lem_hyp well_formed_range_r; auto.
          lia.
        
    + apply nodup_append; unfold disjoint_lists; auto; intros.
      *

        find_eapply_lem_hyp shuffle_nodup_append;
          unfold disjoint_lists; auto; intros;
            eauto.
        repeat tr_wf.
        simpl in *.
        lia.
      *
        do_nodup.
      *
        inv_in.
        --
          find_eapply_lem_hyp shuffle_in; eauto;
            destruct_disjunct;
            repeat tr_wf;
              simpl in *;  
              try find_eapply_lem_hyp well_formed_range_r; eauto;
                simpl in * ;
                lia.         
Qed.

Ltac do_shuf_l :=
  match goal with
  | [H: shuffle ?tr0 ?tr1 ?tr2,
        H': In ?ev ?tr0 |- _] =>
    eapply shuffle_in_left in H; eauto 
  end.

Ltac do_shuf_r :=
  match goal with
  | [H: shuffle ?tr0 ?tr1 ?tr2,
        H': In ?ev ?tr1 |- _] =>
    eapply shuffle_in_right in H; eauto 
  end.

(** * Event Systems and Traces *)

Lemma evsys_tr_in:
  forall t p e tr ev0,
    well_formed_r t ->
    trace t p e tr ->
    ev_in ev0 (ev_sys t p e) ->
    In ev0 tr.
Proof.
  intros.
  induction H0; inv_wfr; simpl in *;
    try expand_let_pairs; do_evin; simpl; auto;
      try (left; solve_by_inversion).
  -
    rewrite in_app_iff in *.
    right.
    do_evin; eauto.
    do_evin.
    try (try right; left; solve_by_inversion).  
  -
    rewrite in_app_iff; auto.
  -
    rewrite in_app_iff; auto.   
  -
    right.
    rewrite in_app_iff in *.
    do_evin; auto.
    +
      do_evin; auto;
        eauto.
      rewrite in_app_iff; auto.
    +
      do_evin; auto.
      (repeat rewrite in_app_iff; right).
      right.
      left.
      auto.    
  - right.
    do_evin; auto.
    +
      do_evin; auto.
      *
        repeat find_apply_hyp_hyp.
        do_shuf_l.
        rewrite in_app_iff; auto.
      *
        find_eapply_hyp_hyp; auto.

        do_shuf_r.
        rewrite in_app_iff; auto.
    +
      do_evin.
      rewrite in_app_iff; right; simpl; auto.
Qed.

Ltac inv_prec :=
  match goal with
  | H:prec (?C _) _ _ |- _ => inv H
  end.

Ltac do_evin2 :=
  match goal with
  | [H:ev_in _ (?C _),
       H':ev_in _ (?D _)|- _] =>
    inv H; inv H'
  end.

(** The traces associated with an annotated term are compatible with
    its event system. *)

Theorem trace_order:
  forall t p e tr ev0 ev1,
    well_formed_r t ->
    trace t p e tr ->
    prec (ev_sys t p e) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros t p e tr ev0 ev1 H H0 H1.
  induction H0; inv H; simpl in H1;
    try expand_let_pairs;
    inv_prec; simpl; auto. 
  -
    do_evin2.
    +
      find_eapply_lem_hyp evsys_tr_in; eauto.
      apply earlier_cons; auto.
      apply in_app_iff; auto.
    +
      do_evin.
      apply earlier_cons; auto.
      apply in_app_iff; auto; right; simpl; auto.
  - solve_by_inversion.
  -
    inv_prec.
    +
      do_evin.
      find_eapply_lem_hyp evsys_tr_in; eauto.
      apply earlier_cons_shift; auto.
      apply earlier_append; auto; simpl; auto.
    +
      find_eapply_hyp_hyp; eauto.
      apply earlier_cons_shift; auto.
      apply earlier_left; auto.
    + solve_by_inversion.
  -
    find_eapply_lem_hyp evsys_tr_in; eauto.
    find_eapply_lem_hyp evsys_tr_in; eauto.
    apply earlier_append; auto.
  -
    find_apply_hyp_hyp; auto.
    apply earlier_left; auto.
  -
    find_apply_hyp_hyp; auto.
    apply earlier_right; auto.   
  -
    do_evin2.
    +
      do_evin.
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        apply earlier_cons; auto.
        apply in_app_iff; auto.
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.      
        apply earlier_cons; auto.
        apply in_app_iff; right;
          apply in_app_iff; simpl; auto.
    +
      do_evin.
      apply earlier_cons; auto.
      repeat (apply in_app_iff; right).
      simpl; auto.
  -
    solve_by_inversion.
  -
    inv_prec.
    +
      do_evin2.
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        apply earlier_cons_shift; auto.
        apply earlier_append; auto.
        apply in_app_iff; right; simpl; auto.
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        apply earlier_cons_shift; auto.
        apply earlier_right; auto.
        apply earlier_append; simpl; auto.
    +
      inv_prec.
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        find_eapply_lem_hyp evsys_tr_in; eauto.

        apply earlier_cons_shift; auto.
        apply earlier_append; auto.
        apply in_app_iff; left; auto.
      *
        find_apply_hyp_hyp; auto.
        apply earlier_cons_shift; auto.
        apply earlier_left; auto.
      *
        find_apply_hyp_hyp; auto.
        apply earlier_cons_shift; auto.
        apply earlier_right; auto.
        apply earlier_left; auto.
    +
      solve_by_inversion.

  -
    do_evin2.
    +
      do_evin;
        find_eapply_lem_hyp evsys_tr_in; eauto.
      * apply earlier_cons; auto.
        Check shuffle_in_left.
        find_eapply_lem_hyp shuffle_in_left.
        2: {
          eauto.
        }
        erewrite in_app_iff; left; auto.
      * apply earlier_cons; auto.
        find_eapply_lem_hyp shuffle_in_right.
        2: {
          eauto.
        }
        apply in_app_iff; left; auto.
    +
      do_evin.
      apply earlier_cons; auto.
      apply in_app_iff; right; simpl; auto.
  -
    solve_by_inversion.
  -
    eapply earlier_cons_shift.
    
    inversion H12; subst.
    +
      inversion H13; subst.
      ++
        invc H14.
        eapply earlier_append.
        eapply shuffle_in_left.
        eassumption.
        eapply evsys_tr_in.
        apply H6.
        eassumption.
        eassumption.
        econstructor.
        tauto.
      ++
        apply earlier_append.
        eapply shuffle_in_right.
        eassumption.
        eapply evsys_tr_in.
        eassumption.
        eassumption.
        eassumption.
        invc H14.
        econstructor.
        tauto.
    +
      eapply earlier_left.
      inversion H13; subst.
      ++
        eapply shuffle_earlier_left.
        2: {
          eassumption.
        }   
        eauto.
      ++
        eapply shuffle_earlier_right.
        2: {
          eassumption.
        }
        eauto.
    +
      solve_by_inversion.
Defined.

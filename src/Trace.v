(* Traces and their relation to event systems *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** Traces and their relation to event systems. *)

Require Import Preamble More_lists Term_Defs Term Event_system Term_system StructTactics.

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
(*| tbseq: forall r lr s x y p tr0 tr1,
    trace x p tr0 ->
    trace y p tr1 ->
    trace (abseq r lr s x y) p
          ((Term_Defs.split (fst r) p)
             :: tr0 ++ tr1 ++
             [(join (pred (snd r)) p)])
| tbpar: forall r lr s x y p tr0 tr1 tr2 (*xi xi'*) yi yi',
    trace x p tr0 ->
    trace y p tr1 ->
    shuffle tr0 tr1 tr2 ->
    trace (abpar r lr (*(xi,xi')*) (yi,yi') s x y) p
          ((splitp (fst r) (*xi*) yi p)
             :: tr2 ++
             [(joinp (pred (snd r)) (*xi'*) yi' yi' p)]) *) .
Hint Resolve tasp : core.

Lemma trace_length:
  forall t p tr,
    trace t p tr -> esize t = length tr.
Proof.
  induction t; intros; inv H;
    simpl; auto; rewrite app_length; simpl; auto;
      try (repeat find_eapply_hyp_hyp;
           try rewrite app_length; simpl in *;
           try find_apply_lem_hyp shuffle_length;
           lia).
Defined.
(*
  -
    find_eapply_hyp_hyp.
    lia.
    


  
  - apply IHt in H7; lia.
  - apply IHt1 in H6.
    apply IHt2 in H7; lia.
    
  - apply IHt1 in H7.
    apply IHt2 in H8.
    rewrite app_length; simpl in *; lia.
    
  - apply IHt1 in H9.
    apply IHt2 in H10.
    apply shuffle_length in H11; lia. 
Qed.
*)

(** The events in a trace correspond to the events associated with an
    annotated term, a place, and some evidence. *)

Require Import List_Facts Coq.Program.Tactics.

Lemma trace_events:
  forall t p tr v,
    well_formed_r t ->
    trace t p tr ->
    In v tr <-> events t p v.
Proof.
  split; intros.
  - induction H0; inv_wfr.
    +
      destruct x;
        do_nodup.

      (*
      nodup_facts

      inv H1; try inv H.
      destruct x; constructor; auto. *)
    +
      inv_in.
      (*
      

      inv H1. *)
      constructor; auto.
      rewrite in_app_iff in *.
      destruct_disjunct.
      eauto.

      inv_in; try solve_by_inversion.
      
(*
      invc H2; try solve_by_inversion. *)
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
        (*
    +
      inv_in; subst; try solve_by_inversion.
      (*
      

      destruct H1; subst; try solve_by_inversion. *)
      (*
      apply evtsbseqsplit; auto. *)
      rewrite in_app_iff in *; destruct_disjunct.
      apply evtsbseql; auto.
      rewrite in_app_iff in *; destruct_disjunct.
      apply evtsbseqr; auto.
      inv_in; subst; try solve_by_inversion.
      (*
      destruct H0; subst; try solve_by_inversion. *)
      repeat find_rewrite.
      (*
      rewrite H10. *)
      apply evtsbseqjoin; auto.
    +
      

      inv_in; subst; try solve_by_inversion.
      (*
      apply evtsbparsplit; auto. *)
      rewrite in_app_iff in *; destruct_disjunct.
      (* find_eapply_lem_hyp shuffle_in. *)
      
      apply shuffle_in with (e:=v) in H0.
      (* repeat find_apply_hyp_hyp. *)
      (*apply H0 in H1. *)
      destruct H0.
      repeat concludes.
      destruct_disjunct.
      
      (*
      apply H0 in H.
      destruct H.
       *)
      
      apply evtsbparl; auto.
      apply evtsbparr; auto.
      inv_in.
      repeat find_rewrite.
      solve_by_inversion.

      (*
      (*
      rewrite H13 in H; simpl in H.
      destruct H; try tauto; subst. *)
      apply evtsbparjoin; auto. *)
*)
  - induction H0; inv H.
    + inv H1; destruct r as [i j]; simpl in *; auto.
    + simpl; rewrite in_app_iff; simpl.
      inv H1; auto.
      right; right.
      repeat find_rewrite; simpl; auto.
    + rewrite in_app_iff.
      inv H1; auto.

      (*
    + simpl.
      rewrite in_app_iff.
      rewrite in_app_iff.
      simpl.
      inv H1; auto.
      repeat find_rewrite.
      auto.
      (*
      rewrite H12 in *.
      auto. *)
      
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

      (*
      *
        find_apply_hyp_hyp; auto.
        find_eapply_lem_hyp shuffle_in_right; eauto.
        

        apply IHtrace1 in H8; auto.
        eapply shuffle_in_left in H0; eauto.
      * apply IHtrace2 in H10; auto.
        eapply shuffle_in_right in H0; eauto.
      * repeat find_rewrite; simpl; auto. *)
*)
Qed.

Lemma trace_range:
  forall t p tr v,
    well_formed_r t ->
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
    well_formed_r t ->
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
    well_formed_r t ->
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

Require Import Defs.

Ltac tr_wf :=
  match goal with
  | [H: well_formed_r ?t,
        H': trace ?t _ ?tr,
            H'': In ?v ?tr |- _] =>
    assert_new_proof_by (fst (range t) <= ev v < snd (range t))
                        ltac:(eapply trace_range; [apply H | apply H' | apply H''])
  end.

(*
Ltac inv_in' :=
  match goal with
  | H:In _ _ |- _ => invc H
  end.
*)

Lemma nodup_trace:
  forall t p tr,
    well_formed_r t ->
    trace t p tr ->
    NoDup tr.
Proof.
  induction t; intros; inv_wfr; inv H0.
  - constructor; auto; constructor.
  - destruct r as [i j]; simpl in *; subst; simpl.
    apply NoDup_cons.
    + intro.
      rewrite in_app_iff in *.
      
      destruct_disjunct.
      (*
      destruct H1. *)
      *
        find_eapply_lem_hyp trace_range; eauto.
        simpl in *.
        lia.
        (*

        eapply trace_range in H12; eauto.
        simpl in *.
        lia. *)
      *
        inv_in.
        solve_by_inversion.
        (*
        inv H1.
        discriminate H2.
        inv H2. *)
    +
      apply nodup_append; unfold disjoint_lists; auto; intros.
      * eapply IHt; eauto.
      * constructor; auto; constructor.
      *
        inv_in.
        find_eapply_lem_hyp trace_range; eauto.
        simpl in *.
        lia.

        (*

        inv H2.
        eapply trace_range in H12; eauto.
        simpl in *.
        lia.
        solve_by_inversion. *)
  - apply nodup_append; unfold disjoint_lists; auto; intros; eauto.

    (*
    eapply IHt1; eauto.
    eapply IHt2; eauto.
     *)
    
    (*
    find_eapply_lem_hyp trace_range; eauto.
    find_eapply_lem_hyp trace_range; eauto.
    lia. *)

    repeat tr_wf.
    lia.

    (*
  -
    dest_range'; simpl in *; subst; simpl.
    (*

    destruct r as [i j]; simpl in *; subst; simpl. *)
      
    apply NoDup_cons.
    + intro.
      repeat rewrite in_app_iff in *.
      repeat destruct_disjunct;
        try solve_by_inversion.
      (*
        try (tr_wf;
             simpl in *;
             lia). *)
      
      *
        (*
        find_eapply_lem_hyp trace_range; eauto.
        repeat find_rewrite.
        simpl in *. lia. *)

        tr_wf.
        simpl in *.
        lia.
        (*

        eapply trace_range in H13; eauto.
        simpl in H13.
        lia. *)
      *
        repeat tr_wf.

        (*

        eapply trace_range in H14; eauto. *)
        simpl in *.
        Locate well_formed_range.
        Check well_formed_range.
        repeat find_eapply_lem_hyp well_formed_range_r; auto.
        lia.
        (*
        apply well_formed_range_r in H6; auto.
        lia. *)
      * inv_in.
        solve_by_inversion.
        (*
        discriminate H2.
        solve_by_inversion. *)
    + apply nodup_append; unfold disjoint_lists; auto; intros.
      * eapply IHt1; eauto.
      * apply nodup_append; unfold disjoint_lists; auto; intros;
          try eauto;
          try do_nodup;
          try (inv_in; repeat tr_wf; simpl in *; lia).

        (*
        (*
        -- eapply IHt2; eauto.
         *)
        
        --
          do_nodup.
          (*

          apply NoDup_cons.
           intro HH; inv HH.
           constructor. *)
        --

          inv_in.
          repeat tr_wf.
          simpl in *; lia.

          (*
          

          inv H2.
           eapply trace_range in H14; eauto.
           simpl in H14.
           lia.
           solve_by_inversion. *)

         *)


        
      *

        rewrite in_app_iff in *; destruct_disjunct.

        (*


        apply in_app_iff in H2; destruct H2. *)

        repeat tr_wf.
        lia.

        (*
        
        eapply trace_range in H13; eauto.
        eapply trace_range in H14; eauto.
        lia. *)

        inv_in.
        repeat tr_wf.
        repeat find_eapply_lem_hyp well_formed_range_r; auto.
        simpl in *.
        lia.

        (*

        
        inv H2.
        eapply trace_range in H13; eauto.
        simpl in H13.
        apply well_formed_range_r in H7; auto.
        lia.
        solve_by_inversion.
         *)
        
        
        
  -
    dest_range'; simpl in *; subst; simpl.
    (*



    destruct r as [i j]; simpl in *; subst; simpl. *)
    apply NoDup_cons.
    + intro HH.
      rewrite in_app_iff in *; destruct_disjunct;
        try (inv_in; solve_by_inversion; tauto).
      *
        find_eapply_lem_hyp shuffle_in; eauto.
        (*

        eapply shuffle_in in H1; eauto. *)
        
        destruct_disjunct;
          try (inv_in; solve_by_inversion);
          try solve_by_inversion;
          try (tr_wf;
               simpl in *;
               lia).
        (*
        --
          tr_wf.
          simpl in *.
          lia.
          (*

          eapply trace_range in H16; eauto.
           simpl in H16.
           lia. *)
        -- eapply trace_range in H17; eauto.
           simpl in H17.
           apply well_formed_range_r in H9; auto.
           lia.
         
        
      
        inv H1.
        discriminate H2.
        solve_by_inversion. *)
        
    + apply nodup_append; unfold disjoint_lists; auto; intros.
      *

        find_eapply_lem_hyp shuffle_nodup_append;
          unfold disjoint_lists; auto; intros;
            eauto.

        (*

        find_eapply_lem_hyp trace_range; eauto.


        apply shuffle_nodup_append in H18;
          unfold disjoint_lists; auto; intros.
        eapply IHt1; eauto.
        eapply IHt2; eauto.
        eapply trace_range in H16; eauto.
        eapply trace_range in H17; eauto. *)
        repeat tr_wf.
        simpl in *.
        lia.
      *
        do_nodup.
        (*

        apply NoDup_cons.
        intro HH.
        solve_by_inversion.
        constructor. *)
      *
        inv_in.
        (*

        inv H2. *)
        --
          find_eapply_lem_hyp shuffle_in; eauto;
            destruct_disjunct;
            repeat tr_wf;
              simpl in *;  
              try find_eapply_lem_hyp well_formed_range_r; eauto;
                simpl in * ;
                lia.

          (*
            
          (*

          eapply shuffle_in in H1; eauto.
           destruct H1. *)

          (*
           eapply trace_range in H16; eauto.
           simpl in H16. *)
           apply well_formed_range_r in H9; auto.
           lia.
           eapply trace_range in H17; eauto.
           simpl in H17.
           lia.
     
    

        -- solve_by_inversion.
           *)
*)
          
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
  forall t p tr ev0,
    well_formed_r t ->
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
  
 
  induction H0; inv_wfr; simpl in *;
    try expand_let_pairs; do_evin; simpl; auto;
      try (left; solve_by_inversion).

  (*
  - left. solve_by_inversion. *)
  -

    rewrite in_app_iff in *.
    right.
    do_evin; eauto.
    do_evin.
    try (try right; left; solve_by_inversion).

    (*
    right. simpl. eauto.
    +
    eauto.
    do_evin.
    
    (*

      apply IHtrace in H5; auto.
      rewrite in_app_iff; auto. *)
    + inv H5. rewrite in_app_iff.
      right. simpl. left. auto.
     *)
    
  -
    rewrite in_app_iff; auto.
    (*

    
    apply IHtrace1 in H5; auto.
    rewrite in_app_iff; auto. *)
  -
    rewrite in_app_iff; auto.

    (*

    apply IHtrace2 in H6; auto.
    rewrite in_app_iff; auto.
     *)
    

    (*
    
  - left. solve_by_inversion.
     *)

    (*
  - right.
    rewrite in_app_iff in *.
    do_evin; auto.

    (*


    inv H3; auto. *)
    +
      do_evin; auto;
        eauto.
      rewrite in_app_iff; auto.

      (*

      (*

      inv H4; auto. *)
      * apply IHtrace1 in H6; auto.
        rewrite in_app_iff; auto.
      * apply IHtrace2 in H7; auto.
        rewrite in_app_iff.
        right; rewrite in_app_iff; auto. *)
    +
      do_evin; auto.
      (*
      inv H4; auto. *)
      (repeat rewrite in_app_iff; right).
      right.
      left.
      auto.
      (*
      rewrite in_app_iff.
      right.
      simpl.
      auto.
      left.
      simpl.
      repeat (rewrite in_app_iff; right).
      simpl; left; auto. *)

      (*
      
  - left. solve_by_inversion.
       *)
      
  - right.

    do_evin; auto.
    (*

    inv H4; auto. *)
    +
      do_evin; auto.
      (*

      inv H5; auto. *)
      *
        repeat find_apply_hyp_hyp.
        (*
        apply IHtrace1 in H6; auto. *)
        do_shuf_l.

        (*
        

        
        find_eapply_lem_hyp shuffle_in_left
        eapply shuffle_in_left in H0; eauto. *)
        rewrite in_app_iff; auto.
      *
        find_eapply_hyp_hyp; auto.

        do_shuf_r.
        rewrite in_app_iff; auto.

        (*
        

        apply IHtrace2 in H6; auto.
        eapply shuffle_in_right in H0; eauto.
        rewrite in_app_iff; auto. *)
    +
      do_evin.
      (*
      inv H5. *)
      rewrite in_app_iff; right; simpl; auto.
      (*
      apply in_app_iff; right; simpl; auto. *)
*)
Qed.


(*
Ltac inv_step :=
  match goal with
  | H:step (?C _) _ _ |- _ => inv H
  end.


Ltac inv_traceS' :=
  match goal with
  | H:traceS _ _ |- _ => inv H
  end.
*)

Ltac inv_prec :=
  match goal with
  | H:prec (?C _) _ _ |- _ => inv H
  end.

(** The traces associated with an annotated term are compatible with
    its event system. *)

Theorem trace_order:
  forall t p tr ev0 ev1,
    well_formed_r t ->
    trace t p tr ->
    prec (ev_sys t p) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros t p tr ev0 ev1 H H0 H1.
  induction H0; inv H; simpl in H1;
    try expand_let_pairs;
    inv_prec; simpl; auto. 

 (* inv H1; simpl; auto. *)
  -
    Print do_evin.
    Ltac do_evin2 :=
      match goal with
      | [H:ev_in _ (?C _),
           H':ev_in _ (?D _)|- _] =>
         inv H; inv H'
      end.

    do_evin2.

    (*

    inv H12; inv H11. *)
    +
      find_eapply_lem_hyp evsys_tr_in; eauto.
      (*
      eapply evsys_tr_in in H4; eauto. *)
      apply earlier_cons; auto.
      apply in_app_iff; auto.
    +
      do_evin.
      (*
      inv H4. *)
      apply earlier_cons; auto.
      apply in_app_iff; auto; right; simpl; auto.
  - solve_by_inversion.
  -
    inv_prec.
    (*

    inv H11. *)
    +
      do_evin.
      (*

      inv H13. *)
      find_eapply_lem_hyp evsys_tr_in; eauto.
      (*
      eapply evsys_tr_in in H12; eauto. *)
      apply earlier_cons_shift; auto.
      apply earlier_append; auto; simpl; auto.
    +
      find_eapply_hyp_hyp; eauto.
      (*

      eapply IHtrace in H6; eauto. *)
      apply earlier_cons_shift; auto.
      apply earlier_left; auto.
    + solve_by_inversion.
  -
    find_eapply_lem_hyp evsys_tr_in; eauto.
    find_eapply_lem_hyp evsys_tr_in; eauto.

    (*
    eapply evsys_tr_in in H5; eauto.
    eapply evsys_tr_in in H6; eauto. *)
    apply earlier_append; auto.
  -
    find_apply_hyp_hyp; auto.

    (*
    apply IHtrace1 in H5; auto. *)
    apply earlier_left; auto.
  -
    find_apply_hyp_hyp; auto.
    (*

    apply IHtrace2 in H6; auto. *)
    apply earlier_right; auto.

    (*
  -
    do_evin2.
    (*

    inv H12; inv H11. *)
    +
      do_evin.
      (*

      inv H3. *)
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        (*

        eapply evsys_tr_in in H4; eauto. *)
        apply earlier_cons; auto.
        apply in_app_iff; auto.
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        
        apply earlier_cons; auto.
        (*

        
        eapply evsys_tr_in in H4; eauto.
        apply earlier_cons; auto. *)
        apply in_app_iff; right;
          apply in_app_iff; simpl; auto.
    +
      do_evin.
      (*

      inv H3. *)
      apply earlier_cons; auto.
      repeat (apply in_app_iff; right).
      simpl; auto.
  - solve_by_inversion.
    
  -
    inv_prec.
    (*

    inv H11. *)
    +
      do_evin2.
      (*

      inv H13. inv H12. *)
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        (*

        eapply evsys_tr_in in H3; eauto. *)
        apply earlier_cons_shift; auto.
        apply earlier_append; auto.
        apply in_app_iff; right; simpl; auto.
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        (*

        eapply evsys_tr_in in H3; eauto. *)
        apply earlier_cons_shift; auto.
        apply earlier_right; auto.
        apply earlier_append; simpl; auto.
    +
      inv_prec.
      (*

      inv H12. *)
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        find_eapply_lem_hyp evsys_tr_in; eauto.

        (*
        eapply evsys_tr_in in H14; eauto.
        eapply evsys_tr_in in H13; eauto. *)
        apply earlier_cons_shift; auto.
        apply earlier_append; auto.
        apply in_app_iff; left; auto.
      *
        find_apply_hyp_hyp; auto.
        (*

        apply IHtrace1 in H6; auto. *)
        apply earlier_cons_shift; auto.
        apply earlier_left; auto.
      *
        find_apply_hyp_hyp; auto.
        (*
        apply IHtrace2 in H7; auto. *)
        apply earlier_cons_shift; auto.
        apply earlier_right; auto.
        apply earlier_left; auto.
    + solve_by_inversion.
      
  -
    do_evin2.
    (*

    inv H7. inv H9. *)
    +
      do_evin;
        find_eapply_lem_hyp evsys_tr_in; eauto.
      (*
      
      inv H4; eapply evsys_tr_in in H5; eauto. *)
      * apply earlier_cons; auto.
        Check shuffle_in_left.
        find_eapply_lem_hyp shuffle_in_left.
        Focus 2.
        eauto.

        (*
        apply shuffle_in_left with
            (es1:=tr1)(es2:=tr2) in H5; auto.  *)
        erewrite in_app_iff; left; auto.
        (*
        eapply in_app_iff; left; auto. *)
      * apply earlier_cons; auto.
        find_eapply_lem_hyp shuffle_in_right.
        Focus 2.
        eauto.
        (*
        apply shuffle_in_right with (e:=ev1) in H0; auto. *)
        apply in_app_iff; left; auto.
    +
      do_evin.
      (*

      inv H4. *)
      apply earlier_cons; auto.
      apply in_app_iff; right; simpl; auto.
  - solve_by_inversion.
  -
    inv_prec.
    (*

    inv H7. *)
    +
      do_evin2.
      (*

      inv H15. inv H9. *)
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        (*

        eapply evsys_tr_in in H4; eauto. *)
        find_eapply_lem_hyp shuffle_in_left; eauto.
        (*
        apply shuffle_in_left with (e:= ev0) in H0; auto. *)
        apply earlier_cons_shift; auto.
        apply earlier_append; simpl; auto.
      *
        find_eapply_lem_hyp evsys_tr_in; eauto.
        find_eapply_lem_hyp shuffle_in_right; eauto.
        (*

        eapply evsys_tr_in in H4; eauto.
        apply shuffle_in_right with (e:=ev0) in H0; auto. *)
        apply earlier_cons_shift; auto.
        apply earlier_append; simpl; auto.
    +
      inv_prec.
      (*
      inv H9. *)
      *
        find_apply_hyp_hyp; auto.
        find_eapply_lem_hyp shuffle_earlier_left.
        Focus 2.
        eauto.
        (*
        apply IHtrace1 in H8; auto.
        apply shuffle_earlier_left
          with (e0:=ev0)(e1:=ev1) in H0; auto. *)
        
        apply earlier_cons_shift; auto.
        apply earlier_left; auto.
      *
        find_apply_hyp_hyp; auto.
        (*

        apply IHtrace2 in H10; auto. *)
        find_eapply_lem_hyp shuffle_earlier_right.
        Focus 2.
        eauto.
        (*
        apply shuffle_earlier_right
          with (e0:=ev0)(e1:=ev1) in H0; auto. *)
        apply earlier_cons_shift; auto.
        apply earlier_left; auto.
    + solve_by_inversion.
*)
Qed.

(* Copland specific event systems *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** Copland specific event systems. *)

Require Import Omega Preamble More_lists Term Event_system.

(** Construct an event system from an annotated term, place, and
    evidence. *)

Fixpoint ev_sys (t: AnnoTerm) : EvSys Ev :=
  match t with
  | aasp (i, j) x => leaf (i, j) (asp_event i x)
(*  | aatt (i, j) q x =>
    before (i, j)
      (leaf (i, S i) (req i q (unanno x)))
      (before (S i, j)
              (ev_sys x)
              (leaf (pred j, j) (rpy (pred j) q))) *)
  | alseq r x y => before r (ev_sys x)
                          (ev_sys y)
  | abseq (i, j) s x y =>
    before (i, j)
           (leaf (i, S i)
                 (split i ))
           (before (S i, j)
                   (before (S i, (pred j))
                           (ev_sys x)
                           (ev_sys y))
                   (leaf ((pred j), j)
                   (join (pred j) ))) (*
  | abpar (i, j) s x y =>
    before (i, j)
           (leaf (i, S i)
                 (split i ))
           (before (S i, j)
                   (merge (S i, (pred j))
                          (ev_sys x)
                          (ev_sys y))
                   (leaf ((pred j), j)
                   (join (pred j) ))) *)
  end.

Lemma evsys_range:
  forall t,
    es_range (ev_sys t) = range t.
Proof.
  induction t; intros; simpl; auto;
    repeat expand_let_pairs; simpl; auto.
Qed.

Lemma well_structured_evsys:
  forall t,
    well_formed t ->
    well_structured ev (ev_sys t).
Proof.
  induction t; intros; inv H; simpl;
    repeat expand_let_pairs; destruct r as [i k];
      simpl in *; subst; auto.
  - apply ws_leaf_event; auto;
      destruct a; simpl; auto.
(*  - apply ws_before; simpl; auto.
    rewrite H4.
    apply ws_before; simpl; auto; rewrite evsys_range; auto. *)
  - apply ws_before; auto; repeat rewrite evsys_range; auto.
    
  - repeat (apply ws_before; simpl in *; auto; repeat rewrite evsys_range; auto). (*
  - repeat (apply ws_before; simpl in *; auto; repeat rewrite evsys_range; auto).
    repeat (apply ws_merge; simpl in *; auto; repeat rewrite evsys_range; auto). *)
Qed.

(** The events in the event system correspond to the events associated
    with a term, a place, and some evidence. *)

Lemma evsys_events:
  forall t ev,
    well_formed t ->
    ev_in ev (ev_sys t) <-> events t ev.
Proof. (*
  split; induction t; intros; inv H; simpl in *;
    repeat expand_let_pairs; simpl in *.
  - inv H0; auto; destruct a; simpl; auto.
  - inv H0; auto.

  - inv H0; auto.
  - inv H0; auto.
    (*
    
    inv H2; auto.
    inv H2; auto.
    inv H1; auto.

    apply evtsattrpy. simpl. omega.
*)
    


(*
    rewrite H6 in H0; clear H6; simpl in H0.
    rewrite H5 in H0; clear H5; simpl in H0.
    inv H0. inv H2.
    inv H4; auto.
    econstructor. 


    auto. inv H2; auto.
    inv H1; auto. *)
  - inv H0; auto.
  - rewrite H9 in H0; simpl in H0.
    inv H0; inv H2; auto; inv H1; auto.
  - rewrite H9 in H0; simpl in H0.
    inv H0; inv H2; auto; inv H1; auto.
  - inv H0; auto.
  - inv H0; auto.




    rewrite H6; simpl.
    
    Print ev_in.
    apply ein_beforer.
    apply ein_beforer.
    assert (snd (range t) = i). omega.
    subst.
    apply ein_leaf.

  - inv H0; auto.
  - inv H0; auto.
    apply ein_beforer.
    apply ein_beforer.
    assert ((Init.Nat.pred (snd r) = i)). omega. subst.
    apply ein_leaf.

 -   inv H0; auto.
    apply ein_beforer.
    apply ein_beforer.
    assert ((Init.Nat.pred (snd r) = i)). omega. subst.
    apply ein_leaf. 
Qed. *)
Admitted.


(** Maximal events are unique. *)

Lemma supreme_unique:
  forall t,
    well_formed t ->
    exists ! v, supreme (ev_sys t) v.
Proof.
  (*
  intros.
  assert (G: well_structured ev (ev_sys t)).
  apply well_structured_evsys; auto.
  rewrite <- unique_existence.
  split.
  - exists (max (ev_sys t)).
    apply supreme_max with (ev:=ev); auto.
  - unfold uniqueness.
    intros.
    rewrite <- sup_supreme with (ev:=ev) in H0; auto.
    rewrite <- sup_supreme with (ev:=ev) in H1; auto.
    revert H1.
    revert H0.
    revert G.
    induction H; intros.
    + destruct r as [i j]; simpl in *.
      inv H0; inv H1; auto.
    + destruct r as [i j]; simpl in *.
      repeat apply before_sup in H2.
      repeat apply before_sup in H3.
      inv H2; inv H3; auto.
    + destruct r as [i j]; simpl in *.
      repeat apply before_sup in H4.
      repeat apply before_sup in H5.
      eapply IHwell_formed2 in H4; eauto.
      inv G; auto.
    + destruct r as [i j]; simpl in *.
      repeat apply before_sup in H4.
      repeat apply before_sup in H5.
      inv H4; inv H5; auto.
    + destruct r as [i j]; simpl in *.
      repeat apply before_sup in H4.
      repeat apply before_sup in H5.
      inv H4; inv H5; auto.
Qed. *)
Admitted.


Lemma evsys_max_unique:
  forall t,
    well_formed t ->
    unique (supreme (ev_sys t)) (max (ev_sys t)).
Proof.
  (*
  intros.
  assert (G: well_structured ev (ev_sys t)).
  apply well_structured_evsys; auto.
  unfold unique.
  split.
  apply supreme_max with (ev:=ev); auto.
  intros.
  rewrite <- sup_supreme with (ev:=ev) in H0; auto.
  revert H0.
  revert G.
  revert x'.
  induction H; intros; destruct r as [i j]; inv G; simpl in *; auto.
  - inv H0; auto.
  - repeat apply before_sup in H2.
    inv H2; auto.
  - repeat apply before_sup in H4.
    apply IHwell_formed2 in H4; auto.
  - repeat apply before_sup in H4.
    inv H4; auto.
  - repeat apply before_sup in H4.
    inv H4; auto.
Qed. *)
Admitted.


(** Maximal event evidence output matches [aeval]. *)

(*
Definition out_ev v :=
  match v with
  | copy _ _ e => e
  | kmeas _ _ _ _ _ e => e
  | umeas _ _ _ _ e => e
  | sign _ _ e => e
  | hash _ _ e => e
  | req _ _ _ t => mt
  | rpy _ _ _ e => e
  | split _ _ _ _ e => e
  | join _ _ _ _ e => e
  end.

Lemma max_eval:
  forall t p e,
    well_formed t ->
    out_ev (max (ev_sys t p e)) = aeval t p e.
Proof.
  intros.
  revert e.
  revert p.
  induction H; intros; simpl; repeat expand_let_pairs; simpl; auto.
  destruct x; simpl; auto.
Qed. *)

(** lseq is associative relative to the event semantics *)

Lemma lseq_assoc:
  forall t1 t2 t3 i,
    same_rel
      (ev_sys (snd (anno (lseq t1 (lseq t2 t3)) i)))
      (ev_sys (snd (anno (lseq (lseq t1 t2) t3) i))).
Proof.
  intros; simpl.
  repeat expand_let_pairs; simpl.
  apply before_associative_pairs.
Qed.

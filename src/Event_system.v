(* Abstract event systems:  strict partial orders of events. *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Import PeanoNat Lia Preamble.

Set Implicit Arguments.

(** An event system is a set of events and a strict partial order on
    the events.  An event system is represented by a well-structured
    [EvSys]. *)

Section Event_system.

  (** The sort of an event. *)

  Variable A: Type.

  (** The number associated with an event. *)

  Variable ev: A -> nat.

  Definition ES_Range : Type := nat * nat.

  (** An event system. *)

  Inductive EvSys :=
  | leaf: ES_Range -> A -> EvSys
  | before: ES_Range -> EvSys -> EvSys -> EvSys
  | merge: ES_Range -> EvSys -> EvSys -> EvSys.

  Definition es_range es :=
    match es with
    | leaf r _ => r
    | before r _ _ => r
    | merge r _ _ => r
    end.

  Fixpoint es_size es :=
    match es with
    | leaf _ _=> 1
    | before _ x y => es_size x + es_size y
    | merge _ x y => es_size x + es_size y
    end.

  (** Definition of a well-structured event system. *)

  Inductive well_structured: EvSys -> Prop :=
  | ws_leaf_event:
      forall r e,
        snd r = S (fst r) ->
        ev e = fst r ->
        well_structured (leaf r e)
  | ws_before:
      forall r x y,
        well_structured x ->
        well_structured y ->
        r = (fst (es_range x), snd (es_range y)) ->
        snd (es_range x) = fst (es_range y) ->
        well_structured (before r x y)
  | ws_merge:
      forall r x y,
        well_structured x ->
        well_structured y ->
        r = (fst (es_range x), snd (es_range y)) ->
        snd (es_range x) = fst (es_range y) ->
        well_structured (merge r x y).
  #[local] Hint Constructors well_structured : core.

  Lemma well_structured_range:
    forall es,
      well_structured es ->
      snd (es_range es) = fst (es_range es) + es_size es.
  Proof.
    induction es; simpl; intros; old_inv H; simpl; auto;
      try rewrite Nat.add_1_r; auto;
        apply IHes1 in H3;
        apply IHes2 in H4;
        lia.
  Qed.

  (** Is an event in an event system? *)

  Inductive ev_in: A -> EvSys -> Prop :=
  | ein_leaf: forall r ev,
      ev_in ev (leaf r ev)
  | ein_beforel: forall r ev es1 es2,
      ev_in ev es1 -> ev_in ev (before r es1 es2)
  | ein_beforer: forall r ev es1 es2,
      ev_in ev es2 -> ev_in ev (before r es1 es2)
  | ein_mergel: forall r ev es1 es2,
      ev_in ev es1 -> ev_in ev (merge r es1 es2)
  | ein_merger: forall r ev es1 es2,
      ev_in ev es2 -> ev_in ev (merge r es1 es2).
  #[local] Hint Constructors ev_in : core.

  (** Is one event before another? *)

  Inductive prec: EvSys -> A -> A -> Prop :=
  | prseq: forall r x y e f,
      ev_in e x -> ev_in f y ->
      prec (before r x y) e f
  | prseql: forall r x y e f,
      prec x e f ->
      prec (before r x y) e f
  | prseqr: forall r x y e f,
      prec y e f ->
      prec (before r x y) e f
  | prparl: forall r x y e f,
      prec x e f ->
      prec (merge r x y) e f
  | prparr: forall r x y e f,
      prec y e f ->
      prec (merge r x y) e f.
  #[local] Hint Constructors prec : core.

  Lemma prec_in_left:
    forall es ev1 ev2,
      prec es ev1 ev2 -> ev_in ev1 es.
  Proof.
    intros; induction H; auto.
  Qed.

  Lemma prec_in_right:
    forall es ev1 ev2,
      prec es ev1 ev2 -> ev_in ev2 es.
  Proof.
    intros; induction H; auto.
  Qed.

  Lemma ws_evsys_range:
    forall es e,
      well_structured es ->
      ev_in e es ->
      fst (es_range es) <= ev e < snd (es_range es).
  Proof.
    intros.
    pose proof H as G.
    apply well_structured_range in G.
    rewrite G.
    clear G.
    revert H0.
    revert e.
    induction es; intros; simpl in *; old_inv H; simpl in *;
      old_inv H0; simpl; try lia.
    - apply IHes1 in H2; auto; lia.
    - apply IHes2 in H2; auto.
      apply well_structured_range in H4.
      lia.
    - apply IHes1 in H2; auto; lia.
    - apply IHes2 in H2; auto.
      apply well_structured_range in H4.
      lia.
  Qed.

  Lemma es_injective_events:
    forall es ev0 ev1,
      well_structured es ->
      ev_in ev0 es -> ev_in ev1 es ->
      ev ev0 = ev ev1 ->
      ev0 = ev1.
  Proof.
    intros.
    revert H2.
    revert H1.
    revert H0.
    revert ev1.
    revert ev0.
    induction H; intros; simpl in *.
    - old_inv H1; old_inv H2; auto.
    - old_inv H3; old_inv H4.
      + eapply IHwell_structured1 in H8; eauto.
      + apply ws_evsys_range in H8; auto.
        apply ws_evsys_range in H6; auto.
        lia.
      + apply ws_evsys_range in H8; auto.
        apply ws_evsys_range in H6; auto.
        lia.
      + eapply IHwell_structured2 in H8; eauto.
    - old_inv H3; old_inv H4.
      + eapply IHwell_structured1 in H8; eauto.
      + apply ws_evsys_range in H8; auto.
        apply ws_evsys_range in H6; auto.
        lia.
      + apply ws_evsys_range in H8; auto.
        apply ws_evsys_range in H6; auto.
        lia.
      + eapply IHwell_structured2 in H8; eauto.
  Qed.

  (** A relation is a strict partial order iff it is irreflexive and
    transitive. *)

  Lemma evsys_irreflexive:
    forall es ev,
      well_structured es ->
      ~prec es ev ev.
  Proof.
    induction es; intros; intro; old_inv H; old_inv H0.
    - apply ws_evsys_range in H8; auto.
      apply ws_evsys_range in H9; auto.
      lia.
    - apply IHes1 in H8; auto.
    - apply IHes2 in H8; auto.
    - apply IHes1 in H8; auto.
    - apply IHes2 in H8; auto.
  Qed.

  Lemma evsys_transitive:
    forall es ev0 ev1 ev2,
      well_structured es ->
      prec es ev0 ev1 ->
      prec es ev1 ev2 ->
      prec es ev0 ev2.
  Proof.
    induction es; intros.
    - old_inv H0.
    - old_inv H.
      old_inv H0.
      + old_inv H1.
        * apply ws_evsys_range in H10; auto.
        * apply prec_in_left in H7.
          apply ws_evsys_range in H7; auto.
          apply ws_evsys_range in H10; auto.
          lia.
        * apply prec_in_right in H7; auto.
      + assert (G: ev_in ev0 es1). apply prec_in_left in H9; auto.
        assert (F: ev_in ev1 es1). apply prec_in_right in H9; auto.
        old_inv H1; auto.
        eapply IHes1 in H7; eauto.
        apply prseq; auto.
        apply prec_in_right in H7; auto.
      + assert (G: ev_in ev0 es2). apply prec_in_left in H9; auto.
        assert (F: ev_in ev1 es2). apply prec_in_right in H9; auto.
        old_inv H1.
        * apply ws_evsys_range in H7; auto.
          apply ws_evsys_range in F; auto.
          lia.
        * apply prec_in_left in H7.
          apply ws_evsys_range in H7; auto.
          apply ws_evsys_range in F; auto.
          lia.
        * eapply IHes2 in H7; eauto.
    - old_inv H.
      old_inv H0.
      + old_inv H1.
        * eapply IHes1 in H7; eauto.
        * apply prec_in_left in H7.
          apply prec_in_right in H9.
          apply ws_evsys_range in H9; auto.
          apply ws_evsys_range in H7; auto.
          lia.
      + assert (G: ev_in ev0 es2). apply prec_in_left in H9; auto.
        assert (F: ev_in ev1 es2). apply prec_in_right in H9; auto.
        old_inv H1.
        * apply prec_in_left in H7.
          apply ws_evsys_range in H7; auto.
          apply ws_evsys_range in F; auto.
          lia.
        * eapply IHes2 in H7; eauto.
  Qed.

  (** Merge is associative. *)

  Definition same_rel es0 es1 :=
    forall ev0 ev1,
      prec es0 ev0 ev1 <-> prec es1 ev0 ev1.

  Lemma ws_merge1:
    forall r s x y z,
      well_structured (merge r x y) ->
      well_structured (merge s y z) ->
      well_structured (merge (fst r, snd s) x (merge s y z)).
  Proof.
    intros r s x y z Hr Hs.
    old_inv Hr; old_inv Hs.
    constructor; simpl; auto; lia.
  Qed.

  Lemma ws_merge2:
    forall r s x y z,
      well_structured (merge r x y) ->
      well_structured (merge s y z) ->
      well_structured (merge (fst r, snd s) (merge r x y) z).
  Proof.
    intros r s x y z Hr Hs.
    old_inv Hr; old_inv Hs.
    constructor; simpl; auto; lia.
  Qed.

  Lemma merge_associative:
    forall r s x y z,
      same_rel (merge (fst r, snd s) x (merge s y z))
               (merge (fst r, snd s) (merge r x y) z).
  Proof.
    intros r s x y z.
    split; intro; old_inv H.
    - apply prparl; apply prparl; auto.
    - old_inv H5.
      + apply prparl; apply prparr; auto.
      + apply prparr; auto.
    - old_inv H5.
      + apply prparl; auto.
      + apply prparr; apply prparl; auto.
    - apply prparr; apply prparr; auto.
  Qed.

  (** A more useful form of merge associative *)

  Lemma merge_associative_pairs:
    forall r0 r1 s0 s1 x y z,
      same_rel (merge (r0, s1) x (merge (s0, s1) y z))
               (merge (r0, s1) (merge (r0, r1) x y) z).
  Proof.
    intros.
    apply merge_associative with (s:=(s0, s1))(r:=(r0,r1)).
  Qed.

  (** Before is associative. *)

  Lemma ws_before1:
    forall r s x y z,
      well_structured (before r x y) ->
      well_structured (before s y z) ->
      well_structured (before (fst r, snd s) x (before s y z)).
  Proof.
    intros r s x y z Hr Hs.
    old_inv Hr; old_inv Hs.
    constructor; simpl; auto; lia.
  Qed.

  Lemma ws_before2:
    forall r s x y z,
      well_structured (before r x y) ->
      well_structured (before s y z) ->
      well_structured (before (fst r, snd s) (before r x y) z).
  Proof.
    intros r s x y z Hr Hs.
    old_inv Hr; old_inv Hs.
    constructor; simpl; auto; lia.
  Qed.

  Lemma before_associative:
    forall r s x y z,
      same_rel (before (fst r, snd s) x (before s y z))
               (before (fst r, snd s) (before r x y) z).
  Proof.
    intros r s x y z.
    split; intro; old_inv H.
    - old_inv H6.
      + apply prseql; auto.
      + apply prseq; auto.
    - apply prseql; apply prseql; auto.
    - old_inv H5.
      + apply prseq; auto.
      + apply prseql; apply prseqr; auto.
      + apply prseqr; auto.
    - old_inv H5.
      + apply prseq; auto.
      + apply prseqr; apply prseq; auto.
    - old_inv H5.
      + apply prseq; auto.
      + apply prseql; auto.
      + apply prseqr; apply prseql; auto.
    - apply prseqr; apply prseqr; auto.
  Qed.

  Lemma before_associative_pairs:
    forall r0 r1 s0 s1 x y z,
      same_rel (before (r0, s1) x (before (s0, s1) y z))
               (before (r0, s1) (before (r0, r1) x y) z).
  Proof.
    intros.
    apply before_associative with (s:=(s0, s1))(r:=(r0,r1)).
  Qed.

  Lemma ws_exists:
    forall es,
      well_structured es ->
      exists e, ev_in e es.
  Proof.
    intros.
    induction H.
    - exists e; auto.
    - destruct IHwell_structured1 as [e].
      exists e; auto.
    - destruct IHwell_structured1 as [e].
      exists e; auto.
  Qed.

  (** Maximal events. *)

  Definition supreme es e :=
    ev_in e es /\ forall e0, ev_in e0 es -> ~prec es e e0.

  (** Inductive version of a maximal event. *)

  Inductive sup: EvSys -> A -> Prop :=
  | sup_leaf: forall r e, sup (leaf r e) e
  | sup_before:
      forall r es0 es1 e,
        sup es1 e -> sup (before r es0 es1) e
  | sup_mergel:
      forall r es0 es1 e,
        sup es0 e -> sup (merge r es0 es1) e
  | sup_merger:
      forall r es0 es1 e,
        sup es1 e -> sup (merge r es0 es1) e.
  #[local] Hint Constructors sup : core.

  Lemma before_sup:
    forall r x y e,
      sup (before r x y) e -> sup y e.
  Proof.
    intros.
    old_inv H.
    auto.
  Qed.

  Lemma sup_supreme:
    forall es e,
      well_structured es ->
      sup es e <-> supreme es e.
  Proof.
    unfold supreme; split.
    -  induction H; intros.
       + old_inv H1.
         split; auto; intros; intro.
         old_inv H1.
         apply evsys_irreflexive in H2; auto.
       + old_inv H1.
         old_inv H3.
         apply IHwell_structured2 in H7.
         destruct H7.
         split.
         * apply ein_beforer; auto.
         * intros; intro.
           old_inv H4; old_inv H5.
           -- apply ws_evsys_range in H8; auto.
              apply ws_evsys_range in H12; auto.
              lia.
           -- apply prec_in_left in H11.
              apply ws_evsys_range in H1; auto.
              apply ws_evsys_range in H11; auto.
              lia.
           -- apply prec_in_right in H11.
              apply ws_evsys_range in H8; auto.
              apply ws_evsys_range in H11; auto.
              lia.
           -- apply ws_evsys_range in H1; auto.
              apply ws_evsys_range in H11; auto.
              lia.
           -- apply prec_in_left in H11.
              apply ws_evsys_range in H1; auto.
              apply ws_evsys_range in H11; auto.
              lia.
           -- apply H3 in H8.
              tauto.
       + old_inv H3.
         * apply IHwell_structured1 in H8.
           destruct H8.
           split.
           -- apply ein_mergel; auto.
           -- intros; intro.
              old_inv H4; old_inv H5.
              ++ apply H3 in H8; tauto.
              ++ apply prec_in_right in H11.
                 apply ws_evsys_range in H8; auto.
                 apply ws_evsys_range in H11; auto.
                 lia.
              ++ apply prec_in_right in H11.
                 apply ws_evsys_range in H8; auto.
                 apply ws_evsys_range in H11; auto.
                 lia.
              ++ apply prec_in_left in H11.
                 apply ws_evsys_range in H1; auto.
                 apply ws_evsys_range in H11; auto.
                 lia.
         * apply IHwell_structured2 in H8.
           destruct H8.
           split.
           -- apply ein_merger; auto.
           -- intros; intro.
              old_inv H4; old_inv H5.
              ++ apply prec_in_left in H11.
                 apply ws_evsys_range in H1; auto.
                 apply ws_evsys_range in H11; auto.
                 lia.
              ++ apply prec_in_right in H11.
                 apply ws_evsys_range in H8; auto.
                 apply ws_evsys_range in H11; auto.
                 lia.
              ++ apply prec_in_left in H11.
                 apply ws_evsys_range in H1; auto.
                 apply ws_evsys_range in H11; auto.
                 lia.
              ++ apply H3 in H8; tauto.
    - intro; destruct H0.
      induction H; intros.
      + old_inv H0; auto.
      + old_inv H0; auto.
        * cut (exists f, ev_in f y).
          -- intros.
             destruct H0 as [f].
             specialize H1 with f.
             assert (G: prec
                          (before (fst (es_range x), snd (es_range y)) x y) e f).
             apply prseq; auto.
             apply H1 in G; auto.
             tauto.
          -- apply ws_exists; auto.
        * apply sup_before.
          apply IHwell_structured2; auto.
          intros; intro.
          assert (G: prec
                       (before (fst (es_range x), snd (es_range y)) x y) e e0).
          apply prseqr; auto.
          apply H1 in G; auto; tauto.
      + old_inv H0.
        * apply IHwell_structured1 in H7; auto.
          intros; intro.
          assert (G: prec
                       (merge (fst (es_range x), snd (es_range y)) x y) e e0).
          apply prparl; auto.
          apply H1 in G; auto; tauto.
        * apply IHwell_structured2 in H7; auto.
          intros; intro.
          assert (G: prec
                       (merge (fst (es_range x), snd (es_range y)) x y) e e0).
          apply prparr; auto.
          apply H1 in G; auto; tauto.
  Qed.

  (** Return one of possibly many maximal events. *)

  Fixpoint max es :=
    match es with
    | leaf _ e => e
    | before _ x y => max y
    | merge _ x y => max y
    end.

  Lemma supreme_max:
    forall es,
      well_structured es ->
      supreme es (max es).
  Proof.
    intros.
    apply sup_supreme; auto.
    induction H; auto.
  Qed.

End Event_system.

#[export] Hint Constructors well_structured ev_in prec sup : core.

Unset Implicit Arguments.

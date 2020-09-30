(* Facts about lists *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** More facts about lists. *)

Require Import List PeanoNat Compare_dec Lia.
Import List.ListNotations.
Open Scope list_scope.

Set Implicit Arguments.

Section More_lists.

  Variable A: Type.

  (** This is the analog of [firstn_app] from the List library. *)

  Lemma skipn_app n:
    forall l1 l2: list A,
      skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
  Proof. induction n as [|k iHk]; intros l1 l2.
    - now simpl.
    - destruct l1 as [|x xs].
      * unfold skipn at 2, length.
        repeat rewrite app_nil_l.
        rewrite <- Minus.minus_n_O.
        auto.
      * rewrite <- app_comm_cons. simpl. apply iHk.
  Qed.

  Lemma firstn_append:
    forall l l': list A,
      firstn (length l) (l ++ l') = l.
  Proof.
    induction l; intros; simpl; auto.
    rewrite IHl; auto.
  Qed.

  Lemma skipn_append:
    forall l l': list A,
      skipn (length l) (l ++ l') = l'.
  Proof.
    induction l; intros; simpl; auto.
  Qed.

  Lemma skipn_all:
    forall l: list A,
      skipn (length l) l = [].
  Proof.
    induction l; intros; simpl; auto.
  Qed.

  Lemma skipn_nil:
    forall i,
      @skipn A i [] = [].
  Proof.
    destruct i; simpl; auto.
  Qed.

  Lemma firstn_all_n:
    forall (l: list A) n,
      length l <= n ->
      firstn n l = l.
  Proof.
    induction l; intros; simpl.
    - rewrite firstn_nil; auto.
    - destruct n.
      simpl in H.
      lia.
      simpl in *.
      apply le_S_n in H.
      apply IHl in H.
      rewrite H; auto.
  Qed.

  Lemma skipn_all_n:
    forall (l: list A) n,
      length l <= n ->
      skipn n l = [].
  Proof.
    induction l; intros; simpl.
    - rewrite skipn_nil; auto.
    - destruct n; simpl in *.
      lia.
      apply le_S_n in H.
      apply IHl; auto.
  Qed.

  Lemma firstn_in:
    forall x i (l: list A),
      In x (firstn i l) ->
      In x l.
  Proof.
    induction i; intros.
    - simpl in H; tauto.
    - destruct l.
      + simpl in H; tauto.
      + simpl in H.
        destruct H.
        subst; simpl; auto.
        apply IHi in H.
        simpl; auto.
  Qed.

  Lemma skipn_in:
    forall x i (l: list A),
      In x (skipn i l) ->
      In x l.
  Proof.
    induction i; intros.
    - simpl in H; tauto.
    - destruct l.
      + simpl in H; tauto.
      + simpl in H.
        apply IHi in H.
        simpl; auto.
  Qed.

  Lemma skipn_zero:
    forall l: list A,
      skipn 0 l = l.
  Proof.
    destruct l; simpl; auto.
  Qed.

  Lemma in_skipn_cons:
    forall i x y (l: list A),
      In x (skipn i l) ->
      In x (skipn i (y :: l)).
  Proof.
    induction i; intros; simpl.
    - rewrite skipn_zero in H; auto.
    - destruct l.
      + simpl in H; tauto.
      + simpl in H; auto.
  Qed.

  (** Do [l] and [l'] share no elements? *)

  Definition disjoint_lists (l l': list A): Prop :=
    forall x, In x l -> In x l' -> False.

  Lemma nodup_append:
    forall l l': list A,
      NoDup l -> NoDup l' ->
      disjoint_lists l l' ->
      NoDup (l ++ l').
  Proof.
    intros.
    induction H.
    - rewrite app_nil_l; auto.
    - rewrite <- app_comm_cons.
      apply NoDup_cons.
      + intro.
        apply in_app_iff in H3.
        destruct H3; intuition.
        apply H1 in H3; try tauto; simpl; auto.
      + apply IHNoDup. unfold disjoint_lists; intros.
        apply H1 in H4; try tauto.
        simpl; auto.
  Qed.

  Lemma in_cons_app_cons:
    forall x y z (l: list A),
      In x (y :: l ++ [z]) <->
      x = y \/ In x l \/ x = z.
  Proof.
    intros.
    rewrite app_comm_cons.
    rewrite in_app_iff; simpl.
    intuition.
  Qed.

  (** * Earlier *)

  (** Is [x] earlier than [y] in list [l]?  This definition is used in
      contexts in which [l] has no duplicates. *)

  Definition earlier (l: list A) (x y: A) :=
    exists n,
      In x (firstn n l) /\
      In y (skipn n l).

  Lemma earlier_in_left:
    forall l x y,
      earlier l x y -> In x l.
  Proof.
    intros.
    destruct H as [i].
    destruct H.
    apply firstn_in in H; auto.
  Qed.

  Lemma earlier_in_right:
    forall l x y,
      earlier l x y -> In y l.
  Proof.
    intros.
    destruct H as [i].
    destruct H.
    apply skipn_in in H0; auto.
  Qed.

  (** [x] is earlier than [y] in [p ++ q] if [x] is earlier than [y]
      in [p].  *)

  Lemma earlier_left:
    forall p q x y,
      earlier p x y -> earlier (p ++ q) x y.
  Proof.
    intros.
    destruct H as [i].
    destruct H.
    exists i.
    split.
    - rewrite firstn_app.
      apply in_or_app.
      left; auto.
    - rewrite skipn_app.
      apply in_or_app.
      left; auto.
  Qed.

  (** [x] is earlier than [y] in [p ++ q] if [x] is earlier than [y]
      in [q].  *)

  Lemma earlier_right:
    forall p q x y,
      earlier q x y -> earlier (p ++ q) x y.
  Proof.
    intros.
    destruct H as [i].
    destruct H.
    exists (length p + i).
    assert (G: length p + i - length p = i).
    lia.
    split.
    - rewrite firstn_app.
      apply in_or_app.
      right.
      rewrite G; auto.
    - rewrite skipn_app.
      apply in_or_app.
      right.
      rewrite G; auto.
  Qed.

  Lemma earlier_append:
    forall p q x y,
      In x p -> In y q ->
      earlier (p ++ q) x y.
  Proof.
    intros.
    exists (length p).
    rewrite firstn_append.
    rewrite skipn_append.
    auto.
  Qed.

  Lemma earlier_append_iff:
    forall x y (l l': list A),
      earlier (l ++ l') x y <->
      earlier l x y \/ In x l /\ In y l' \/ earlier l' x y.
  Proof.
    split; intros.
    - destruct H as [i].
      destruct H.
      rewrite firstn_app in H.
      rewrite skipn_app in H0.
      pose proof (le_lt_dec i (length l)) as G.
      destruct G as [G|G].
      + rewrite <- Nat.sub_0_le in G; auto.
        rewrite G in *.
        simpl in *.
        rewrite app_nil_r in H.
        apply in_app_iff in H0.
        destruct H0.
        * left; exists i; auto.
        * right; left; split; auto.
          apply firstn_in in H; auto.
      + right.
        rewrite firstn_all_n in H; try lia.
        rewrite skipn_all_n in H0; try lia.
        rewrite app_nil_l in H0.
        apply in_app_iff in H.
        destruct H.
        * apply skipn_in in H0; auto.
        * right.
          exists (i - length l); auto.
    - destruct H.
      apply earlier_left; auto.
      destruct H.
      + destruct H.
        apply earlier_append; auto.
      + apply earlier_right; auto.
  Qed.

  Lemma earlier_cons:
    forall p x y,
      In y p ->
      earlier (x :: p) x y.
  Proof.
    intros; exists 1; simpl; auto.
  Qed.

  Lemma earlier_cons_shift:
    forall p x y z,
      earlier p x y ->
      earlier (z :: p) x y.
  Proof.
    intros.
    destruct H as [i].
    destruct H.
    exists (S i).
    simpl; auto.
  Qed.

End More_lists.

Unset Implicit Arguments.

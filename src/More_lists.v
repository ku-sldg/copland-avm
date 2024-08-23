(* Facts about lists *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** More facts about lists. *)

Require Import List Compare_dec Lia StructTactics.
Import List.ListNotations.
Open Scope list_scope.
Require Import StructTactics.

Set Implicit Arguments.

Section More_lists.

  Variable A: Type.

  (** This is the analog of [firstn_app] from the List library. *)

  Lemma skipn_app n: forall l1 l2: list A,
    skipn n (l1 ++ l2) = (skipn n l1) ++ (skipn (n - length l1) l2).
  Proof. 
    induction n; ff.
  Qed.

  Lemma firstn_append: forall l l': list A,
    firstn (length l) (l ++ l') = l.
  Proof.
    induction l; ff.
  Qed.

  Lemma skipn_append: forall l l': list A,
    skipn (length l) (l ++ l') = l'.
  Proof.
    induction l; ff.
  Qed.

  Lemma skipn_all: forall l: list A,
    skipn (length l) l = [].
  Proof.
    induction l; ff.
  Qed.

  Lemma skipn_nil: forall i,
    @skipn A i [] = [].
  Proof.
    induction i; ff.
  Qed.

  Lemma firstn_all_n: forall (l: list A) n,
    length l <= n ->
    firstn n l = l.
  Proof.
    induction l; ff;
    destruct n; ff;
    find_higher_order_rewrite; ffl.
  Qed.

  Lemma skipn_all_n: forall (l: list A) n,
    length l <= n ->
    skipn n l = [].
  Proof.
    induction l; ff;
    destruct n; ff;
    find_higher_order_rewrite; ffl.
  Qed.

  Lemma firstn_in: forall x i (l: list A),
    In x (firstn i l) ->
    In x l.
  Proof.
    induction i; ff.
  Qed.

  Lemma skipn_in: forall x i (l: list A),
    In x (skipn i l) ->
    In x l.
  Proof.
    induction i; ff.
  Qed.

  Lemma skipn_zero: forall l: list A,
    skipn 0 l = l.
  Proof.
    induction l; ff.
  Qed.

  Lemma in_skipn_cons: forall i x y (l: list A),
    In x (skipn i l) ->
    In x (skipn i (y :: l)).
  Proof.
    induction i; ff.
  Qed.

  (** Do [l] and [l'] share no elements? *)

  Definition disjoint_lists (l l': list A): Prop :=
    forall x, In x l -> In x l' -> False.

  Lemma nodup_append: forall l l': list A,
    NoDup l -> NoDup l' ->
    disjoint_lists l l' ->
    NoDup (l ++ l').
  Proof.
    intros; induction H; ff;
    econstructor; unfold disjoint_lists in *; ff;
    find_eapply_lem_hyp in_app_iff; ff.
  Qed.

  Lemma in_cons_app_cons:
    forall x y z (l: list A),
      In x (y :: l ++ [z]) <->
      x = y \/ In x l \/ x = z.
  Proof.
    ff; find_erewrite_lem in_app_iff; ff.
  Qed.

  (** * Earlier *)

  (** Is [x] earlier than [y] in list [l]?  This definition is used in
      contexts in which [l] has no duplicates. *)

  Definition earlier (l: list A) (x y: A) :=
    exists n,
      In x (firstn n l) /\
      In y (skipn n l).

  Lemma earlier_in_left: forall l x y,
    earlier l x y -> In x l.
  Proof.
    ff; unfold earlier in *; ff;
    find_eapply_lem_hyp firstn_in; ff.
  Qed.

  Lemma earlier_in_right: forall l x y,
    earlier l x y -> In y l.
  Proof.
    ff; unfold earlier in *; ff;
    find_eapply_lem_hyp skipn_in; ff.
  Qed.

  (** [x] is earlier than [y] in [p ++ q] if [x] is earlier than [y]
      in [p].  *)

  Lemma earlier_left: forall p q x y,
    earlier p x y -> earlier (p ++ q) x y.
  Proof.
    unfold earlier; ff; eexists;
    try erewrite firstn_app;
    try erewrite skipn_app;
    split; eapply in_or_app; ff.
  Qed.

  (** [x] is earlier than [y] in [p ++ q] if [x] is earlier than [y]
      in [q].  *)

  Lemma earlier_right: forall p q x y,
    earlier q x y -> earlier (p ++ q) x y.
  Proof.
    unfold earlier; ff; exists (length p + x0);
    try erewrite firstn_app;
    try erewrite skipn_app;
    split; eapply in_or_app; ff;
    assert (length p + x0 - length p = x0) by lia;
    ff.
  Qed.

  Lemma earlier_append: forall p q x y,
    In x p -> In y q ->
    earlier (p ++ q) x y.
  Proof.
    unfold earlier; ff; eexists;
    try erewrite firstn_append;
    try erewrite skipn_append; ff.
  Qed.

  Lemma earlier_cons: forall p x y,
    In y p ->
    earlier (x :: p) x y.
  Proof.
    unfold earlier; exists 1; ff.
  Qed.

  Lemma earlier_cons_shift: forall p x y z,
    earlier p x y ->
    earlier (z :: p) x y.
  Proof.
    unfold earlier; ff;
    exists (S x0); ff.
  Qed.

  Fixpoint true_last {A : Type} (l : list A) : option A :=
    match l with
    | nil => None
    | h' :: t' => 
      match true_last t' with
      | None => Some h'
      | Some x => Some x
      end
    end.

  Lemma true_last_none_iff_nil : forall A (l : list A),
    true_last l = None <-> l = nil.
  Proof.
    induction l; ff.
  Qed.

  Lemma true_last_app : forall A (l1 l2 : list A),
    l2 <> nil ->
    true_last (l1 ++ l2) = true_last l2.
  Proof.
    induction l1; ff;
    find_higher_order_rewrite; ff;
    find_eapply_lem_hyp true_last_none_iff_nil; ff.
  Qed.

  Lemma true_last_app_spec : forall A (l1 l2 : list A) x,
    true_last (l1 ++ l2) = Some x ->
    (true_last l1 = Some x /\ l2 = nil) \/ true_last l2 = Some x.
  Proof.
    induction l1; ff;
    find_eapply_lem_hyp true_last_none_iff_nil; ff;
    find_eapply_lem_hyp app_eq_nil; ff.
  Qed.

  Theorem list_length_app_cons : forall A (l1 l2 : list A) x x',
    l1 ++ [x] = x' :: l2 ->
    length (l1 ++ [x]) = length (x' :: l2).
  Proof.
    induction l1; ff.
  Qed.

End More_lists.

Unset Implicit Arguments.

(* Copland specific event systems *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** Copland specific event systems. *)

Require Import Preamble More_lists StructTactics Defs Term_Defs Term Event_system.

Require Import Lia List PeanoNat.

Search "succ".

Set Nested Proofs Allowed.

(** Construct an event system from an annotated term, place, and
    evidence. *)

Fixpoint ev_sys (t: AnnoTerm) p e: EvSys Ev :=
  match t with
  | aasp (i, j) x => leaf (i, j) (asp_event i x p e)
  | aatt (i, j) q x =>
    before (i, j)
      (leaf (i, S i) (req i p q (unanno x) e))
      (before (S i, j)
              (ev_sys x q e)
              (leaf (pred j, j) (rpy (pred j) p q (aeval x q e))))
  | alseq r x y => before r (ev_sys x p e)
                          (ev_sys y p (aeval x p e))
  | abseq (i, j) s x y =>
    before (i, j)
           (leaf (i, S i)
                 (Term_Defs.split i p))
           (before (S i, j)
                   (before (S i, (pred j))
                           (ev_sys x p (splitEv_T_l s e))
                           (ev_sys y p (splitEv_T_r s e)))
                   (leaf ((pred j), j)
                         (join (pred j) p)))
  | abpar (i, j) s x y =>
    before (i, j)
           (leaf (i, S i)
                 (Term_Defs.split i p))
           (before (S i, j)
                   (merge (S i, (pred j))
                           (ev_sys x p (splitEv_T_l s e))
                           (ev_sys y p (splitEv_T_r s e)))
                   (leaf ((pred j), j)
                         (join (pred j) p)))
  end.

Lemma evsys_range:
  forall t p e,
    es_range (ev_sys t p e) = range t.
Proof.
  induction t; intros; simpl; auto;
    repeat expand_let_pairs; simpl; auto.
Qed.

Ltac dest_range' :=
match goal with
| H:Range |- _ => destruct H
end.

Lemma well_structured_evsys:
  forall t p e,
    well_formed_r_annt t ->
    well_structured ev (ev_sys t p e).
Proof.
  induction t; intros; inv_wfr; simpl;
    repeat expand_let_pairs; dest_range'; (*destruct r as [i k]; *)
      simpl in *; subst; auto;
        try destruct a;
        repeat (econstructor; repeat rewrite evsys_range; auto).
Defined.

Ltac do_evin :=
  match goal with
  | [H:ev_in _ (?C _) |- _] => inv H
  end.

(** The events in the event system correspond to the events associated
    with a term, a place, and some evidence. *)

Search "succ".

Lemma evsys_events:
  forall t p e ev,
    well_formed_r_annt t ->
    ev_in ev (ev_sys t p e) <-> events t p e ev.
Proof.
  split; revert p; revert e; induction t; intros; inv_wfr; simpl in *;
    repeat expand_let_pairs; simpl in *;
      try (destruct a; auto; do_evin; auto; tauto);

      try (
          repeat dest_range;
          repeat (find_rewrite; simpl in * );
          repeat (do_evin; auto);
          inv_events; auto);
          
          repeat (find_rewrite; simpl in * );
          (find_apply_lem_hyp Nat.succ_inj  ) ; subst; auto;
            tauto.
Defined.

Ltac inv_sup :=
  match goal with
  | [H:sup (?C _) _ |- _] => inv H
  end.

Ltac do_before_sup :=
  match goal with
  | [H: sup (before _ _ _) _ |- _] =>
    repeat apply before_sup in H
  | [H: sup (ev_sys _ _ _) (* (alseq (n, n0) ls x y) p)*) _
     |- _] =>
    repeat apply before_sup in H
  end.

Ltac inv_ws :=
  match goal with
  | [H:well_structured _ (?C _) |- _] => inv H
  end.

(** Maximal events are unique. *)

Lemma supreme_unique:
  forall t p e,
    well_formed_r_annt t ->
    exists ! v, supreme (ev_sys t p e) v.
Proof.
  intros t p e H.
  assert (G: well_structured ev (ev_sys t p e)).
  apply well_structured_evsys; auto.
  rewrite <- unique_existence.
  split.
  - exists (max (ev_sys t p e)).
    eapply supreme_max (*with (ev:=ev);*); eauto.
  - unfold uniqueness.
    intros x y H0 H1.
    erewrite <- sup_supreme (*with (ev:=ev)*) in H0; eauto.
    erewrite <- sup_supreme (*with (ev:=ev)*) in H1; eauto.
    revert H1.
    revert H0.
    revert G.
    revert p.
    revert e.
    induction H; intros;
      try(
          repeat dest_range; simpl in *;
          repeat break_let;
          repeat do_before_sup;

          try (inv_ws; eauto; tauto);

          repeat inv_sup; auto;
          tauto).
Defined.

Lemma evsys_max_unique:
  forall t p e,
    well_formed_r_annt t ->
    unique (supreme (ev_sys t p e)) (max (ev_sys t p e)).
Proof.
  intros t p e H.
  assert (G: well_structured ev (ev_sys t p e)).
  apply well_structured_evsys; auto.
  unfold unique.
  split.
  apply supreme_max with (ev:=ev); auto.
  intros.
  rewrite <- sup_supreme with (ev:=ev) in H0; auto.
  revert H0.
  revert G.
  revert x'.
  revert p.
  revert e.
  induction H;
    intros;
    repeat dest_range;
    repeat expand_let_pairs;
    inv_ws.
  -
    repeat inv_sup; auto.
  -
    repeat inv_sup; auto.
  -
    cbn.
    apply IHwell_formed_r_annt2.
    eassumption.
    cbn in *.
    do_before_sup.
    eassumption.
  -
    repeat do_before_sup.
    solve_by_inversion.
  -
    do_before_sup.
    solve_by_inversion.
Qed.

(*
(** Maximal event evidence output matches [aeval]. *)

Definition out_ev v :=
  match v with
  | copy _ _ e => e
  | kmeas _ _ _ _ e => e
  | umeas _ _ _ _ e => e
  | sign _ _ _ e => e
  | hash _ _ _ e => e
  | req _ _ _ e => e
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
Qed.
*)

(** lseq is associative relative to the event semantics *)

Lemma lseq_assoc:
  forall t1 t2 t3 i p e n n' t' t'',
    anno (lseq t1 (lseq t2 t3)) i = (n, t') ->
    anno (lseq (lseq t1 t2) t3) i = (n',t'') ->
  
    same_rel
      (ev_sys t' p e)
      (ev_sys t'' p e).
Proof.
  intros; simpl.
  repeat expand_let_pairs; simpl.
  ff; repeat find_rewrite; ff.
  apply before_associative_pairs.
Qed.

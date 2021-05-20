(* Copland specific event systems *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** Copland specific event systems. *)

Require Import Preamble More_lists StructTactics Defs Term_Defs Term Event_system.

Require Import Omega Lia List.

Set Nested Proofs Allowed.

(** Construct an event system from an annotated term, place, and
    evidence. *)

Fixpoint ev_sys (t: AnnoTerm) p e: EvSys Ev :=
  match t with
  | aasp (i, j) x => leaf (i, j) (asp_event i x p)
  | aatt (i, j) q x =>
    before (i, j)
      (leaf (i, S i) (req i p q (unanno x) e))
      (before (S i, j)
              (ev_sys x q e)
              (leaf (pred j, j) (rpy (pred j) p q)))
  | alseq r x y => before r (ev_sys x p e)
                          (ev_sys y p (aeval x p e))
  | abseq (i, j) s x y =>
    before (i, j)
           (leaf (i, S i)
                 (Term_Defs.split i p))
           (before (S i, j)
                   (before (S i, (pred j))
                           (ev_sys x p (splitEv_T (fst s) e))
                           (ev_sys y p (splitEv_T (snd s) e)))
                   (leaf ((pred j), j)
                         (join (pred j) p)))
           (*
  | abpar (i, j) lr (*(xi,xi')*) (yi,yi') s x y =>
    before (i, j)
           (leaf (i, S i)
                 (splitp i (*xi*) yi p))
           (before (S i, j)
                   (merge (S i, (pred j))
                          (ev_sys x p)
                          (ev_sys y p))
                   (leaf ((pred j), j)
                   (joinp (pred j) (*xi'*) yi' yi' p)))
*)
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
    well_formed_r t ->
    well_structured ev (ev_sys t p e).
Proof.
  induction t; intros; inv_wfr; simpl;
    repeat expand_let_pairs; dest_range'; (*destruct r as [i k]; *)
      simpl in *; subst; auto;
        try destruct a;
        repeat (econstructor; repeat rewrite evsys_range; auto).
Defined.
(* 
  - repeat (apply ws_before; simpl in *; auto; repeat rewrite evsys_range; auto).
    repeat (apply ws_merge; simpl in *; auto; repeat rewrite evsys_range; auto).
Qed.
 *)

Ltac do_evin :=
  match goal with
  | [H:ev_in _ (?C _) |- _] => inv H
  end.

Ltac inv_events :=
  match goal with
  | [H:events (?C _) _ _ _ |- _] => inv H
  end.

(** The events in the event system correspond to the events associated
    with a term, a place, and some evidence. *)

Lemma evsys_events:
  forall t p e ev,
    well_formed_r t ->
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
          (find_apply_lem_hyp Nat.succ_inj) ; subst; auto;
            tauto.
  
  (*
      try (
          repeat dest_range;
          repeat find_rewrite; simpl in *;
          repeat (do_evin; auto);
          tauto);
      try (
          repeat (find_rewrite; simpl in * );
          inv_events; auto;
          repeat (find_rewrite; simpl in * );
          repeat (do_evin; auto);
          (find_apply_lem_hyp Nat.succ_inj) ; subst; auto;
          tauto).
*)
Defined.
(*

  (*
  -
    destruct a; simpl; auto; do_evin; auto.

    (*
    inv H0; auto; destruct a; simpl; auto. *)
   *)

  (*
  -

    dest_range.
    (*
    destruct p. *)
    repeat find_rewrite; simpl in *.
    (*
    rewrite H8 in H0; simpl in H0. *)

    repeat (do_evin; auto).
    (*
    inv H0; auto. inv H2; auto. inv H2; auto. inv H1; auto. *)
  - repeat (do_evin; auto).
    (*

    inv H0; auto. *)
    
  -
    repeat find_rewrite; simpl in *;
      repeat (do_evin; auto).
    (*

    rewrite H10 in H0; simpl in H0.
    inv H0; inv H2; auto; inv H1; auto. *)
    
  -

    repeat dest_range;
      repeat find_rewrite; simpl in *;
        repeat (do_evin; auto).

    (*

    destruct p; destruct p0.
    rewrite H12 in H0; simpl in H0.
    inv H0; auto. inv H2; auto. inv H2; auto. inv H1; auto. inv H1; auto. *)

*)
  -

    inv_events; auto.

  -
    repeat (find_rewrite; simpl in * ).
    inv_events; auto.
    repeat (find_rewrite; simpl in * ).

    

    find_apply_lem_hyp Nat.succ_inj; subst; auto.

            (*
            

    rewrite Nat.succ_inj in *.

    apply Nat.succ_inj in H7; subst; auto.

    rewrite H8; simpl.
    inv H0; auto.
    rewrite H11 in H8.
    apply Nat.succ_inj in H8; subst; auto. *)
  -
    inv_events; auto.
    (*

    inv H0; auto. *)
  -
    repeat (find_rewrite; simpl in * ).
    inv_events; auto.
    repeat (find_rewrite; simpl in * ).

    find_apply_lem_hyp Nat.succ_inj; subst; auto.
    (*
    

    rewrite H10; simpl.
    inv H0; auto.
    rewrite H12 in H10.
    apply Nat.succ_inj in H10; subst; auto. *)
    
  -
    repeat (find_rewrite; simpl in * );
    inv_events; auto;
    repeat (find_rewrite; simpl in * );
    (find_apply_lem_hyp Nat.succ_inj) ; subst; auto.

    (*
    rewrite H12; simpl.
    inv H0; auto.
    rewrite H15 in H12.
    apply Nat.succ_inj in H12; subst; auto. *)
Qed.
 *)

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
    well_formed_r t ->
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
(*

    (*
      try
        (
          repeat dest_range; simpl in *;
          repeat break_let;
          repeat do_before_sup;
          repeat inv_sup; auto; tauto).
*)
      
    +
      repeat dest_range; simpl in *;
        repeat break_let.
      repeat do_before_sup;
      repeat inv_sup; auto.

      (*


      destruct r as [i j]; simpl in *.
      inv H0; inv H1; auto. *)
    +
      repeat dest_range; simpl in *;
        repeat break_let;



      repeat do_before_sup;
      repeat inv_sup; auto.

      (*
          

      (*

      destruct r as [i j]; simpl in *.
      repeat expand_let_pairs. *)
      repeat apply before_sup in H3;
      repeat apply before_sup in H4;
     
      repeat inv_sup; auto.
      (*
      inv H3; inv H4; auto. *)
       *)
      
    +
      repeat dest_range; simpl in *;
        repeat break_let.

      repeat do_before_sup.

      (*
      (*

      destruct r as [i j]; simpl in *. *)
      repeat apply before_sup in H4.
      repeat apply before_sup in H5.
       *)

      inv_ws.
      eauto.

      

      (*
      invc G.
      eauto.
      
 
      eapply IHwell_formed_r2 in H4; eauto.
      solve_by_inversion.
       *)
      
      (*
      inv G; auto. *)
      
    +

      repeat dest_range; simpl in *;
        repeat break_let.

      
      repeat do_before_sup;
        repeat inv_sup; auto.

      (*

      (*

      destruct r as [i j]; simpl in *.
      repeat expand_let_pairs. *)
      repeat apply before_sup in H4.
      repeat apply before_sup in H5.
      repeat inv_sup; auto.
      (*
      inv H3; inv H4; auto. *)
*)


      (*

      destruct r as [i j]; simpl in *.
      repeat apply before_sup in H4.
      repeat apply before_sup in H5.
      inv H4; inv H5; auto. *)
      
    +
      repeat dest_range; simpl in *;
        repeat break_let.

      
      repeat do_before_sup;
      repeat inv_sup; auto.

      (*

      destruct r as [i j]; simpl in *.
      repeat expand_let_pairs. *)
      repeat apply before_sup in H5.
      repeat apply before_sup in H6.
      repeat inv_sup; auto.


      (*
      destruct r as [i j]; simpl in *.
      repeat expand_let_pairs.
      repeat apply before_sup in H5.
      repeat apply before_sup in H6.
      inv H5; inv H6; auto. *)
Qed.
*)

Lemma evsys_max_unique:
  forall t p e,
    well_formed_r t ->
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
    try destruct locs;
    inv_ws;
    try destruct locs.
   (* repeat find_rewrite; *)

    (*
    repeat do_before_sup;
    try (eauto; tauto) *)
    

  -
  repeat inv_sup; auto.

  

(*
      repeat expand_let_pairs; simpl in *; auto;
        try(
          repeat dest_range; simpl in *;
          repeat break_let;
          repeat do_before_sup;

          try (inv_ws; eauto; tauto);

          repeat inv_sup; auto;
          tauto)
 *)
  (*
  -

    inv H0; auto. *)
  -

    repeat inv_sup; auto.

    (*

    repeat expand_let_pairs.
    repeat apply before_sup in H3.
    inv H3; auto. *)
  -
    cbn.
    apply IHwell_formed_r2.
    eassumption.
    cbn in *.
    do_before_sup.
    eassumption.

    (*

    

   
    
    repeat apply before_sup in H4; auto.

    
    
    
    apply IHwell_formed_r2 in H4; auto. *)

    
  -
    repeat do_before_sup.
    solve_by_inversion.

    (*

    repeat apply before_sup in H4.
    solve_by_inversion.
    (*
    inv H4; auto. *)
*)
    (*
  -
    do_before_sup.
    solve_by_inversion.

    (*

    repeat expand_let_pairs.
    repeat apply before_sup in H5.
    inv H5; auto. *)

    (*
  -
     do_before_sup.
    solve_by_inversion.
    repeat expand_let_pairs.
    repeat apply before_sup in H5.
    inv H5; auto.
  -
    repeat expand_let_pairs.
    inv H6; eauto.
*)
*)
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

(*

Lemma firstn_gt: forall (ls: list nat) m n,
    m >= n ->
    firstn n (firstn m ls) = firstn n ls.
Proof.
  Search (firstn _ (firstn _ _)).

  intros.
  pose firstn_firstn.
  pose (e nat ls n m).
  assert (Init.Nat.min n m = n).
  {
    lia.
  }
  congruence.
Defined.

Lemma skipn_firstn_len: forall (ls:list nat) n m,
    (firstn n (skipn m ls)) =
    (skipn m (firstn (m + n) ls)).
Proof.
  intros.
  Search (firstn (_ + _)).
  eapply firstn_skipn_comm.
Defined.

Lemma skipn_assoc: forall (ls:list nat) n m,
    (skipn n (skipn m ls)) =
    (skipn (m + n) ls).
Proof.
  induction ls; intros.
  -
    repeat rewrite skipn_nil.
    tauto.
  -
    ff'.
    destruct m.
    +
      ff'.
    +
      ff'.
Defined.
*)


(*
Lemma lseq_assoc:
  forall t1 t2 t3 i p ls b n n' t' t'',
    anno (lseq t1 (lseq t2 t3)) i ls b = Some (n, t') ->
    anno (lseq (lseq t1 t2) t3) i ls b = Some (n',t'') ->
  
    same_rel
      (ev_sys t' p)
      (ev_sys t'' p).
Proof.
  intros; simpl.
  repeat expand_let_pairs; simpl.
  ff.
  Check before_associative_pairs.
  ff'.
  assert ((List.firstn (nss t1) (List.firstn (nss t1 + nss t2) ls)) =
          (List.firstn (nss t1) ls)) as HH.
  {
    eapply firstn_gt; lia.
  }
  
  rewrite HH in *; clear HH.

  rewrite Heqo3 in *; clear Heqo3.

  ff.

  assert (
      (List.firstn (nss t2) (List.skipn (nss t1) ls)) =
      (List.skipn (nss t1) (List.firstn (nss t1 + nss t2) ls))) as HH.
  {
    eapply skipn_firstn_len.
  }

  ff.

  repeat find_rewrite.

  (*
  
  rewrite HH in *; clear HH.

  rewrite Heqo2 in *; clear Heqo2. *)
  ff.


  

  assert (
      (List.skipn (nss t2) (List.skipn (nss t1) ls)) =
      (List.skipn (nss t1 + nss t2) ls)) as HHH.
  {
    eapply skipn_assoc.
  }

  

  repeat find_rewrite.

  invc Heqo0.
  
  (*
  repeat find_inversion.
  ff.

  rewrite HH in *; clear HH.

  rewrite Heqo0 in *; clear Heqo0.
  ff.     
   *)
  
  (*
  rewrite Heqo0 in *. *)
  (*
  inv Heqo4. *)
  apply before_associative_pairs.
Qed.

*)

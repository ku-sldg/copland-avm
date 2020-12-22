(* Small-step semantics *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** A small-step semantics for annotated terms. *)

Require Import List.
Import List.ListNotations.
Open Scope list_scope.
Require Import PeanoNat Minus Lia Preamble Term Store_system.

(** * States *)

Inductive St: Set :=
| stop: (*Plc -> Evidence ->*) St
| conf: AnnoTerm -> (*Plc -> Evidence ->*) St
| rem: (*Plc -> Plc ->*) St -> St
| ls: St -> AnnoTerm -> St
| bsl: nat -> St -> AnnoTerm -> (*Plc -> Evidence ->*) St
| bsr: nat -> (*Evidence ->*) St -> St
| bp: nat -> St -> St -> St
| bpl: St -> St
| bpr: St -> St.

(*
Fixpoint pl (s:St) :=
  match s with
  | stop p _ => p
  | conf _ p _ => p
  | rem _ p _ => p
  | ls st _ => pl st
  | bsl _ _ _ p _ => p
  | bsr _ _ st => pl st
  | bp _ _ st => pl st
  end.

(** The evidence associated with a state. *)

Fixpoint seval st :=
  match st with
  | stop _ e => e
  | conf t p e => aeval t p e
  | rem _ _ st => seval st
  | ls st t => aeval t (pl st) (seval st)
  | bsl _ st t p e => ss (seval st) (aeval t p e)
  | bsr _ e st => ss e (seval st)
  | bp _ st0 st1 => pp (seval st0) (seval st1)
end.
*)

(** * Labeled Transition System

    The label in a transition is either an event or [None] when the
    transition is silent.  Notice the use of annotations to provide
    the correct number for each event.  *)

Inductive step: St -> option PutPoll -> St -> Prop :=
(** Measurement *)

| stasp:
    forall r x,
      step (conf (aasp r x))
           (Some none_putpoll)
           (stop)
(** Remote call *)

| statt:
    forall r x q,
      step (conf (aatt r q x))
           (Some (putpoll (fst r) (fst r) (snd r)))
           (rem (conf x))
| stattstep:
    forall st0 st1 ev,
      step st0 ev st1 ->
      step (rem st0) ev (rem st1)
| stattstop:
   
      step (rem (stop))
           None
           (stop)
(** Linear Sequential Composition *)

| stlseq:
    forall r x y,
      step (conf (alseq r x y))
           None
           (ls (conf x) y)
| stlseqstep:
    forall st0 ev st1 t,
      step st0 ev st1 ->
      step (ls st0 t) ev (ls st1 t)
| stlseqstop:
    forall t,
      step (ls (stop) t) None (conf t)
(** Branching Sequential Composition *)

| stbseq:
    forall r s x y,
      step (conf (abseq r s x y))
           None
           (bsl (snd r) (conf x)
                y)
| stbslstep:
    forall st0 ev st1 j t,
      step st0 ev st1 ->
      step (bsl j st0 t) ev (bsl j st1 t)
| stbslstop:
    forall j t,
      step (bsl j (stop) t)
           None
           (bsr j (conf t))
| stbsrstep:
    forall st0 ev st1 j,
      step st0 ev st1 ->
      step (bsr j st0) ev (bsr j st1)
| stbsrstop:
    forall j,
      step (bsr j (stop))
           None
           (stop)

(** Branching Parallel composition *)

| stbpar:
    forall r s x y,
      step (conf (abpar r s x y))
           (*(Some (putpoll (fst (range x)) (fst (range x)) (snd (range x) - 1))) *)
           None
           (bp (snd r)
               (bpl (conf x))
               (bpr (conf y)))
| stbparl: forall x,
    step (bpl (conf x))
         (Some (putpoll (fst (range x)) (fst (range x)) (snd (range x) - 1)))
         (conf x)
| stbparr: forall y,
    step (bpr (conf y))
         (Some (putpoll (fst (range y)) (fst (range y)) (snd (range y) - 1)))
         (conf y)
                             
| stbpstepleft:
    forall st0 st1 st2 ev j,
      step st0 ev st2 ->
      step (bp j st0 st1) ev (bp j st2 st1)
| stbpstepright:
    forall st0 st1 st2 ev j,
      step st1 ev st2 ->
      step (bp j st0 st1) ev (bp j st0 st2)
| stbpstop:
    forall j,
      step (bp j (stop) (stop))
           None
           (stop).
Hint Constructors step : core.

(*
(** A step preserves place. *)

Lemma step_pl_eq:
  forall st0 ev st1,
    step st0 ev st1 -> pl st0 = pl st1.
Proof.
  intros.
  induction H; simpl; auto.
Qed.

(** A step preserves evidence. *)

Lemma step_seval:
  forall st0 ev st1,
    step st0 ev st1 ->
    seval st0 = seval st1.
Proof.
  intros.
  induction H; simpl; auto; try rewrite IHstep; auto.
  apply step_pl_eq in H. rewrite H; auto.
Qed.
*)

(** * Transitive Closures *)

Inductive lstar: St -> list PutPoll -> St -> Prop :=
| lstar_refl: forall st, lstar st [] st
| lstar_tran: forall st0 e st1 tr st2,
    step st0 (Some e) st1 -> lstar st1 tr st2 -> lstar st0 (e :: tr) st2
| lstar_silent_tran: forall st0 st1 tr st2,
    step st0 None st1 -> lstar st1 tr st2 -> lstar st0 tr st2.
Hint Resolve lstar_refl : core.

Lemma lstar_transitive:
  forall st0 tr0 st1 tr1 st2,
    lstar st0 tr0 st1 ->
    lstar st1 tr1 st2 ->
    lstar st0 (tr0 ++ tr1) st2.
Proof.
  intros.
  induction H.
  - rewrite app_nil_l; auto.
  - apply IHlstar in H0.
    rewrite <- app_comm_cons.
    eapply lstar_tran; eauto.
  - apply IHlstar in H0.
    eapply lstar_silent_tran; eauto.
Qed.

(** Transitive closure without labels. *)

Inductive star: St -> St -> Prop :=
| star_refl: forall st, star st st
| star_tran: forall st0 e st1 st2,
    step st0 e st1 -> star st1 st2 -> star st0 st2.
Hint Resolve star_refl : core.

Lemma star_transitive:
  forall st0 st1 st2,
    star st0 st1 ->
    star st1 st2 ->
    star st0 st2.
Proof.
  intros.
  induction H; auto.
  apply IHstar in H0.
  eapply star_tran; eauto.
Qed.

Lemma lstar_star:
  forall st0 tr st1,
    lstar st0 tr st1 -> star st0 st1.
Proof.
  intros.
  induction H; auto;
    eapply star_tran; eauto.
Qed.

Lemma star_lstar:
  forall st0 st1,
    star st0 st1 -> exists tr, lstar st0 tr st1.
Proof.
  intros.
  induction H; auto.
  - exists []; auto.
  - destruct IHstar as [tr G].
    destruct e.
    + exists (p :: tr).
      eapply lstar_tran; eauto.
    + exists tr.
      eapply lstar_silent_tran; eauto.
Qed.

(*
Lemma star_seval:
  forall st0 st1,
    star st0 st1 -> seval st0 = seval st1.
Proof.
  intros.
  induction H; auto.
  apply step_seval in H; auto.
  rewrite H; auto.
Qed.

Lemma steps_preserves_eval:
  forall t p p' e0 e1,
    star (conf t p e0) (stop p' e1) ->
    aeval t p e0 = e1.
Proof.
  intros.
  apply star_seval in H.
  simpl in H; auto.
Qed.
*)

(** * Correct Path Exists *)

Lemma star_strem:
  forall st0 st1,
    star st0 st1 -> star (rem st0) (rem st1).
Proof.
  intros.
  induction H; auto.
  eapply star_tran; eauto.
Qed.

Lemma star_stls:
  forall st0 st1 t,
    star st0 st1 -> star (ls st0 t) (ls st1 t).
Proof.
  intros.
  induction H; auto.
  eapply star_tran; eauto.
Qed.


Lemma star_stbsl:
  forall st0 st1 j t,
    star st0 st1 ->
    star (bsl j st0 t) (bsl j st1 t).
Proof.
  intros.
  induction H; auto.
  eapply star_tran; eauto.
Qed.

Lemma star_stbsr:
  forall st0 st1 j,
    star st0 st1 ->
    star (bsr j st0) (bsr j st1).
Proof.
  intros.
  induction H; auto.
  eapply star_tran; eauto.
Qed.

(* Congruence lemmas for Copland LTS semantics *)
Lemma lstar_stls :
  forall st0 st1 t tr,
    lstar st0 tr st1 -> lstar (ls st0 t) tr (ls st1 t).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Qed.

Lemma lstar_strem : forall st st' tr,
    lstar st tr
          st' ->
    lstar (rem st) tr (rem st').
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma lstar_stbsl:
  forall st0 st1 j t tr,
    lstar st0 tr st1 ->
    lstar (bsl j st0 t) tr (bsl j st1 t).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma lstar_stbsr:
  forall st0 st1 j tr,
    lstar st0 tr st1 ->
    lstar (bsr j st0) tr (bsr j st1).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma star_stbp:
  forall st0 st1 st2 st3 j,
    star st0 st1 ->
    star st2 st3 ->
    star (bp j st0 st2) (bp j st1 st3).
Proof.
  intros.
  induction H; auto.
  - induction H0; auto.
    eapply star_tran; eauto.
  - eapply star_tran; eauto.
Qed.

Theorem correct_path_exists:
  forall t,
    star (conf t) (stop).
Proof.
  induction t; intros; simpl; eauto.
  - eapply star_tran; eauto.
  - eapply star_tran; eauto.
    eapply star_transitive.
    apply star_strem.
    apply IHt.
    eapply star_tran; eauto.
  - eapply star_tran; eauto.
    eapply star_transitive.
    apply star_stls.
    apply IHt1.
    eapply star_tran; eauto.
    
  - eapply star_tran; eauto.
    eapply star_transitive.
    apply star_stbsl.
    apply IHt1.
    eapply star_tran; eauto.
    eapply star_transitive.
    apply star_stbsr.
    apply IHt2.
    eapply star_tran; eauto.
  - eapply star_tran.
    apply stbpar.
    eapply star_tran.
    eapply stbpstepleft.
    eauto.
    eapply star_tran.
    eapply stbpstepright.
    eauto.
    
    eapply star_transitive.
    (*
    eapply stbparl.
    eapply star_tran.
    apply stbparr.
    eapply star_transitive.   *)
    apply star_stbp.
    apply IHt1.
    apply IHt2.
    eapply star_tran; eauto.
Qed.


(** * Progress *)

Definition halt st :=
  match st with
  | stop => True
  | _ => False
  end.

(*

(** The step relation nevers gets stuck. *)

Theorem never_stuck:
  forall st0,
    halt st0 \/ exists e st1, step st0 e st1.
Proof.
  induction st0.
  - left; simpl; auto.
  - right.
    destruct a.
    + exists (Some none_putpoll).
      eapply ex_intro; eauto.
    + exists (Some (putpoll (fst r) (fst r) (snd r))).
      eapply ex_intro; eauto.
    + exists None.
      eapply ex_intro; eauto.
      
    + exists None.
      eapply ex_intro; eauto.
      
    + exists None.
      eapply ex_intro; eauto.
  - right.
    destruct IHst0.
    + destruct st0; simpl in H; try tauto.
      exists None.
      eapply ex_intro; eauto.
    + destruct H as [e H].
      exists e.
      destruct H as [st1 H].
      exists (rem st1). auto.
  - right.
    destruct IHst0.
    + destruct st0; simpl in H; try tauto.
      exists None. eapply ex_intro; eauto.
    + destruct H as [e H].
      exists e.
      destruct H as [st H].
      exists (ls st a). auto.
      
  - right.
    destruct IHst0.
    + destruct st0; simpl in H; try tauto.
      exists None. eapply ex_intro; eauto.
    + destruct H as [e0 H].
      exists e0.
      destruct H as [st H].
      exists (bsl n st a). auto.
  - right.
    destruct IHst0.
    + destruct st0; simpl in H; try tauto.
      exists None.
      eapply ex_intro; eauto.
    + destruct H as [e0 H].
      exists e0.
      destruct H as [st H].
      exists (bsr n st). auto.
      
  - right.
    destruct IHst0_1 as [H|H].
    + destruct st0_1; simpl in H; try tauto.
      clear H.
      destruct IHst0_2.
      * destruct st0_2; simpl in H; try tauto.
        exists None.
        eapply ex_intro; eauto.
      * destruct H as [e0 H].
        exists e0.
        destruct H as [st H].
        exists (bp n (stop) st). auto.
    + destruct H as [e0 H].
      exists e0.
      destruct H as [st H].
      exists (bp n st st0_2). auto.
  -
    right.
    destruct IHst0 as [H|H].
    +
      unfold halt in H. destruct st0; try contradiction.
      exists (Some (putpoll (fst (range x)) (fst (range x)) (snd (range x) - 1))).
    
    
      
Qed.
*)

(** * Termination *)

Inductive nstar: nat -> St -> St -> Prop :=
| nstar_refl: forall st, nstar 0 st st
| nstar_tran: forall st0 st1 st2 e n,
    nstar n st0 st1 -> step st1 e st2 -> nstar (S n) st0 st2.
Hint Resolve nstar_refl : core.

Lemma nstar_transitive:
  forall m n st0 st1 st2,
    nstar m st0 st1 ->
    nstar n st1 st2 ->
    nstar (m + n) st0 st2.
Proof.
  intros.
  induction H0.
  rewrite Nat.add_0_r; auto.
  apply IHnstar in H.
  eapply nstar_tran in H; eauto.
  rewrite plus_n_Sm in H.
  eauto.
Qed.

Lemma nstar_star:
  forall n st0 st1,
    nstar n st0 st1 -> star st0 st1.
Proof.
  intros.
  induction H; auto.
  eapply star_transitive; eauto.
  eapply star_tran; eauto.
Qed.

Lemma star_nstar:
  forall st0 st1,
    star st0 st1 ->
    exists n, nstar n st0 st1.
Proof.
  intros.
  induction H.
  - exists 0; auto.
  - destruct IHstar as [n G].
    exists (S n).
    rewrite <- Nat.add_1_l.
    eapply nstar_transitive; eauto.
    eapply nstar_tran; eauto.
Qed.

(** Size of a term (number of steps to reduce). *)

Fixpoint tsize t: nat :=
  match t with
  | aasp _ _ => 1
  | aatt _ _ x => 2 + tsize x
  | alseq _ x y => 2 + tsize x + tsize y
  | abseq _ _ x y => 3 + tsize x + tsize y
  | abpar _ _ x y => 4 + tsize x + tsize y
  end.

(** Size of a state (number of steps to reduce). *)

Fixpoint ssize s: nat :=
  match s with
  | stop => 0
  | conf t => tsize t
  | rem x => 1 + ssize x
  | ls x t => 1 + ssize x + tsize t
  | bsl _ x t => 2 + ssize x + tsize t
  | bsr _ x => 1 + ssize x
  | bp _ x y => 1 + ssize x + ssize y
  | bpl x => 1 + ssize x
  | bpr y => 1 + ssize y
  end.

(** Halt state has size 0. *)

Lemma halt_size:
  forall st,
    halt st <-> ssize st = 0.
Proof.
  split; intros.
  - destruct st; simpl in H; try tauto.
  - destruct st; simpl in H; try tauto;
      try discriminate.
    + simpl; auto.
    + destruct a; simpl in H; discriminate.
Qed.

(** A state decreases its size by one. *)

Lemma step_size:
  forall st0 e st1,
    step st0 e st1 ->
    S (ssize st1) = ssize st0.
Proof.
  intros.
  induction H; try (simpl; auto; lia).
Qed.

Lemma step_count:
  forall n t st,
    nstar n (conf t) st ->
    tsize t = n + ssize st.
Proof.
  induction n; intros.
  - inv H; simpl; auto.
  - inv H.
    apply IHn in H1.
    rewrite H1.
    apply step_size in H2.
    lia.
Qed.

(** Every run terminates. *)

Theorem steps_to_stop:
  forall t st,
    nstar (tsize t) (conf t) st ->
    halt st.
Proof.
  intros.
  apply step_count in H.
  apply halt_size.
  lia.
Qed.

(** * Numbered Labeled Transitions *)

Inductive nlstar: nat -> St -> list PutPoll -> St -> Prop :=
| nlstar_refl: forall st, nlstar 0 st [] st
| nlstar_tran: forall n st0 e st1 tr st2,
    step st0 (Some e) st1 -> nlstar n st1 tr st2 -> nlstar (S n) st0 (e :: tr) st2
| nlstar_silent_tran: forall n st0 st1 tr st2,
    step st0 None st1 -> nlstar n st1 tr st2 -> nlstar (S n) st0 tr st2.
Hint Resolve nlstar_refl : core.

Lemma nlstar_transitive:
  forall m n st0 tr0 st1 tr1 st2,
    nlstar m st0 tr0 st1 ->
    nlstar n st1 tr1 st2 ->
    nlstar (m + n) st0 (tr0 ++ tr1) st2.
Proof.
  intros.
  induction H.
  - rewrite app_nil_l; auto.
  - apply IHnlstar in H0.
    rewrite <- app_comm_cons.
    eapply nlstar_tran; eauto.
  - apply IHnlstar in H0.
    eapply nlstar_silent_tran; eauto.
Qed.

Lemma nlstar_lstar:
  forall n st0 tr st1,
    nlstar n st0 tr st1 -> lstar st0 tr st1.
Proof.
  intros.
  induction H; auto.
  - eapply lstar_tran; eauto.
  - eapply lstar_silent_tran; eauto.
Qed.

Lemma lstar_nlstar:
  forall st0 tr st1,
    lstar st0 tr st1 ->
    exists n, nlstar n st0 tr st1.
Proof.
  intros.
  induction H.
  - exists 0; auto.
  - destruct IHlstar as [n G].
    exists (S n).
    eapply nlstar_tran; eauto.
  - destruct IHlstar as [n G].
    exists (S n).
    eapply nlstar_silent_tran; eauto.
Qed.

Lemma nlstar_step_size:
  forall n st0 tr st1,
    nlstar n st0 tr st1 ->
    ssize st1 <= ssize st0.
Proof.
  intros.
  induction H; auto;
    apply step_size in H;
    lia.
Qed.

Lemma lstar_nlstar_size:
  forall st0 tr st1,
    lstar st0 tr st1 ->
    nlstar (ssize st0 - ssize st1) st0 tr st1.
Proof.
  intros.
  induction H.
  - rewrite Nat.sub_diag; auto.
  - pose proof H as G.
    apply step_size in G.
    rewrite <- G.
    rewrite <- minus_Sn_m.
    + eapply nlstar_tran; eauto.
    + apply nlstar_step_size in IHlstar; auto.
  - pose proof H as G.
    apply step_size in G.
    rewrite <- G.
    rewrite <- minus_Sn_m.
    + eapply nlstar_silent_tran; eauto.
    + apply nlstar_step_size in IHlstar; auto.
Qed.

(** The reverse version of [nlstar]. *)

Inductive rlstar: nat -> St -> list PutPoll -> St -> Prop :=
| rlstar_refl: forall st, rlstar 0 st [] st
| rlstar_tran: forall n st0 e st1 tr st2,
    rlstar n st0 tr st1 -> step st1 (Some e) st2 ->
    rlstar (S n) st0 (tr ++ [e]) st2
| rlstar_silent_tran: forall n st0 st1 tr st2,
    rlstar n st0 tr st1 -> step st1 None st2 ->
    rlstar (S n) st0 tr st2.
Hint Resolve rlstar_refl : core.

Lemma rlstar_transitive:
  forall m n st0 tr0 st1 tr1 st2,
    rlstar m st0 tr0 st1 ->
    rlstar n st1 tr1 st2 ->
    rlstar (m + n) st0 (tr0 ++ tr1) st2.
Proof.
  intros.
  induction H0.
  - rewrite Nat.add_0_r; rewrite app_nil_r; simpl; auto.
  - apply IHrlstar in H.
    rewrite Nat.add_succ_r.
    rewrite app_assoc.
    eapply rlstar_tran; eauto.
  - apply IHrlstar in H.
    rewrite Nat.add_succ_r.
    eapply rlstar_silent_tran; eauto.
Qed.

Lemma rlstar_lstar:
  forall n st0 tr st1,
    rlstar n st0 tr st1 -> lstar st0 tr st1.
Proof.
  intros.
  induction H; auto.
  - eapply lstar_transitive; eauto.
    eapply lstar_tran; eauto.
  - rewrite <- app_nil_r with (l:=tr).
    eapply lstar_transitive; eauto.
    apply lstar_silent_tran with st2; auto.
Qed.

Lemma lstar_rlstar:
  forall st0 tr st1,
    lstar st0 tr st1 ->
    exists n, rlstar n st0 tr st1.
Proof.
  intros.
  induction H.
  - exists 0; auto.
  - destruct IHlstar as [n G].
    exists (S n).
    cut (rlstar (1 + n) st0 ([e] ++ tr) st2).
    simpl; auto.
    eapply rlstar_transitive; eauto.
    cut (rlstar 1 st0 ([] ++ [e]) st1).
    simpl; auto.
    eapply rlstar_tran; eauto.
  - destruct IHlstar as [n G].
    exists (S n).
    cut (rlstar (1 + n) st0 ([] ++ tr) st2).
    rewrite app_nil_l; auto.
    eapply rlstar_transitive; eauto.
    eapply rlstar_silent_tran; eauto.
Qed.

Lemma rlstar_nlstar:
  forall n st0 tr st1,
    rlstar n st0 tr st1 <-> nlstar n st0 tr st1.
Proof.
  split; intros.
  - induction H; auto.
    + rewrite <- Nat.add_1_r.
      eapply nlstar_transitive; eauto.
      eapply nlstar_tran; eauto.
    + rewrite <- Nat.add_1_r.
      rewrite <- app_nil_r with (l:=tr).
      eapply nlstar_transitive; eauto.
      eapply nlstar_silent_tran; eauto.
  - induction H; auto.
    + rewrite <- Nat.add_1_l.
      assert (G: e :: tr = [e] ++ tr).
      simpl; auto.
      rewrite G.
      eapply rlstar_transitive; eauto.
      rewrite <- app_nil_l with (l:=[e]).
      eapply rlstar_tran; eauto.
    + rewrite <- Nat.add_1_l.
      rewrite <- app_nil_l with (l:=tr).
      eapply rlstar_transitive; eauto.
      eapply rlstar_silent_tran in H; eauto.
Qed.

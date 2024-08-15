(*  --Structural lemmas about well-formednesplit_evt of annotated Copland
    phrases and their event ID ranges, associated automation.
    --The `events` relation --a denotational semantics for phrase events.
    --Lemmas/automation related to `events` *)

Require Import Defs ResultT.
Require Import Preamble.

Require Import Compare_dec Coq.Program.Tactics.

Require Import Lia.

Import List.ListNotations.

Require Export Term_Defs Anno_Term_Defs.

Lemma wfr_lseq_pieces: forall r t1 t2,
    well_formed_r_annt (alseq r t1 t2) ->
    well_formed_r_annt t1 /\ well_formed_r_annt t2.
Proof.
  intros; ff.
Qed.

Lemma wfr_at_pieces: forall t r p,
    well_formed_r_annt (aatt r p t) ->
    well_formed_r_annt t.
Proof.
  intros; ff.
Qed.

Lemma wfr_bseq_pieces: forall r s t1 t2,
    well_formed_r_annt (abseq r s t1 t2) ->
    well_formed_r_annt t1 /\ well_formed_r_annt t2.
Proof.
  intros; ff.
Qed.

Lemma wfr_bpar_pieces: forall r s t1 t2,
    well_formed_r_annt (abpar r s t1 t2) ->
    well_formed_r_annt t1 /\ well_formed_r_annt t2.
Proof.
  intros; ff.
Qed.

Ltac do_wf_pieces :=
  match goal with
  | [H: well_formed_r_annt (alseq _ _ _ ) |- _] =>
    (edestruct wfr_lseq_pieces; eauto)
  | [H: well_formed_r_annt (aatt _ _?t) |- _] =>   
    assert (well_formed_r_annt t)
      by (eapply wfr_at_pieces; eauto)
  | [H: well_formed_r_annt (abseq _ _ _ _) |- _] =>
    (edestruct wfr_bseq_pieces; eauto)
  | [H: well_formed_r_annt (abpar _ _ _ _) |- _] =>
    (edestruct wfr_bpar_pieces; eauto)
  end.


Lemma well_formed_range_r:
  forall t,
    well_formed_r_annt t ->
    snd (range t) = fst (range t) + esize t.
Proof.
  induction t;
  try (intros H; simpl; inv H; simpl;
        repeat find_apply_hyp_hyp; lia).
Qed.

Lemma esize_nonempty: forall t, esize t > 0.
Proof.
  intros; induction t; intros; simpl; lia.
Qed.

Lemma wf_mono: forall t,
    well_formed_r_annt t ->
    snd (range t) > fst (range t).
Proof.
  intros.
  rewrite well_formed_range_r; ff;
  pose proof (esize_nonempty t); lia.
Qed.

Ltac do_mono :=
  (* let asdff := eapply anno_mono; eauto in *)
  match goal with
  | [H: anno _ ?x _ _ = Some (?y,_) |- _] => assert_new_proof_by (y > x) ltac:(eapply anno_mono; eauto)
  end.

Lemma asp_lrange_irrel: forall a i a0 a1 n n',
    anno (asp a) i = (n, a0) ->
    anno (asp a) i = (n',a1) ->
    a0 = a1.
Proof.
  intros; destruct a; ff.
Qed.

(** This predicate specifies when a term, a place, and some initial
    EvidenceT is related to an event.  In other words, it specifies the
    set of events associated with a term, a place, and some initial
    EvidenceT. *)

Inductive events: AnnoTerm -> Plc -> EvidenceT -> Ev -> Prop :=
| evtsnull:
    forall r i p e,
      fst r = i ->
      events (aasp r NULL) p e (null i p)
| evtscpy:
    forall r i p e,
      fst r = i ->
      events (aasp r CPY) p e (copy i p)
| evtsusm:
    forall i r p e sp fwd ps,
      fst r = i ->
      events (aasp r (ASPC sp fwd ps)) p e (umeas i p ps (sp_ev sp e))
| evtssig:
    forall r i p e,
      fst r = i ->
      events (aasp r SIG) p e (umeas i p sig_params e) (* (sign i p e) *)
| evtshsh:
    forall r i p e,
      fst r = i ->
      events (aasp r HSH) p e (umeas i p hsh_params e) (* (hash i p e) *)
| evtsenc:
    forall r i p q e,
      fst r = i ->
      events (aasp r (ENC q)) p e (umeas i p (enc_params q) e) (* (hash i p e) *)

| evtsappr:
    forall r i p e,
      fst r = i ->
      events (aappr r) p e (appr_ev i p e)

| evtsattreq:
    forall r q t i p e,
      fst r = i ->
      events (aatt r q t) p e (req i p q (unanno t) e)
| evtsatt:
    forall r q t ev p e,
      events t q e ev ->
      events (aatt r q t) p e ev
| evtsattrpy:
    forall r q t i p e cm et,
      snd r = S i ->
      (aeval t q e cm) = resultC et ->
      events (aatt r q t) p e (rpy i p q et)
| evtslseql:
    forall r t1 t2 ev p e,
      events t1 p e ev ->
      events (alseq r t1 t2) p e ev
| evtslseqr:
    forall r t1 t2 ev p e cm e1,
      aeval t1 p e cm = resultC e1 ->
      events t2 p e1 ev ->
      events (alseq r t1 t2) p e ev
             
| evtsbseqsplit:
    forall r i s e t1 t2 p,
      fst r = i ->
      events (abseq r s t1 t2) p e (Term_Defs.split i p)
| evtsbseql:
    forall r s e t1 t2 ev p,
      events t1 p (splitEv_T_l s e) ev ->
      events (abseq r s t1 t2) p e ev
| evtsbseqr:
    forall r s e t1 t2 ev p,
      events t2 p (splitEv_T_r s e) ev ->
      events (abseq r s t1 t2) p e ev
| evtsbseqjoin:
    forall r i s e t1 t2 p,
      snd r = S i ->
      events (abseq r s t1 t2) p e (join i p)

| evtsbparsplit:
    forall r i s e t1 t2 p,
      fst r = i ->
      events (abpar r s t1 t2) p e
             (Term_Defs.split i p)
| evtsbparl:
    forall r s e t1 t2 ev p,
      events t1 p (splitEv_T_l s e) ev ->
      events (abpar r s t1 t2) p e ev
| evtsbparr:
    forall r s e t1 t2 ev p,
      events t2 p (splitEv_T_r s e) ev ->
      events (abpar r s t1 t2) p e ev
| evtsbparjoin:
    forall r i s e t1 t2 p,
      snd r = S i ->
      events (abpar r s t1 t2) p e
             (join i  p).
#[export] Hint Constructors events : core.

Ltac inv_events :=
  match goal with
  | [H:events (?C _) _ _ _ |- _] => inv H
  end.

Ltac inv_wfr :=
  match goal with
  | [H: well_formed_r_annt _ |- _] => inv H
  end.

Lemma events_range:
  forall t v p e,
    well_formed_r_annt t ->
    events t p e v ->
    fst (range t) <= ev v < snd (range t).
Proof.
  intros t v p e H H0.
  pose proof H as G.
  apply well_formed_range_r in G.
  rewrite G.
  clear G.
  induction H0;
    try (inv_wfr; simpl in *; auto;
         repeat find_apply_hyp_hyp;
         repeat (find_apply_lem_hyp well_formed_range_r); lia).
Qed.

Lemma at_range:
  forall x r i,
    S (fst r) = fst x ->
    snd r = S (snd x) ->
    fst r <= i < snd r ->
    i = fst r \/
    fst x <= i < snd x \/
    i = snd x.
Proof.
  intros.
  pose proof lt_dec i (S (fst r)) as G.
  destruct G as [G|G]; [left; lia| right].
  pose proof lt_dec i (snd x) as F.
  destruct F as [F|F]; [left; lia| right].
  lia.
Qed.

Lemma lin_range:
  forall x y i,
    snd x = fst y ->
    fst x <= i < snd y ->
    fst x <= i < snd x \/
    fst y <= i < snd y.
Proof.
  intros.
  pose proof lt_dec i (snd x) as G.
  destruct G; lia.
Qed.

Lemma bra_range:
  forall x y r i,
    S (fst r) = fst x ->
    snd x = fst y ->
    snd r = S (snd y) ->
    fst r <= i < snd r ->
    i = fst r \/
    fst x <= i < snd x \/
    fst y <= i < snd y \/
    i = snd y.
Proof.
  destruct x, y, r; lia.
Qed.

Ltac dest_range :=
  match goal with
  | [H: (nat * nat) |- _] => destruct H
  end.

Ltac do_lin_range :=
  match goal with
  | [H: snd _ = fst _,
        H': fst _ <= ?n < snd _
     |- _] =>
    apply lin_range with (i:=n) in H; eauto
  end.

Ltac do_bra_range :=
  match goal with
  | [H: snd _ = fst _,
        H': fst ?x <= ?n < snd ?x
     |- _] =>
    apply bra_range with (i:=n) (r:=x) in H; eauto
  end.

(** Properties of events. *)

(* NOTE: New axiom introduced HERE!!!!
We need to be seriously considering 
whether this should be an axiom or something that that
can be carried about by some wf_* property.
*)
Axiom wf_r_annt_impl_aeval_success : forall t p e cm,
    well_formed_r_annt t ->
    exists et, aeval t p e cm = resultC et.

Lemma events_range_event:
  forall t p i e,
    well_formed_r_annt t ->
    fst (range t) <= i < snd (range t) ->
    exists v, events t p e v /\ ev v = i.
Proof.
  intros t p i e H; revert i; revert p; revert e.
  induction H; intros; simpl in *.
  - destruct x; try destruct a; eapply ex_intro; split; auto;
    simpl in *; try lia.
  - destruct r; simpl in *; subst;
    eexists; intuition; simpl in *; lia.
      
  - find_eapply_lem_hyp at_range; eauto.
    repeat (destruct_disjunct; subst; eauto).

    find_eapply_hyp_hyp; eauto.
    destruct_conjs; eauto.
    eapply wf_r_annt_impl_aeval_success in H; eauto;
    break_exists; eauto.
    Unshelve. eapply nil.
  - do_lin_range; eauto; try lia;
    destruct H2.
    * repeat find_eapply_lem_hyp wf_r_annt_impl_aeval_success.
      eapply IHwell_formed_r_annt1 in H2.
      destruct H2.
      destruct H.
      eexists; intuition; eauto; try lia.
      Unshelve.  all: eauto; eapply nil.
    * eapply IHwell_formed_r_annt2 in H2.
      destruct H2 as [v [? ?]]. 
      eapply wf_r_annt_impl_aeval_success in H0; eauto;
      destruct H0 as [et ?].
      pose proof (evtslseqr).
      exists v; intuition; eauto.
      eapply evtslseqr; eauto.
      eapply wf_r_annt_impl_aeval_success in H; 
      break_exists; eauto.
      eapply H.
      eapply H2.
      eapply H2.
      eexists; intuition; eauto; try lia.
      eapply evtslseqr; eauto;
      edestruct IHwell_formed_r_annt2; eauto; try lia.
      Unshelve.  all: eauto; eapply nil.
    destruct H.

    eexists; eauto; try lia.
    * split.
      ** destruct H.
      assert (fst (range x) <= i < snd (range x)) by lia.
      eapply IHwell_formed_r_annt1 in H4; break_exists; 
      intuition; eauto.
    - 
      eauto;
      repeat destruct_disjunct;
      try lia;
      try (find_eapply_hyp_hyp; eauto;
           destruct_conjs;
           eauto).  
  -
    do_bra_range;
      eauto;
      repeat destruct_disjunct; subst;
        try lia;
        try (find_eapply_hyp_hyp; eauto;
             destruct_conjs;
             eauto; tauto).
    

    + eapply ex_intro; split; try (auto; eauto;tauto).
    + eapply ex_intro; split; try (eauto; auto; tauto).
      
  -
    do_bra_range;
      eauto;
      repeat destruct_disjunct; subst;
        try lia;
        try (find_eapply_hyp_hyp; eauto;
             destruct_conjs;
             eauto; tauto).

    + eapply ex_intro; split; auto.
    + eapply ex_intro; split; eauto.
Qed.

Ltac events_event_range :=
  repeat match goal with
         | [ H: events _ _ _ _ |- _ ] =>
           apply events_range in H; auto
         end; lia.

Ltac aba :=
  match goal with
  | [H: events _ _ _ _, H': events _ _ _ _ |- _] => inv H; inv H'
  end.

Ltac wfr :=
  match goal with
  | [H': well_formed_r_annt ?HH |- _] => pose_new_proof (well_formed_range_r HH H')
  end.

Lemma events_injective:
  forall t p e v1 v2,
    well_formed_r_annt t ->
    events t p e v1 ->
    events t p e v2 ->
    ev v1 = ev v2 ->
    v1 = v2.
Proof.
  intros.
  generalizeEverythingElse H.
  induction H; intros;
    try (
        repeat wfr;
        aba; simpl in *; subst; auto;
        try (events_event_range; tauto);
        try (find_eapply_hyp_hyp; eauto);
        eauto).
Qed.

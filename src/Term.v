(*  --Structural lemmas about well-formednesplit_evt of annotated Copland
    phrases and their event ID ranges, associated automation.
    --The `events` relation --a denotational semantics for phrase events.
    --Lemmas/automation related to `events` *)

Require Import Defs ResultT.
Require Import Preamble.

Require Import Compare_dec Coq.Program.Tactics.

Require Import Lia.
Require Import List More_lists.

Import List.ListNotations.

Require Export Term_Defs.

(** This predicate specifies when a term, a place, and some initial
    EvidenceT is related to an event.  In other words, it specifies the
    set of events associated with a term, a place, and some initial
    EvidenceT. *)

Inductive events: GlobalContext -> CopPhrase -> nat -> list Ev -> Prop :=
| evts_asp: forall G i p e a evs,
    asp_events G p e a i = resultC evs ->
    events G (cop_phrase p e (asp a)) i evs

| evts_att: forall G q t i i' p e rem_evs,
    events G (cop_phrase q e t) (i + 1) rem_evs ->
    i' = i + 1 + length rem_evs ->
    events G 
      (cop_phrase p e (att q t)) i
      ([req i p q t e] ++ rem_evs ++ [rpy i' p q e])

| evts_lseq : forall G t1 t2 p e e' i evs1 evs2,
    events G (cop_phrase p e t1) i evs1 ->
    eval G p e t1 = resultC e' ->
    events G (cop_phrase p e' t2) (i + length evs1) evs2 ->
    events G (cop_phrase p e (lseq t1 t2)) i (evs1 ++ evs2)

| evts_bseq: forall G t1 t2 p e evs1 evs2 s i i',
    events G (cop_phrase p (splitEv_T_l s e) t1) (i + 1) evs1 ->
    events G (cop_phrase p (splitEv_T_r s e) t2) (i + 1 + length evs1) evs2 ->
    i' = i + 1 + length evs1 + length evs2 ->
    events G (cop_phrase p e (bseq s t1 t2)) i
      ([split i p] ++ evs1 ++ evs2 ++ [join i' p])

| evts_bpar: forall G t1 t2 p e evs1 evs2 s i i' i'' loc et_l et_r,
    et_l = splitEv_T_l s e ->
    et_r = splitEv_T_r s e ->
    events G (cop_phrase p et_l t1) (i + 2) evs1 ->
    events G (cop_phrase p et_r t2) (i + 2 + length evs1) evs2 ->
    loc = i + 1 ->
    i' = i + 2 + length evs1 + length evs2 ->
    i'' = i + 2 + length evs1 + length evs2 + 1 ->
    events G (cop_phrase p e (bpar s t1 t2)) i
      ([split i p] ++ [cvm_thread_start loc loc p t1 et_l] ++ evs1 ++ 
      evs2 ++ [cvm_thread_end i' loc] ++ [join i'' p]).
#[export] Hint Constructors events : core.

Lemma events_range: forall G t p e evs i,
  events G (cop_phrase p e t) i evs ->
  events_size G p e t = resultC (length evs).
Proof.
  induction t; simpl in *; intuition;
  inversion H; subst; 
  try (repeat find_apply_hyp_hyp;
    repeat find_rewrite; simpl in *; 
    repeat find_rewrite; simpl in *;
    repeat rewrite app_length; simpl in *;
    eauto;
    try (f_equal; lia)).
  - find_apply_lem_hyp asp_events_size_works; ff.
Qed.

(** Properties of events. *)
Theorem events_deterministic_index : forall G t p e i v,
  events G (cop_phrase p e t) i v ->
  forall v',
  true_last v = Some v' ->
  ev v' = i + length v - 1.
Proof.
  intros.
  generalizeEverythingElse H.
  induction H; intros;
  try (repeat (
    find_apply_lem_hyp true_last_app_spec;
    intuition; try congruence;
    simpl in *;
    repeat find_injection;
    simpl in *;
    repeat rewrite app_length;
    simpl in *;
    try lia
  );
  repeat (find_apply_lem_hyp app_eq_nil;
    intuition; try congruence
  ); fail).
  - eapply asp_events_deterministic_index; eauto.
  - find_apply_lem_hyp true_last_app_spec; intuition;
    subst; simpl in *;
    try rewrite app_nil_r; eauto;
    repeat rewrite app_length; 
    find_apply_hyp_hyp; try lia.
  - repeat (find_apply_lem_hyp true_last_app_spec;
    door; [ simpl in *; repeat find_injection; try congruence;
      repeat rewrite app_assoc in *;
      find_eapply_lem_hyp app_eq_nil;
      intuition; congruence | ]);
    simpl in *; repeat find_injection;
    repeat rewrite app_length;
    simpl in *; lia.
Qed.

Theorem events_injective: forall G t p e i v1 v2,
  events G (cop_phrase p e t) i v1 ->
  events G (cop_phrase p e t) i v2 ->
  v1 = v2.
Proof.
  induction t; simpl in *; intros;
  invc H; invc H0; ff.
  - match goal with
    | H : events _ _ _ _,
      H0 : events _ _ _ _ |- _ => 
      eapply IHt in H; [ | eapply H0 ]; 
      clear H0; ff
    end.
  - match goal with
    | H : events _ (cop_phrase _ _ t1) _ _,
      H0 : events _ (cop_phrase _ _ t1) _ _ |- _ => 
      eapply IHt1 in H; [ | eapply H0 ];
      clear H0; clear IHt1; ff
    end; 
    repeat find_rewrite; repeat find_injection;
    match goal with
    | H : events _ (cop_phrase _ _ t2) _ _,
      H0 : events _ (cop_phrase _ _ t2) _ _ |- _ => 
      eapply IHt2 in H; [ | eapply H0 ];
      clear H0; clear IHt2; ff
    end.
  - match goal with
    | H : events _ (cop_phrase _ _ t1) _ _,
      H0 : events _ (cop_phrase _ _ t1) _ _ |- _ => 
      eapply IHt1 in H; [ | eapply H0 ];
      clear H0; clear IHt1; ff
    end; 
    repeat find_rewrite; repeat find_injection;
    match goal with
    | H : events _ (cop_phrase _ _ t2) _ _,
      H0 : events _ (cop_phrase _ _ t2) _ _ |- _ => 
      eapply IHt2 in H; [ | eapply H0 ];
      clear H0; clear IHt2; ff
    end.
  - match goal with
    | H : events _ (cop_phrase _ _ t1) _ _,
      H0 : events _ (cop_phrase _ _ t1) _ _ |- _ => 
      eapply IHt1 in H; [ | eapply H0 ];
      clear H0; clear IHt1; ff
    end; 
    repeat find_rewrite; repeat find_injection;
    match goal with
    | H : events _ (cop_phrase _ _ t2) _ _,
      H0 : events _ (cop_phrase _ _ t2) _ _ |- _ => 
      eapply IHt2 in H; [ | eapply H0 ];
      clear H0; clear IHt2; ff
    end.
Qed.

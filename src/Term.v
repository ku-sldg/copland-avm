(*  --Structural lemmas about well-formednesplit_evt of annotated Copland
    phrases and their event ID ranges, associated automation.
    --The `events` relation --a denotational semantics for phrase events.
    --Lemmas/automation related to `events` *)

Require Import StructTactics ResultT.

Require Import StructTactics Coq.Program.Tactics.

Require Import Lia String.
Require Import List.

Import List.ListNotations ResultNotation.

Require Export Term_Defs.

(** This predicate specifies when given a Global Context,
    a Copland Phrase (Plc, EvidenceT, Term), and an initial index,
    the events related to that Copland Phrase. 

    This event specification is a Big Step Semantics describing
    Copland execution and the ordering of events that must occur 
*)
Inductive events: GlobalContext -> CopPhrase -> nat -> list Ev -> Prop :=
| evts_asp: forall G i p e a evs,
    asp_events G p e a i = resultC evs ->
    events G (cop_phrase p e (asp a)) i evs

| evts_att: forall G q t i i' p e e' rem_evs,
    events G (cop_phrase q e t) (i + 1) rem_evs ->
    i' = i + 1 + length rem_evs ->
    eval G q e t = resultC e' ->
    events G 
      (cop_phrase p e (att q t)) i
      ([req i p q e t] ++ rem_evs ++ [rpy i' p q e'])

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
      ([split i p] ++ [cvm_thread_start loc loc p et_r t2] ++ evs1 ++ 
      evs2 ++ [cvm_thread_end i' loc] ++ [join i'' p]).
#[export] Hint Constructors events : core.


Fixpoint events_fix (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : Term) (i : nat) 
  : ResultT (list Ev) string :=
  match t with
  | asp a => asp_events G p e a i
  | att q t' => 
    evs <- events_fix G q e t' (i + 1) ;;
    e' <- eval G q e t' ;;
    resultC ([req i p q e t'] ++ evs ++ [rpy (i + 1 + List.length evs) p q e'])
  | lseq t1 t2 => 
    evs1 <- events_fix G p e t1 i ;;
    e' <- eval G p e t1 ;;
    evs2 <- events_fix G p e' t2 (i + List.length evs1) ;;
    resultC (evs1 ++ evs2)
  | bseq s t1 t2 => 
    evs1 <- events_fix G p (splitEv_T_l s e) t1 (i + 1) ;;
    evs2 <- events_fix G p (splitEv_T_r s e) t2 (i + 1 + List.length evs1) ;;

    resultC ([split i p] ++ evs1 ++ evs2 ++ [join (i + 1 + List.length evs1 + List.length evs2) p])
  | bpar s t1 t2 =>
    evs1 <- events_fix G p (splitEv_T_l s e) t1 (i + 2) ;;
    evs2 <- events_fix G p (splitEv_T_r s e) t2 (i + 2 + List.length evs1) ;;
    let loc := i + 1 in
    resultC ([split i p] ++ [cvm_thread_start loc loc p (splitEv_T_r s e) t2] ++ evs1 ++ 
      evs2 ++ [cvm_thread_end (i + 2 + List.length evs1 + List.length evs2) loc] ++ 
      [join (i + 2 + List.length evs1 + List.length evs2 + 1) p])
  end.

Theorem events_events_fix_eq : forall G p e t i evs,
  events G (cop_phrase p e t) i evs <->
  events_fix G p e t i = resultC evs.
Proof.
  split.
  - generalizeEverythingElse t; induction t;
    simpl in *; intuition; invc H; eauto;
    ffa using result_monad_unfold.
  - generalizeEverythingElse t; induction t;
    simpl in *; intuition;
    ffa using result_monad_unfold;
    econstructor; eauto.
Qed.
    
Lemma events_range: forall G t p e evs i,
  events G (cop_phrase p e t) i evs ->
  events_size G p e t = resultC (length evs).
Proof.
  induction t; simpl in *; intuition;
  inversion H; subst; 
  try (repeat find_apply_hyp_hyp;
    repeat find_rewrite; simpl in *; 
    repeat find_rewrite; simpl in *;
    repeat rewrite length_app; simpl in *;
    eauto;
    try (f_equal; lia)).
  - find_apply_lem_hyp asp_events_size_works; ff.
Qed.

Lemma events_fix_range : forall G p e t i evs,
  events_fix G p e t i = resultC evs ->
  events_size G p e t = resultC (length evs).
Proof.
  intros; rewrite <- events_events_fix_eq in *; 
  eapply events_range; eauto.
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
    repeat rewrite length_app;
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
    repeat rewrite length_app; 
    find_apply_hyp_hyp; try lia.
  - repeat (find_apply_lem_hyp true_last_app_spec;
    break_or_hyp; [ ff;
      repeat rewrite app_assoc in *;
      find_eapply_lem_hyp app_eq_nil;
      intuition; congruence | ]).
    simpl in *; repeat find_injection;
    repeat rewrite length_app;
    simpl in *; ff; lia.
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

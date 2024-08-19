(*  --Structural lemmas about well-formednesplit_evt of annotated Copland
    phrases and their event ID ranges, associated automation.
    --The `events` relation --a denotational semantics for phrase events.
    --Lemmas/automation related to `events` *)

Require Import Defs ResultT.
Require Import Preamble.

Require Import Compare_dec Coq.Program.Tactics.

Require Import Lia.
Require Import List.

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
    events G (cop_phrase q e t) i rem_evs ->
    events G 
      (cop_phrase p e (att q t)) i
      ([req i p q t e] ++ rem_evs ++ [rpy i' p q e])

| evts_lseq : forall G t1 t2 p e e' i i' evs1 evs2,
    events G (cop_phrase p e t1) i evs1 ->
    eval G p e t1 = resultC e' ->
    events G (cop_phrase p e' t2) i' evs2 ->
    events G (cop_phrase p e (lseq t1 t2)) i (evs1 ++ evs2)

| evts_bseq: forall G t1 t2 p e evs1 evs2 s i i' i'',
    events G (cop_phrase p (splitEv_T_l s e) t1) i evs1 ->
    events G (cop_phrase p (splitEv_T_r s e) t2) i' evs2 ->
    events G (cop_phrase p e (bseq s t1 t2)) i
      ([split i p] ++ evs1 ++ evs2 ++ [join i'' p])

| evts_bpar: forall G t1 t2 p e evs1 evs2 s i i' i'',
    events G (cop_phrase p (splitEv_T_l s e) t1) i evs1 ->
    events G (cop_phrase p (splitEv_T_r s e) t2) i' evs2 ->
    events G (cop_phrase p e (bpar s t1 t2)) i
      ([split i p] ++ evs1 ++ evs2 ++ [join i'' p]).
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
(* Fixpoint true_last {A : Type} (l : list A) 
  {h t} `{HL : l = h :: t} {struct l} : A.
  refine (match l as l' return l = l' -> A with
  | nil => fun HL => _
  | h' :: t' => fun HL =>
    match t' as t'' return t' = t'' -> A with
    | nil => fun HL' => h'
    | h'' :: t'' => fun HL' => @true_last _ t' h'' t'' _
    end eq_refl
  end eq_refl).
- subst; congruence. 
- subst; ff. 
Defined. *)
Fixpoint true_last {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | h' :: t' => 
    match t' with
    | nil => Some h'
    | h'' :: t'' => true_last t'
    end
  end.

Theorem events_deterministic : forall G t p e i v,
  events G (cop_phrase p e t) i v ->
  forall v',
  true_last v = Some v' ->
  ev v' = i + length v.
Proof.
  induction t; simpl in *; intros;
  inversion H; subst.
  induction t; simpl in *; intros; ff.
  - 


Lemma events_injective: forall G t p e i v1 v2,
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
    eapply IHt in H8; ff; ff.
  - inversion H; inversion H0.
  generalizeEverythingElse H.
  induction H; intros;
    try (
        repeat wfr;
        aba; simpl in *; subst; auto;
        try (events_event_range; tauto);
        try (find_eapply_hyp_hyp; eauto);
        eauto).
Qed.

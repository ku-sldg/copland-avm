(* Definition and general properties of Annotated Copland Terms (AnnoTerm).
    Includes annotation and "un-annotation" functions, well-formednesplit_evt predicates, 
    event identifier "span" computations, and their formal properties.
*)


Require Import Term_Defs Preamble.
Require Import StructTactics Defs ResultT String.

Require Import Lia.
Import List.ListNotations ResultNotation.


(** * Annotated Terms

    Annotated terms are used to ensure that each distinct event has a
    distinct natural number.  To do so, each term is annotated by a
    pair of numbers called a range.  Let [(i, k)] be the label for
    term [t].  The labels will be chosen to have the property such
    that for each event in the set of events associated with term [t],
    its number [j] will be in the range [i <= j < k].  *)

Definition Range: Set := nat * nat.

Inductive AnnoTerm :=
| aasp: Range -> ASP -> AnnoTerm
| aatt: Range -> Plc -> AnnoTerm -> AnnoTerm
| alseq: Range -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abseq: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abpar: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm.

(* EvidenceT Type size *)
Fixpoint esize (G : ASP_Type_Env) (t : AnnoTerm) (e : EvidenceT) 
    : ResultT nat string :=
  match t with
  | aasp _ a => 
    match a with
    | APPR => et_size G e
    | _ => resultC 1
    end
  | aatt _ _ t1 => 
    e' <- esize G t1 e ;;
    resultC (2 + e')
  | alseq _ t1 t2 => 
    e1 <- esize G t1 e ;;
    e2 <- esize G t2 e ;;
    resultC (e1 + e2)
  
  | abseq _ _ t1 t2 => 
    e1 <- esize G t1 e ;;
    e2 <- esize G t2 e ;;
    resultC (2 + e1 + e2)
  | abpar _ _ t1 t2 => 
    e1 <- esize G t1 e ;;
    e2 <- esize G t2 e ;;
    resultC (2 + e1 + e2)
  end.

(* Extract Range from each annotated term *)
Definition range x :=
  match x with
  | aasp r _ => r
  | aatt r _ _ => r
  | alseq r _ _ => r
  | abseq r _ _ _ => r
  | abpar r _ _ _ => r
  end.

(* Term subset relation *)
Inductive term_sub : Term -> Term -> Prop :=
| termsub_refl_annt: forall t: Term, term_sub t t
| aatt_sub_annt: forall t t' p,
    term_sub t' t ->
    term_sub t' (att p t)
| alseq_subl_annt: forall t' t1 t2,
    term_sub t' t1 ->
    term_sub t' (lseq t1 t2)
| alseq_subr_annt: forall t' t1 t2,
    term_sub t' t2 ->
    term_sub t' (lseq t1 t2)
| abseq_subl_annt: forall t' t1 t2 s,
    term_sub t' t1 ->
    term_sub t' (bseq s t1 t2)
| abseq_subr_annt: forall t' t1 t2 s,
    term_sub t' t2 ->
    term_sub t' (bseq s t1 t2)
| abpar_subl_annt: forall t' t1 t2 s,
    term_sub t' t1 ->
    term_sub t' (bpar s t1 t2)
| abpar_subr_annt: forall t' t1 t2 s,
    term_sub t' t2 ->
    term_sub t' (bpar s t1 t2).
#[export] Hint Constructors term_sub : core.

Lemma termsub_transitive: forall t t' t'',
    term_sub t t' ->
    term_sub t' t'' ->
    term_sub t t''.
Proof.  
  generalizeEverythingElse t''.
  induction t'';
    intros H H0; ff.
Qed.

Fixpoint anno_ev (e : EvidenceT) (i : nat) : nat :=
  match e with
  | mt_evt => (S i)
  | nonce_evt n => (S i)
  | asp_evt p par e' => S (anno_ev e' i)
  | split_evt e1 e2 => 
      let j := anno_ev e1 i in
      anno_ev e2 j
  end.

(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *)
Fixpoint anno (e : EvidenceT) (t: Term) (i:nat) : (nat * AnnoTerm) :=
  match t with
  | asp x => 
    match x with
    | APPR => (anno_ev e i, aasp (i, anno_ev e i) x)
    | _ => (S i, aasp (i, S i) x)
    end
  
  | att p x =>
    let '(j,a) := anno e x (S i)  in
    (S j, aatt (i, S j) p a)

  | lseq x y =>
    let '(j,a) := anno e x i in
    let '(k,bt) := anno e y j in
    (k, alseq (i, k) a bt)

  | bseq s x y =>
    let '(j,a) := anno e x (S i) in
    let '(k,b) := anno e y j in
    (S k, abseq (i, S k) s a b)

  | bpar s x y =>
    let '(j,a) := anno e x (S i) in
    let '(k,b) := anno e y j in
    (S k, abpar (i, S k) s a b)
  end.

Fixpoint unanno a :=
  match a with
  | aasp _ a => asp a
  | aatt _ p t => att p (unanno t)
  | alseq _ a1 a2 => lseq (unanno a1) (unanno a2)                 
  | abseq _ spl a1 a2 => bseq spl (unanno a1) (unanno a2) 
  | abpar _ spl a1 a2 => bpar spl (unanno a1) (unanno a2)
  end.

Lemma anno_unanno: forall e t i,
    unanno (snd (anno e t i)) = t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ff; rw using ff.
Qed.

(** eval (EvidenceT semantics) for annotated terms. *)

Fixpoint aeval (G : ASP_Type_Env) (cm : ASP_Compat_MapT) (t : AnnoTerm) 
    (p : Plc) (e : EvidenceT) : ResultT EvidenceT string :=
  match t with
  | aasp _ x => eval G cm (asp x) p e
  | aatt _ q x => aeval G cm x q e 
  | alseq _ t1 t2 => 
      e1 <- aeval G cm t1 p e ;;
      aeval G cm t2 p e1 
  | abseq _ s t1 t2 => 
      e1 <- aeval G cm t1 p (splitEv_T_l s e) ;;
      e2 <- aeval G cm t2 p (splitEv_T_r s e) ;;
      resultC (split_evt e1 e2)
  | abpar _ s t1 t2 => 
      e1 <- aeval G cm t1 p (splitEv_T_l s e) ;;
      e2 <- aeval G cm t2 p (splitEv_T_r s e) ;;
      resultC (split_evt e1 e2)
  end.

Lemma eval_aeval:
  forall e' t p e i G cm t',
    t' = snd (anno e' t i) ->
    eval G cm t p e = aeval G cm t' p e.
Proof.
  induction t; simpl in *; 
  intuition; eauto; ff.
  - eapply IHt; rw; eauto.
  - erewrite IHt1; eauto; rw;
    result_monad_unfold; ff;
    eapply IHt2; rw; eauto.
  - erewrite IHt1; eauto; rw;
    erewrite IHt2; eauto; rw;
    eauto.
  - erewrite IHt1; eauto; rw;
    erewrite IHt2; eauto; rw;
    eauto.
Qed.

(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)
Inductive well_formed_r_annt
    : ASP_Type_Env -> EvidenceT -> AnnoTerm -> Prop :=
| wf_asp_r_annt: forall r e x G n,
    match x with 
    | APPR => et_size G e 
    | _ => resultC 0 end = resultC n ->
    snd r = S (fst r) + n ->
    well_formed_r_annt G e (aasp r x)

| wf_att_r_annt: forall r p x e G,
    well_formed_r_annt G e x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->
    well_formed_r_annt G e (aatt r p x)               

| wf_lseq_r_annt: forall r x y e G,
    well_formed_r_annt G e x -> 
    well_formed_r_annt G e y ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) -> 
    well_formed_r_annt G e (alseq r x y)               

| wf_bseq_r_annt: forall r s x y e G,
    well_formed_r_annt G e x -> 
    well_formed_r_annt G e y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->  
    well_formed_r_annt G e (abseq r s x y)              

| wf_bpar_r_annt: forall r s x y e G,
    well_formed_r_annt G e x -> 
    well_formed_r_annt G e y ->  
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    (*fst (range y) > fst (range x) -> *)
    well_formed_r_annt G e (abpar r s x y).
#[export] Hint Constructors well_formed_r_annt : core.


Lemma same_anno_range: forall t i a b e n n',
    anno e t i = (n,a) ->
    anno e t i = (n',b) ->
    n = n'.
Proof.
  induction t; intros; ff.
Qed.

Lemma anno_ev_mono : forall e i,
  anno_ev e i > i.
Proof.
  induction e; simpl in *; intros; try lia.
  - pose proof (IHe i); lia. 
  - pose proof (IHe1 i);
    pose proof (IHe2 (anno_ev e1 i)); lia.
Qed.

Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm) e,
  anno e t i = (j,t') ->
  j > i.
Proof.
  induction t; intuition; ffa; try lia;
  eapply anno_ev_mono.
Qed.
#[export] Hint Resolve anno_mono : core.

Lemma anno_range:
  forall x i j t' e,
    anno e x i = (j,t') ->
    range (t') = (i, j).
Proof.
  induction x; intros; ff.
Qed.


(** Lemma stating that any annotated term produced via anno is well formed *)
Lemma anno_well_formed_r:
  forall t i j t' G e,
    anno e t i = (j, t') ->
    well_formed_r_annt G e t'.
Proof.
  induction t; intros; ff;
  try (econstructor; ff;
  try (repeat find_apply_lem_hyp anno_range;
    repeat find_rewrite; ff; fail); 
    try assert (n > S i) by eauto; lia).
Qed.

(* Computes the length of the "span" or range of event IDs for a given Term *)
Fixpoint event_id_span_Term (t: Term) : nat :=
  match t with
  | asp x => 1
  | att p x => 2 + (event_id_span_Term x)
  | lseq x y => (event_id_span_Term x) + (event_id_span_Term y)
  | bseq s x y => 2 + (event_id_span_Term x) + (event_id_span_Term y)
  | bpar s x y => 2 + (event_id_span_Term x) + (event_id_span_Term y)
  end.

(* Same as event_id_span', but for Core Terms *)
Fixpoint event_id_span_Core (t: Core_Term) : nat :=
  match t with
  | aspc CLEAR => 0
  | attc _ x => 2 + (event_id_span_Term x)
  | lseqc x y => (event_id_span_Core x) + (event_id_span_Core y)
  | bseqc x y => 2 + (event_id_span_Core x) + (event_id_span_Core y)
  | bparc _ x y => 2 + (event_id_span_Core x) + (event_id_span_Core y)
  | _ => 1
  end.

Lemma event_id_works : forall t,
  event_id_span_Term t = event_id_span_Core (copland_compile t).
Proof with (simpl in *; eauto).
  induction t...
  - destruct a... destruct s...
  - destruct s, s, s0...
  - destruct s, s, s0...
Qed.


Lemma span_range : forall t i j t',
  anno t i = (j, t') ->
  event_id_span_Term t = (j - i).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; simpl in *; try find_injection; try lia;
  ff; repeat match goal with
  | H: anno _ _ = _ ,
    IH : context[forall _, anno _ _ = _ -> _] |- _  => 
    let H' := fresh "H" in
    pose proof H as H'; apply anno_mono in H';
    eapply IH in H; eauto;
    repeat find_rewrite
  end; lia. 
Qed.

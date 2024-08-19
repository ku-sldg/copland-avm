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

Inductive AnnoCopPhrase :=
| anno_cop_phrase : Plc -> EvidenceT -> AnnoTerm -> AnnoCopPhrase.

Fixpoint aeval (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : AnnoTerm) 
    : ResultT EvidenceT string :=
  match t with
  | aasp _ x => eval G p e (asp x)
  | aatt _ q x => aeval G q e x
  | alseq _ t1 t2 => 
      e1 <- aeval G p e t1 ;;
      aeval G p e1 t2
  | abseq _ s t1 t2 => 
      e1 <- aeval G p (splitEv_T_l s e) t1 ;;
      e2 <- aeval G p (splitEv_T_r s e) t2 ;;
      resultC (split_evt e1 e2)
  | abpar _ s t1 t2 => 
      e1 <- aeval G p (splitEv_T_l s e) t1 ;;
      e2 <- aeval G p (splitEv_T_r s e) t2 ;;
      resultC (split_evt e1 e2)
  end.

(* EvidenceT Type size *)
Fixpoint events_size (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : Term)
    : ResultT nat string :=
  match t with
  | asp a => 
    match a with
    | APPR => appr_et_size G e (* appraisal does # of events based on ev type *)
    | _ => resultC 1 (* all other ASPs do 1 event for meas *)
    end
  | att p' t1 => 
    e' <- events_size G p' e t1 ;; (* remotely e' events are done *)
    resultC (2 + e') (* +1 for req, +e' for rem evs, +1 for rpy *)

  | lseq t1 t2 => 
    e1 <- events_size G p e t1 ;; (* first e1 events are done *)
    e' <- eval G p e t1 ;; (* we need a new evidence type for next step *)
    e2 <- events_size G p e' t2 ;; (* next e2 events are done *)
    resultC (e1 + e2) (* +e1 for first evs, +e2 for second evs *)
  
  | bseq s t1 t2 => 
    e1 <- events_size G p (splitEv_T_l s e) t1 ;; (* left does e1 events *)
    e2 <- events_size G p (splitEv_T_r s e) t2 ;; (* right does e2 events *)
    resultC (2 + e1 + e2) (* +1 for split; +e1,+e2 for sides, +1 for join *)
  | bpar s t1 t2 => 
    e1 <- events_size G p (splitEv_T_l s e) t1 ;; (* left does e1 events *)
    e2 <- events_size G p (splitEv_T_r s e) t2 ;; (* right does e2 events *)
    resultC (2 + e1 + e2) (* +1 for split; +e1,+e2 for sides, +1 for join *)
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
  induction t''; intros; ff.
Qed.

(** eval (EvidenceT semantics) for annotated terms. *)

(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *)
Fixpoint anno (G : GlobalContext) (p : Plc) (e : EvidenceT) 
    (t: Term) : ResultT (AnnoTerm * EvidenceT) string :=
  match t with
  | asp x => 
    match x with
    | APPR => 
      match appr_et_size G e with
      | errC s => errC s
      | resultC n => 
        let nterm := aasp (i, S i + n) x in
        e' <- aeval G p e nterm ;;
        resultC (S i + n, nterm, e')
      end
    | _ => 
      let nterm := aasp (i, S i) x in
      e' <- aeval G p e nterm ;;
      resultC (S i, nterm, e')
    end
  
  | att p' x =>
    '(j, a, e') <- anno G p' e x (S i) ;;
    let nterm := aatt (i, S j) p' a in
    e' <- aeval G p e nterm ;;
    resultC (S j, nterm, e')

  | lseq x y =>
    '(j, a, e') <- anno G p e x i ;;
    '(k, b, e'') <- anno G p e' y j ;;
    let nterm := alseq (i, k) a b in
    e' <- aeval G p e nterm ;;
    resultC (k, nterm, e')

  | bseq s x y =>
    '(j, a, e') <- anno G p (splitEv_T_l s e) x (S i) ;;
    '(k, b, e'') <- anno G p (splitEv_T_r s e) y j ;;
    let nterm := abseq (i, S k) s a b in
    e' <- aeval G p e nterm ;;
    resultC (S k, nterm, e')

  | bpar s x y =>
    '(j, a, e') <- anno G p (splitEv_T_l s e) x (S i) ;;
    '(k, b, e'') <- anno G p (splitEv_T_r s e) y j ;;
    let nterm := abpar (i, S k) s a b in
    e' <- aeval G p e nterm ;;
    resultC (S k, nterm, e')
  end.

Fixpoint unanno a :=
  match a with
  | aasp _ a => asp a
  | aatt _ p t => att p (unanno t)
  | alseq _ a1 a2 => lseq (unanno a1) (unanno a2)                 
  | abseq _ spl a1 a2 => bseq spl (unanno a1) (unanno a2) 
  | abpar _ spl a1 a2 => bpar spl (unanno a1) (unanno a2)
  end.

Lemma anno_unanno: forall e t t' i i' G p e',
  anno G p e t i = resultC (i', t', e') ->
  unanno t' = t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ffa using result_monad_unfold.
Qed.

Lemma anno_aeval : forall G t t' e e' p i i',
  anno G p e t i = resultC (i', t', e') ->
  aeval G p e t' = resultC e'.
Proof.
  induction t; simpl in *; intuition; ffa using result_monad_unfold.
Qed.

Lemma anno_eval : forall G t t' e e' p i i',
  anno G p e t i = resultC (i', t', e') ->
  eval G p e t = resultC e'.
Proof.
  induction t; simpl in *; intuition; ff;
  result_monad_unfold; ff; 
  try (ffa using result_monad_unfold; fail);
  try (match goal with
  | H: anno _ _ _ _ _ = _ |- _ => 
    eapply anno_aeval in H as ?;
    ffa
  end; fail);
  match goal with
  | H: anno _ _ _ _ _ = _,
    H1: anno _ _ _ _ _ = _ |- _ => 
    eapply anno_aeval in H as ?;
    eapply anno_aeval in H1 as ?;
    repeat find_rewrite;
    repeat find_injection;
    ffa
  end.
Qed.

Lemma eval_aeval:
  forall t t' p e i i' G e',
    anno G p e t i = resultC (i', t', e') ->
    eval G p e t = aeval G p e t'.
Proof.
  intros;
  eapply anno_eval in H as ?;
  eapply anno_aeval in H as ?;
  ff.
Qed.

Theorem evidence_size_agree : forall G t e p n,
  esize G p e t = resultC n ->
  forall e',
  aeval G p e t = resultC e' ->
  et_size G e' = resultC n.
Proof.
  induction t.
  - simpl in *; intros. 
    break_match. subst; try find_injection.
    *  
    ff.
    ff.

  event_id_span_Term G 0 e t = resultC (snd (range t) - fst (range t)).

(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)
Inductive well_formed_r_annt : GlobalContext -> AnnoCopPhrase -> Prop :=
| wf_asp_r_annt: forall r e x G n p,
    match x with 
    | APPR => appr_et_size G e 
    | _ => resultC 0 end = resultC n ->
    snd r = S (fst r) + n ->
    well_formed_r_annt G (anno_cop_phrase p e (aasp r x))

| wf_att_r_annt: forall r p x e G p',
    well_formed_r_annt G (anno_cop_phrase p' e x) ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->
    well_formed_r_annt G (anno_cop_phrase p e (aatt r p' x))

| wf_lseq_r_annt: forall r x y e G p e',
    well_formed_r_annt G (anno_cop_phrase p e x) ->
    aeval G p e x = resultC e' ->
    well_formed_r_annt G (anno_cop_phrase p e' y) ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) -> 
    well_formed_r_annt G (anno_cop_phrase p e (alseq r x y))

| wf_bseq_r_annt: forall r s x y e G p,
    well_formed_r_annt G (anno_cop_phrase p (splitEv_T_l s e) x) -> 
    well_formed_r_annt G (anno_cop_phrase p (splitEv_T_r s e) y) ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->  
    well_formed_r_annt G (anno_cop_phrase p e (abseq r s x y))

| wf_bpar_r_annt: forall r s x y e G p,
    well_formed_r_annt G (anno_cop_phrase p (splitEv_T_l s e) x) -> 
    well_formed_r_annt G (anno_cop_phrase p (splitEv_T_r s e) y) ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    (*fst (range y) > fst (range x) -> *)
    well_formed_r_annt G (anno_cop_phrase p e (abpar r s x y)).
#[export] Hint Constructors well_formed_r_annt : core.

Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm) e e' G p,
  anno G p e t i = resultC (j,t',e') ->
  j > i.
Proof.
  induction t; intuition; ffa using (result_monad_unfold; try lia).
Qed.
#[export] Hint Resolve anno_mono : core.

Lemma anno_range:
  forall x i j t' e G e' p,
    anno G p e x i = resultC (j, t',e') ->
    range (t') = (i, j).
Proof.
  induction x; intros; ffa using result_monad_unfold.
Qed.

(** Lemma stating that any annotated term produced via anno is well formed *)
Lemma anno_well_formed_r:
  forall t i j t' G e e' p,
    anno G p e t i = resultC (j, t', e') ->
    well_formed_r_annt G (anno_cop_phrase p e t').
Proof.
  induction t; intros; eauto.
  - ffa using result_monad_unfold.
  - simpl in *; result_monad_unfold;
    ff.
    econstructor; simpl in *; eauto;
    try (find_apply_lem_hyp anno_range;
    find_rewrite; simpl in *; eauto).
    assert (n > S i) by eauto;
    simpl in *; lia.
  - simpl in *; result_monad_unfold;
    ff; econstructor; eauto;
    try (repeat find_apply_lem_hyp anno_range;
      repeat find_rewrite;
      simpl in *; eauto; fail).
    eapply IHt1 in Heqr as ?;
    eapply anno_aeval in Heqr as ?;
    repeat find_rewrite; ff.
  - simpl in *; result_monad_unfold;
    ff; econstructor; eauto;
    try (repeat find_apply_lem_hyp anno_range;
      repeat find_rewrite;
      simpl in *; eauto; fail).
  - simpl in *; result_monad_unfold;
    ff; econstructor; eauto;
    try (repeat find_apply_lem_hyp anno_range;
      repeat find_rewrite;
      simpl in *; eauto; fail).
Qed.

(* Computes the length of the "span" or range of event IDs for a given Term *)
Fixpoint event_id_span_Term (G : GlobalContext) (p : Plc) (e : EvidenceT) (t: Term) 
    : ResultT nat string :=
  match t with
  | asp x => 
    match x with
    | APPR => match appr_et_size G e with
              | errC s => errC s
              | resultC n => resultC (1 + n)
              end
    | _ => resultC 1
    end
  | att p x => 
    n' <- (event_id_span_Term G p e x) ;;
    resultC (2 + n')
  | lseq x y => 
    n1 <- (event_id_span_Term G p e x) ;;
    e' <- eval G p e x ;;
    n2 <- (event_id_span_Term G p e' y) ;;
    resultC (n1 + n2)
  | bseq s x y => 
    n1 <- (event_id_span_Term G p (splitEv_T_l s e) x) ;;
    n2 <- (event_id_span_Term G p (splitEv_T_r s e) y) ;;
    resultC (2 + n1 + n2)
  | bpar s x y => 
    n1 <- (event_id_span_Term G p (splitEv_T_l s e) x) ;;
    n2 <- (event_id_span_Term G p (splitEv_T_r s e) y) ;;
    resultC (2 + n1 + n2)
  end.

Lemma span_range : forall G t t' p i i' e e',
  anno G p e t i = resultC (i', t', e') ->
  event_id_span_Term G p e t = resultC (i' - i).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; simpl in *; try find_injection; try lia.
  - break_match; simpl in *; try find_injection; try (f_equal; lia);
    result_monad_unfold;
    break_match; try congruence; 
    repeat find_injection; try (f_equal; lia);
    break_match; try congruence;
    repeat find_injection; f_equal; lia.
  - result_monad_unfold; ff;
    match goal with
    | H : anno _ _ _ _ _ = _ |- _ => 
      eapply anno_mono in H as ?
    end; ffa;
    repeat find_rewrite; repeat find_injection;
    try (f_equal; lia).
  - result_monad_unfold; ff;
    match goal with
    | H : anno _ _ _ t1 _ = _,
      H1 : anno _ _ _ t2 _ = _ |- _ => 
      eapply anno_mono in H as ?;
      eapply anno_mono in H1 as ?;
      eapply anno_aeval in H as ?;
      eapply anno_aeval in H1 as ?;
      eapply eval_aeval in H as ?;
      eapply eval_aeval in H1 as ?;
      eapply IHt1 in H;
      eapply IHt2 in H1
    end; ffa; repeat find_rewrite; 
    repeat find_injection;
    repeat find_rewrite; repeat find_injection;
    try (f_equal; lia).
  - result_monad_unfold; ff;
    match goal with
    | H : anno _ _ _ t1 _ = _,
      H1 : anno _ _ _ t2 _ = _ |- _ => 
      eapply anno_mono in H as ?;
      eapply anno_mono in H1 as ?;
      eapply anno_aeval in H as ?;
      eapply anno_aeval in H1 as ?;
      repeat find_rewrite; repeat find_injection;
      eapply eval_aeval in H as ?;
      eapply eval_aeval in H1 as ?;
      eapply IHt1 in H;
      repeat find_rewrite; 
      repeat find_injection; try congruence;
      eapply IHt2 in H1;
      repeat find_rewrite; 
      repeat find_injection; try congruence
    end;
    repeat find_injection;
    repeat find_rewrite; repeat find_injection;
    try congruence;
    try (f_equal; lia).
  - result_monad_unfold; ff;
    match goal with
    | H : anno _ _ _ t1 _ = _,
      H1 : anno _ _ _ t2 _ = _ |- _ => 
      eapply anno_mono in H as ?;
      eapply anno_mono in H1 as ?;
      eapply anno_aeval in H as ?;
      eapply anno_aeval in H1 as ?;
      repeat find_rewrite; repeat find_injection;
      eapply eval_aeval in H as ?;
      eapply eval_aeval in H1 as ?;
      eapply IHt1 in H;
      repeat find_rewrite; 
      repeat find_injection; try congruence;
      eapply IHt2 in H1;
      repeat find_rewrite; 
      repeat find_injection; try congruence
    end;
    repeat find_injection;
    repeat find_rewrite; repeat find_injection;
    try congruence;
    try (f_equal; lia).
Qed.

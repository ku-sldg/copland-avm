(* Definition and general properties of Annotated Copland Terms (AnnoTerm).
    Includes annotation and "un-annotation" functions, well-formednesplit_evt predicates, 
    event identifier "span" computations, and their formal properties.
*)


Require Import Term_Defs Preamble.
Require Import StructTactics Defs ResultT String.

Require Import Lia.
Import List.ListNotations.
Import ResultNotation.


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
| aappr : Range -> AnnoTerm
| aatt: Range -> Plc -> AnnoTerm -> AnnoTerm
| alseq: Range -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abseq: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abpar: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm.

(* EvidenceT Type size *)
Fixpoint esize t :=
  match t with
  | aasp _ _ => 1
  | aappr _ => 1
  | aatt _ _ t1 => 2 + esize t1
  | alseq _ t1 t2 => esize t1 + esize t2
  | abseq _ _ t1 t2 => 2 + esize t1 + esize t2
  | abpar _ _ t1 t2 => 2 + esize t1 + esize t2
  end.

(* Extract Range from each annotated term *)
Definition range x :=
  match x with
  | aasp r _ => r
  | aappr r => r
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

(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *)
Fixpoint anno (t: Term) (i:nat) : (nat * AnnoTerm) :=
  match t with
  | asp x => (S i, (aasp (i, S i) x))
  
  | appr => (S i, aappr (i, S i))

  | att p x =>
    let '(j,a) := anno x (S i)  in
    (S j, aatt (i, S j) p a)

  | lseq x y =>
    let '(j,a) := anno x i in
    let '(k,bt) := anno y j in
    (k, alseq (i, k) a bt)

  | bseq s x y =>
    let '(j,a) := anno x (S i) in
    let '(k,b) := anno y j in
    (S k, abseq (i, S k) s a b)

  | bpar s x y =>
    let '(j,a) := anno x (S i) in
    let '(k,b) := anno y j in
    (S k, abpar (i, S k) s a b)
  end.

Definition annotated x :=
  snd (anno x 0).

Fixpoint unanno a :=
  match a with
  | aasp _ a => asp a
  | aappr _ => appr
  | aatt _ p t => att p (unanno t)
  | alseq _ a1 a2 => lseq (unanno a1) (unanno a2)                 
  | abseq _ spl a1 a2 => bseq spl (unanno a1) (unanno a2) 
  | abpar _ spl a1 a2 => bpar spl (unanno a1) (unanno a2)
  end.

Lemma anno_unanno: forall t i,
    unanno (snd (anno t i)) = t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ff; rw using ff.
Qed.

(** eval (EvidenceT semantics) for annotated terms. *)

Fixpoint aeval (t : AnnoTerm) (p : Plc) (e : EvidenceT) (cm : ASP_Compat_MapT) 
    : ResultT EvidenceT string :=
  match t with
  | aasp _ x => eval (asp x) p e cm
  | aappr _ => eval appr p e cm
  | aatt _ q x => aeval x q e cm
  | alseq _ t1 t2 => 
      e1 <- aeval t1 p e cm ;;
      aeval t2 p e1 cm
  | abseq _ s t1 t2 => 
      e1 <- aeval t1 p (splitEv_T_l s e) cm ;;
      e2 <- aeval t2 p (splitEv_T_r s e) cm ;;
      resultC (split_evt e1 e2)
  | abpar _ s t1 t2 => 
      e1 <- aeval t1 p (splitEv_T_l s e) cm ;;
      e2 <- aeval t2 p (splitEv_T_r s e) cm ;;
      resultC (split_evt e1 e2)
  end.

Lemma eval_aeval:
  forall t p e i cm t',
    t' = snd (anno t i) ->
    eval t p e cm = aeval t' p e cm.
Proof.
  induction t; simpl in *; intuition; eauto;
  ff;
  try (erewrite IHt1; rw; eauto;
  erewrite IHt2; rw; eauto).
  - eapply IHt; rw; eauto.
  - erewrite IHt1; rw; eauto;
    ffa using (result_monad_unfold; eauto);
    erewrite IHt2; rw; eauto.
Qed.


(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)
Inductive well_formed_r_annt: AnnoTerm -> Prop :=
| wf_asp_r_annt: forall r x,
    snd r = S (fst r) ->
    well_formed_r_annt (aasp r x)

| wf_appr_r_annt: forall r,
    snd r = S (fst r) ->
    well_formed_r_annt (aappr r)

| wf_att_r_annt: forall r p x,
    well_formed_r_annt x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->
    well_formed_r_annt (aatt r p x)               

| wf_lseq_r_annt: forall r x y,
    well_formed_r_annt x -> well_formed_r_annt y ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) -> 
    well_formed_r_annt (alseq r x y)               
| wf_bseq_r_annt: forall r s x y,
    well_formed_r_annt x -> well_formed_r_annt y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->  
    well_formed_r_annt (abseq r s x y)              
| wf_bpar_r_annt: forall r s x y,
    well_formed_r_annt x -> well_formed_r_annt y ->  
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    (*fst (range y) > fst (range x) -> *)
    well_formed_r_annt (abpar r s x y).
#[export] Hint Constructors well_formed_r_annt : core.


Lemma same_anno_range: forall t i a b n n',
    anno t i = (n,a) ->
    anno t i = (n',b) ->
    n = n'.
Proof.
  induction t; intros; ff.
Qed.
  
Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm),
  anno t i = (j,t') ->
  j > i.
Proof.
  induction t; intuition; ffa; try lia.
Qed.
#[export] Hint Resolve anno_mono : core.

Lemma anno_range:
  forall x i j t',
     anno x i = (j,t') ->
    range (t') = (i, j).
Proof.
  induction x; intros; ff.
Qed.


(** Lemma stating that any annotated term produced via anno is well formed *)
Lemma anno_well_formed_r:
  forall t i j t',
    anno t i = (j, t') ->
    well_formed_r_annt t'.
Proof.
  induction t; intros; ff;
  econstructor; ff;
  try (repeat find_apply_lem_hyp anno_range;
    repeat find_rewrite; ff; fail);
  assert (n > S i) by eauto; lia.
Qed.

(* Computes the length of the "span" or range of event IDs for a given Term *)
Fixpoint event_id_span_Term (t: Term) : nat :=
  match t with
  | asp x => 1
  | appr => 1
  | att p x => 2 + (event_id_span_Term x)
  | lseq x y => (event_id_span_Term x) + (event_id_span_Term y)
  | bseq s x y => 2 + (event_id_span_Term x) + (event_id_span_Term y)
  | bpar s x y => 2 + (event_id_span_Term x) + (event_id_span_Term y)
  end.

(* Same as event_id_span', but for Core Terms *)
Fixpoint event_id_span_Core (t: Core_Term) : nat :=
  match t with
  | aspc CLEAR => 0
  | apprc => 1
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

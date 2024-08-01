(* Definition and general properties of Annotated Copland Terms (AnnoTerm).
    Includes annotation and "un-annotation" functions, well-formedness predicates, 
    event identifier "span" computations, and their formal properties.
*)


Require Import Term_Defs Preamble.
Require Import StructTactics Defs.


Require Import Lia.
Import List.ListNotations.


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

(* Evidence Type size *)
Fixpoint esize t :=
  match t with
  | aasp _ _ => 1
  | aatt _ _ t1 => 2 + esize t1
  | alseq _ t1 t2 => esize t1 + esize t2
  | abseq _ _ t1 t2 => 2 + esize t1 + esize t2
  | abpar _ _ t1 t2 => 2 + esize t1 + esize t2
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

(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *)
Fixpoint anno (t: Term) (i:nat) : (nat * AnnoTerm) :=
  match t with
  | asp x => (S i, (aasp (i, S i) x))

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
  induction t; intros.
  -
    destruct a; ff.
  -
    ff.
    erewrite <- IHt.
    jkjke.
  -
    ff.
    erewrite <- IHt1.
    erewrite <- IHt2.
    jkjke.
    jkjke.
  -
    ff.
    erewrite <- IHt1.
    erewrite <- IHt2.
    jkjke.
    jkjke.
  -
    ff.
    erewrite <- IHt1.
    erewrite <- IHt2.
    jkjke.
    jkjke.
Qed.

(* Propositional versions of anno function equalities *)
Inductive annoP: AnnoTerm -> Term -> Prop :=
| annoP_c: forall anno_term t,
    (exists n n', anno t n = (n',anno_term)) -> (* anno_term = snd (anno t n)) -> *)
    annoP anno_term t.

Inductive annoP_indexed': AnnoTerm -> Term -> nat -> Prop :=
| annoP_c_i': forall anno_term t n,
    (exists n', anno t n = (n', anno_term)) -> (*anno_term = snd (anno t n) -> *)
    annoP_indexed' anno_term t n.

Inductive annoP_indexed: AnnoTerm -> Term -> nat -> nat ->  Prop :=
| annoP_c_i: forall anno_term t n n',
    (*(exists n', anno t n = (n', anno_term)) -> (*anno_term = snd (anno t n) -> *) *)
    anno t n = (n', anno_term) ->
    annoP_indexed anno_term t n n'.


(** eval (evidence semantics) for annotated terms. *)

Fixpoint aeval t p e :=
  match t with
  | aasp _ x => eval (asp x) p e
  | aatt _ q x => aeval x q e
  | alseq _ t1 t2 => aeval t2 p (aeval t1 p e)
  | abseq _ s t1 t2 => ss (aeval t1 p ((splitEv_T_l s e)))
                         (aeval t2 p ((splitEv_T_r s e)))
  | abpar _ s t1 t2 => ss (aeval t1 p ((splitEv_T_l s e)))
                         (aeval t2 p ((splitEv_T_r s e)))
  end.

Lemma eval_aeval:
  forall t p e i,
    eval t p e = aeval (snd (anno t i)) p e.
Proof.
  induction t; intros; simpl; auto;
    repeat expand_let_pairs; simpl;
      try (repeat jkjk; auto;congruence);
      try (repeat jkjk'; auto).
Qed.


(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)
Inductive well_formed_r_annt: AnnoTerm -> Prop :=
| wf_asp_r_annt: forall r x,
    snd r = S (fst r) ->
    well_formed_r_annt (aasp r x)
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
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try destruct a;
    ff.
Qed.
  
Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm),
  anno t i = (j,t') ->
  j > i.
Proof.
  induction t; intros; (*i j t' ls b H; *)
    ff;
    repeat find_apply_hyp_hyp;
    lia.
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
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff.
  -
    ff.
    +
      econstructor.
      eauto.
      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      assert (n > S i) by (eapply anno_mono; eauto).
      lia.
  -
    ff.
    econstructor.
    eauto.
    eauto.

    simpl.
    erewrite anno_range.
    2: {
        eassumption.
      }
    tauto.

    simpl.
    erewrite anno_range.
    2: {
        eassumption.
      }
    erewrite anno_range.
    2: {
        eassumption.
      }
    tauto.

    simpl.
    erewrite anno_range.
    2: {
        eassumption.
      }
    tauto.
      
  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.

      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      erewrite anno_range.
      2: {
        eassumption.
      }
      
      tauto.
      
      simpl.
      erewrite anno_range.
      2: {
        eassumption.
      }
      tauto.     
Qed.

(* Computes the length of the "span" or range of event IDs for a given Term *)
(* TODO: consider changing this to event_id_span_Term *)
Fixpoint event_id_span' (t: Term) : nat :=
  match t with
  | asp x => 1
  | att p x => Nat.add (S (S O)) (event_id_span' x)
  | lseq x y => Nat.add (event_id_span' x) (event_id_span' y)
  | bseq s x y => Nat.add (S (S O)) (Nat.add (event_id_span' x) (event_id_span' y))
  | bpar s x y => Nat.add (S (S O)) (Nat.add (event_id_span' x) (event_id_span' y))
  end.

(* Same as event_id_span', but for Core Terms *)
(* TODO: consider changing this to event_id_span_Core *)
Fixpoint event_id_span (t: Core_Term) : nat :=
  match t with
  | aspc CLEAR =>  O
  | attc _ x => Nat.add (S (S O)) (event_id_span' x)
  | lseqc x y => Nat.add (event_id_span x) (event_id_span y)
  | bseqc x y => Nat.add (S (S O)) (Nat.add (event_id_span x) (event_id_span y))
  | bparc _ x y => Nat.add (S (S O)) (Nat.add (event_id_span x) (event_id_span y))
  | _ => S O
  end.

Lemma event_id_works : forall t,
  event_id_span' t = event_id_span (copland_compile t).
Proof with (simpl in *; eauto).
  induction t...
  - destruct a... destruct s...
  - destruct s, s, s0...
  - destruct s, s, s0...
Qed.


Lemma span_range : forall t i j t',
  anno t i = (j, t') ->
  event_id_span' t = (j - i).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
    try 
    cbn in *;
    find_inversion;
    lia.
  -
    cbn in *.
    repeat break_let.
    find_inversion.
    assert (event_id_span' t = n - (S i)).
    { eauto. }
    rewrite H.
    assert (n > (S i)).
    {
      eapply anno_mono.
      eassumption.
    }
    lia.
  -
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    assert (event_id_span' t1 = (n - i)) by eauto.
    assert (event_id_span' t2 = (j - n)) by eauto.
    repeat jkjke.
    assert (n > i /\ j > n). {
      split; eapply anno_mono; eauto.
    }
    lia.
  -
    cbn in *.
    repeat break_let.
    repeat find_inversion.
    assert (event_id_span' t1 = (n - (S i))) by eauto.
    assert (event_id_span' t2 = (n0 - n)) by eauto.
    repeat jkjke.
    assert (n > S i /\ n0 > n). {
      split; eapply anno_mono; eauto.
    }
    lia.
  -
        cbn in *.
    repeat break_let.
    repeat find_inversion.
    assert (event_id_span' t1 = (n - (S i))) by eauto.
    assert (event_id_span' t2 = (n0 - n)) by eauto.
    repeat jkjke.
    assert (n > S i /\ n0 > n). {
      split; eapply anno_mono; eauto.
    }
    lia.
Qed.

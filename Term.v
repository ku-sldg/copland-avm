(* Copland terms, events, and annotated terms *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** This module contains the basic definitions for Copland terms,
    events, and annotated terms. *)

Require Import Omega Preamble.
Require Import StructTactics.

(** * Terms and Evidence

    A term is either an atomic ASP, a remote call, a sequence of terms
    with data a dependency, a sequence of terms with no data
    dependency, or parallel terms. *)

(** [Plc] represents a place. *)

Notation Plc := nat (only parsing).

(** An argument to a userspace or kernel measurement. *)
(* Notation Arg := nat (only parsing). *)
Notation ASP_ID := nat (only parsing).
Notation N_ID := nat (only parsing).

(*
Definition eq_arg_dec:
  forall x y: Arg, {x = y} + {x <> y}.
Proof.
  intros;
  decide equality; decide equality.
Defined.
Hint Resolve eq_arg_dec.
*)

Inductive ASP: Set :=
| CPY: ASP
(* | KIM: ASP_ID -> Plc -> (list Arg) -> ASP *)
| ASPC: ASP_ID (* -> (list Arg) *) -> ASP
| SIG: ASP
| HSH: ASP.

(** The method by which data is split is specified by a natural number. *)

Inductive SP: Set :=
| ALL
| NONE.

Definition Split: Set := (SP * SP).

Inductive Term: Set :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
                        
| bseq: Split -> Term -> Term -> Term 
| bpar: Split -> Term -> Term -> Term.

(** The structure of evidence. *)

Inductive Evidence: Set :=
| mt: Evidence
(*| sp: SP -> Evidence -> Evidence *)
(* | kk: ASP_ID -> Plc -> Plc -> (list Arg) -> Evidence -> Evidence *)
| uu: ASP_ID -> Plc -> (* (list Arg) -> *) Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: N_ID -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.

Definition splitEv_T (sp:SP) (e:Evidence) : Evidence :=
  match sp with
  | ALL => e
  | NONE => mt
  end.

Inductive splitEv_T_R : SP -> Evidence -> Evidence -> Prop :=
| spAll: forall e, splitEv_T_R ALL e e
| spNone: forall e, splitEv_T_R NONE e mt.

Fixpoint eval_asp t p e :=
  match t with
  | CPY => e
  | ASPC i (*A*) => uu i p (*A*) e
  | SIG => gg p e
  | HSH => hh p e
  end.

(** The evidence associated with a term, a place, and some initial evidence. *)

Fixpoint eval (t:Term) (p:Plc) (e:Evidence) : Evidence :=
  match t with
  | asp a => eval_asp a p e
  | att q t1 => eval t1 q e
  | lseq t1 t2 => eval t2 p (eval t1 p e)
  | bseq s t1 t2 => ss (eval t1 p (splitEv_T (fst s) e))
                       (eval t2 p (splitEv_T (snd s) e)) 
  | bpar s t1 t2 => pp (eval t1 p (splitEv_T (fst s) e))
                      (eval t2 p (splitEv_T (snd s) e))
  end.


Inductive evalR : Term -> Plc -> Evidence -> Evidence -> Prop :=
| evalR_asp: forall a p e,
    evalR (asp a) p e (eval_asp a p e)
| evalR_att: forall t1 q e e' p,
    evalR t1 q e e' ->
    evalR (att q t1) p e e'
| evalR_lseq: forall t1 t2 p e e' e'',
    evalR t1 p e e' ->
    evalR t2 p e' e'' ->
    evalR (lseq t1 t2) p e e''
| evalR_bseq: forall s e e1 e2 e1' e2' p t1 t2,
    splitEv_T_R (fst s) e e1 ->
    splitEv_T_R (snd s) e e2 ->
    evalR t1 p e1 e1' ->
    evalR t2 p e2 e2' ->
    evalR (bseq s t1 t2) p e (ss e1' e2')
| evalR_bpar: forall s e e1 e2 e1' e2' p t1 t2,
    splitEv_T_R (fst s) e e1 ->
    splitEv_T_R (snd s) e e2 ->
    evalR t1 p e1 e1' ->
    evalR t2 p e2 e2' ->
    evalR (bpar s t1 t2) p e (pp e1' e2').

Lemma eval_iff_evalR: forall t p e e',
    evalR t p e e' <-> eval t p e = e'.
Proof.
  split.
  - (* -> case *)
    intros.
    generalize dependent p.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros.
    + destruct a; try (inv H; reflexivity).
    + inv H. simpl.
      eauto.
    + inv H.
      assert (eval t1 p e = e'0).
      eauto.
      subst.
      simpl.
      eauto.
    + inv H.
      assert (eval t1 p e1 = e1') by eauto.
      assert (eval t2 p e2 = e2') by eauto.
      simpl.
      destruct s. simpl.
      destruct s; destruct s0;
        try (simpl; subst; inv H3; inv H4; reflexivity).
    + inv H.
      assert (eval t1 p e1 = e1') by eauto.
      assert (eval t2 p e2 = e2') by eauto.
      simpl.
      destruct s. simpl.
      destruct s; destruct s0;
        try (simpl; subst; inv H3; inv H4; reflexivity).
  - (* <- case *)
    intros.
    generalize dependent p.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros.
    + inv H.
      destruct a; try econstructor.
    + inv H.
      simpl.
      econstructor.
      eauto.
    + econstructor; eauto.
    + destruct s.
      simpl in H.
      destruct s; destruct s0; simpl in *; subst;
        econstructor; (try simpl); eauto; try (econstructor).
    + destruct s.
      simpl in H.
      destruct s; destruct s0; simpl in *; subst;
        econstructor; (try simpl); eauto; try (econstructor).
Defined.


      
      
    
      
      


(** * Events

    There are events for each kind of action. This includes ASP
    actions such as measurement or data processing. It also includes
    control flow actions: a [split] occurs when a thread of control
    splits, and a [join] occurs when two threads join.  Each event is
    distinguished using a unique natural number.

 *)

Inductive Ev: Set :=
| copy: nat -> Plc -> Ev
(* | kmeas: nat -> Plc -> ASP_ID -> Plc -> (list Arg) -> Ev *)
| umeas: nat -> Plc -> ASP_ID -> (* (list Arg) -> *) Ev
| sign: nat -> Plc -> Ev
| hash: nat -> Plc -> Ev
| req: nat -> Plc -> Plc -> Term -> Ev
| rpy: nat -> Plc -> Plc -> Ev 
| split: nat -> Plc -> Ev
| join:  nat -> Plc -> Ev.

Definition eq_ev_dec:
  forall x y: Ev, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality.
Defined.
Hint Resolve eq_ev_dec.

(** The natural number used to distinguish evidence. *)

Definition ev x :=
  match x with
  | copy i _ => i
(*  | kmeas i _ _ _ _ => i *)
  | umeas i _ _ (*_*) => i
  | sign i _ => i
  | hash i _ => i
  | req i _ _ _ => i
  | rpy i _ _ => i 
  | split i _ => i
  | join i _ => i
  end.

(** Events are used in a manner that ensures that
[[
    forall e0 e1, ev e0 = ev e1 -> e0 = e1.
]]
See Lemma [events_injective].
*)

Definition asp_event i x p :=
  match x with
  | CPY => copy i p
(*  | KIM id q A => kmeas i p id q A *)
  | ASPC id (*A*) => umeas i p id (*A*)
  | SIG => sign i p
  | HSH => hash i p
  end.

(** * Annotated Terms

    Annotated terms are used to ensure that each distinct event has a
    distinct natural number.  To do so, each term is annotated by a
    pair of numbers called a range.  Let [(i, k)] be the label for
    term [t].  The labels will be chosen to have the property such
    that for each event in the set of events associated with term [t],
    its number [j] will be in the range [i <= j < k].  *)

Definition Range: Set := nat * nat.

(* Shouldn't need this. Keeping just in case.
Inductive AnnASP: Set :=
| aCPY: Range -> AnnASP
| aKIM: Range -> (list Arg) -> AnnASP
| aUSM: Range -> (list Arg) -> AnnASP
| aSIG: Range -> AnnASP
| aHSH: Range -> AnnASP.*)

Inductive AnnoTerm: Set :=
| aasp: Range -> ASP -> AnnoTerm
| aatt: Range -> Plc -> AnnoTerm -> AnnoTerm
| alseq: Range -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abseq: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm 
| abpar: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm.

(** The number of events associated with a term.  The branching terms
add a split and a join to the events of their subterms. Similarly, the
remote calls add a request and receive to the events of their subterm.
*)


Fixpoint esize t :=
  match t with
  | aasp _ _ => 1
  | aatt _ _ t1 => 2 + esize t1
  | alseq _ t1 t2 => esize t1 + esize t2
  | abseq _ _ t1 t2 => 2 + esize t1 + esize t2
  | abpar _ _ t1 t2 => 2 + esize t1 + esize t2
  end.

Definition range x :=
  match x with
  | aasp r _ => r
  | aatt r _ _ => r
  | alseq r _ _ => r
  | abseq r _ _ _ => r 
  | abpar r _ _ _ => r
  end.

(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *)

Fixpoint anno (t: Term) i: nat * AnnoTerm :=
  match t with
  | asp x => (S i, aasp (i, S i) x)
  | att p x =>
    let (j, a) := anno x (S i) in
    (S j, aatt (i, S j) p a)
  | lseq x y =>
    let (j, a) := anno x i in
    let (k, b) := anno y j in
    (k, alseq (i, k) a b)
      
  | bseq s x y =>
    let (j, a) := anno x (S i) in
    let (k, b) := anno y j in
    (S k, abseq (i, S k) s a b) 
  | bpar s x y =>
    let (j, a) := anno x (S i) in
    let (k, b) := anno y j in
    (S k, abpar (i, S k) s a b)
  end.

Lemma anno_mono : forall t i j t',
  anno t i = (j, t') ->
  j > i.
Proof.
  intros.
Admitted.



Lemma anno_range:
  forall x i,
    range (snd (anno x i)) = (i, fst (anno x i)).
Proof.
  induction x; intros; simpl; auto;
    repeat expand_let_pairs;
    simpl; auto.
Qed.

Definition annotated x :=
  snd (anno x 0).

Lemma pairsinv : forall (a a' b b':nat),
    a <> a' -> (a,b) <> (a',b').
Proof.
  intros.
  congruence.
Defined.



Lemma afaf : forall i k s a b t' n,
    (abpar (i, k) s a b) = snd (anno t' n)(*(bpar s x y)*) ->
    (fst (range a)) <> (fst (range b)).
Proof.
  intros.
  destruct t'; try (
                   unfold annotated in H;
                   unfold anno in H;
                   repeat break_let;
                   simpl in *;
                   inv H;
                   tauto).

  (*
  unfold annotated in H.
  unfold anno in H.
  simpl in H.
  inv H.
  simpl in *.
*)
  unfold annotated in *.
  cbn in *.
  remember (anno t'1 (S n)) as oo.
  destruct oo.
  remember (anno t'2 n0) as oo.
  destruct oo.
  
  simpl in *.
  repeat break_let.
  inv H.
  assert (n0 > (S n)).
  eapply anno_mono; eauto.
  assert (n1 > n0).
  eapply anno_mono; eauto.
  assert ( range (snd (anno t'1 (S n))) = ((S n), fst (anno t'1 (S n)))).
  eapply anno_range; eauto.
  subst.
  rewrite <- Heqoo in H2.
  simpl in *.

  assert ( range (snd (anno t'2 n0)) = (n0, fst (anno t'2 n0))).
  eapply anno_range; eauto.
  simpl in *.
  subst.
  rewrite <- Heqoo0 in H3.
  simpl in *.
  subst.
  intros.
  rewrite H2.
  rewrite H3.
  simpl in *.
  omega.
Defined.

Fixpoint unanno a :=
  match a with
  | aasp _ a => asp a
  | aatt _ p t => att p (unanno t)
  | alseq _ a1 a2 => lseq (unanno a1) (unanno a2)
                         
  | abseq _ spl a1 a2 => bseq spl (unanno a1) (unanno a2) 
  | abpar _ spl a1 a2 => bpar spl (unanno a1) (unanno a2)
  end.



(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)

Inductive well_formed: AnnoTerm -> Prop :=
| wf_asp: forall r x,
    snd r = S (fst r) ->
    well_formed (aasp r x)
| wf_att: forall r p x,
    well_formed x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    well_formed (aatt r p x)
| wf_lseq: forall r x y,
    well_formed x -> well_formed y ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) ->
    well_formed (alseq r x y)
| wf_bseq: forall r s x y,
    well_formed x -> well_formed y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->
    well_formed (abseq r s x y) 
| wf_bpar: forall r s x y,
    well_formed x -> well_formed y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->
    well_formed (abpar r s x y).
Hint Constructors well_formed.


Inductive well_formedn: AnnoTerm -> nat -> Prop :=
| wfn_asp: forall r x n,
    (fst r = n) -> 
    snd r = S (fst r) ->
    well_formedn (aasp r x) n
| wfn_att: forall r p x n,
    (fst r = n) -> 
    well_formedn x (S n) ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    well_formedn (aatt r p x) n
| wfn_lseq: forall r x y n,
    (fst r = n) -> 
    well_formedn x (n) -> well_formedn y (n + (esize x))->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) ->
    well_formedn (alseq r x y) n
| wfn_bseq: forall r s x y n,
    (fst r = n) -> 
    well_formedn x (S n) -> well_formedn y ((S n) + (esize x)) ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->
    well_formedn (abseq r s x y) n
| wfn_bpar: forall r s x y n,
    well_formedn x (S n) -> well_formedn y ((S n) + (esize x)) ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->
    well_formedn (abpar r s x y) n.
Hint Constructors well_formedn.

(*
Lemma afaf' : forall i k s a b,
    well_formed (abpar (i, S k) s a b) (*= annotated (bpar s x y)*) ->
    range a <> range b.
Proof.
  intros.
  inv H.
  simpl in *.
  assert (range a = (S i, fst (range b))).
  admit.
  subst.
  rewrite H.
  assert (range b = (fst(range b), k)).
  admit.
  rewrite H0.
  simpl.
  subst.
  omega.
 *)

Lemma well_formedn_range:
  forall t n,
    well_formedn t n ->
    snd (range t) = fst (range t) + esize t.
Proof.
  
  induction t; intros; simpl; inv H; simpl.
  - rewrite Nat.add_1_r; auto.
  - apply IHt in H4; omega.
  - erewrite IHt1 in *; eauto.
    erewrite IHt2 in *; eauto.
    omega.
  -  erewrite IHt1 in *; eauto.
    erewrite IHt2 in *; eauto.
    omega.
  -
     erewrite IHt1 in *; eauto.
    erewrite IHt2 in *; eauto.
    omega.
Defined.

Lemma well_formed_range:
  forall t,
    well_formed t ->
    snd (range t) = fst (range t) + esize t.
Proof.
    induction t; intros; simpl; inv H; simpl.
  - rewrite Nat.add_1_r; auto.
  -
    erewrite IHt in *; eauto.
    omega.
  - erewrite IHt1 in *; eauto.
    erewrite IHt2 in *; eauto.
    omega.
  -  erewrite IHt1 in *; eauto.
    erewrite IHt2 in *; eauto.
    omega.
  -
     erewrite IHt1 in *; eauto.
    erewrite IHt2 in *; eauto.
    omega.
Defined.

(*
Lemma anno_well_formedn:
  forall t i,
    well_formedn (snd (anno t i)) i.
Proof.
  induction t; intros; simpl; auto.
  -
    repeat expand_let_pairs.
    simpl.
    apply wfn_att; simpl; auto;
      repeat rewrite anno_range; simpl;
        reflexivity.
  - repeat expand_let_pairs.
    simpl.
    apply wfn_lseq; simpl; auto;
      repeat rewrite anno_range; simpl.
    eapply IHt2.
    apply wfn_lseq; simpl; auto;
      repeat rewrite anno_range; simpl;
        reflexivity.
  - repeat expand_let_pairs; simpl.
    apply wf_bseq; simpl; auto;
      repeat rewrite anno_range; simpl;
        reflexivity.
  - repeat expand_let_pairs; simpl.
    apply wf_bpar; simpl; auto;
      repeat rewrite anno_range; simpl;
        reflexivity.
  *)  
  


Lemma anno_well_formed:
  forall t i,
    well_formed (snd (anno t i)).
Proof.
  
  induction t; intros; simpl; auto.
  - repeat expand_let_pairs.
    simpl.
    apply wf_att; simpl; auto;
      rewrite anno_range; simpl; reflexivity.
  - repeat expand_let_pairs.
    simpl.
    apply wf_lseq; simpl; auto;
      repeat rewrite anno_range; simpl;
        reflexivity.
  - repeat expand_let_pairs; simpl.
    apply wf_bseq; simpl; auto;
      repeat rewrite anno_range; simpl;
        reflexivity.
  - repeat expand_let_pairs; simpl.
    apply wf_bpar; simpl; auto;
      repeat rewrite anno_range; simpl;
        reflexivity.
Qed.


(** Eval for annotated terms. *)


Fixpoint aeval t p e :=
  match t with
  | aasp _ x => eval (asp x) p e
  | aatt _ q x => aeval x q e
  | alseq _ t1 t2 => aeval t2 p (aeval t1 p e)
  | abseq _ s t1 t2 => ss (aeval t1 p ((splitEv_T (fst s)) e))
                         (aeval t2 p ((splitEv_T (snd s)) e)) 
  | abpar _ s t1 t2 => pp (aeval t1 p ((splitEv_T (fst s)) e))
                         (aeval t2 p ((splitEv_T (snd s)) e)) 
  end. 


Lemma eval_aeval:
  forall t p e i,
    eval t p e = aeval (snd (anno t i)) p e.
Proof.
  induction t; intros; simpl; auto.
  - repeat expand_let_pairs; simpl;
      rewrite <- IHt; auto.
  - repeat expand_let_pairs.
    simpl.
    rewrite <- IHt1.
    rewrite <- IHt2; auto.
  - repeat expand_let_pairs.
    simpl.
    rewrite <- IHt1.
    rewrite <- IHt2; auto.
    - repeat expand_let_pairs.
    simpl.
    rewrite <- IHt1.
    rewrite <- IHt2; auto.
Qed.

(** This predicate specifies when a term, a place, and some initial
    evidence is related to an event.  In other words, it specifies the
    set of events associated with a term, a place, and some initial
    evidence. *)


Inductive events: AnnoTerm -> Plc -> (*Evidence ->*) Ev -> Prop :=
| evtscpy:
    forall r i p,
      fst r = i ->
      events (aasp r CPY) p (copy i p)
(*| evtskim:
    forall i id r a q p,
      fst r = i ->
      events (aasp r (KIM id q a)) p (kmeas i p id q a) *)
| evtsusm:
    forall i id r p,
      fst r = i ->
      events (aasp r (ASPC id)) p (umeas i p id)
| evtssig:
    forall r i p,
      fst r = i ->
      events (aasp r SIG) p (sign i p) 
| evtshsh:
    forall r i p,
      fst r = i ->
      events (aasp r HSH) p (hash i p)

| evtsattreq:
    forall r q t i p,
      fst r = i ->
      events (aatt r q t) p (req i p q (unanno t))
| evtsatt:
    forall r q t ev p,
      events t q ev ->
      events (aatt r q t) p ev
| evtsattrpy:
    forall r q t i p,
      snd r = S i ->
      events (aatt r q t) p (rpy i p q)
| evtslseql:
    forall r t1 t2 ev p,
      events t1 p ev ->
      events (alseq r t1 t2) p ev
| evtslseqr:
    forall r t1 t2 ev p,
      events t2 p ev ->
      events (alseq r t1 t2) p ev

| evtsbseqsplit:
    forall r i s t1 t2 p,
      fst r = i ->
      events (abseq r s t1 t2) p
             (split i p)
| evtsbseql:
    forall r s t1 t2 ev p,
      events t1 p ev ->
      events (abseq r s t1 t2) p ev
| evtsbseqr:
    forall r s t1 t2 ev p,
      events t2 p ev ->
      events (abseq r s t1 t2) p ev
| evtsbseqjoin:
    forall r i s t1 t2 p,
      snd r = S i ->
      events (abseq r s t1 t2) p
             (join i p)

| evtsbparsplit:
    forall r i s t1 t2 p,
      fst r = i ->
      events (abpar r s t1 t2) p
             (split i p)
| evtsbparl:
    forall r s t1 t2 ev p,
      events t1 p ev ->
      events (abpar r s t1 t2) p ev
| evtsbparr:
    forall r s t1 t2 ev p,
      events t2 p ev ->
      events (abpar r s t1 t2) p ev
| evtsbparjoin:
    forall r i s t1 t2 p,
      snd r = S i ->
      events (abpar r s t1 t2) p
             (join i p).
Hint Constructors events.

Lemma events_range:
  forall t v p,
    well_formed t ->
    events t p v ->
    fst (range t) <= ev v < snd (range t).
Proof.
  
  intros.
  pose proof H as G.
  apply well_formed_range in G.
  rewrite G.
  clear G.
  induction H0; inv H; simpl in *; auto; try omega.
  - apply IHevents in H4; omega.
  - Check well_formed_range.

    apply well_formed_range in H4; omega.
  - apply IHevents in H4; omega.
  - apply IHevents in H5.
    apply well_formed_range in H4.
    omega.
  - apply IHevents in H5; omega.
  - apply IHevents in H6.
    apply well_formed_range in H5.
    omega.
  - apply well_formed_range in H5.
    apply well_formed_range in H6.
    omega.
  - apply IHevents in H5; omega.
  - apply IHevents in H6.
    apply well_formed_range in H5.
    omega.
  - apply well_formed_range in H5.
    apply well_formed_range in H6.
    omega.
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
  destruct G as [G|G]; [left; omega| right].
  pose proof lt_dec i (snd x) as F.
  destruct F as [F|F]; [left; omega| right].
  omega.
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
  destruct G; omega.
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
  intros.
  pose proof lt_dec i (S (fst r)) as G.
  destruct G as [G|G]; [left; omega| right].
  pose proof lt_dec i (snd x) as F.
  destruct F as [F|F]; [left; omega| right].
  pose proof lt_dec i (snd y) as E.
  destruct E; omega.
Qed.

(** Properties of events. *)

Lemma events_range_event:
  forall t i p,
    well_formed t ->
    fst (range t) <= i < snd (range t) ->
    exists v, events t p v /\ ev v = i.
Proof.  
  intros t i p H; revert i; revert p;
  induction H; intros; simpl in *.
  - destruct x; eapply ex_intro; split; auto;
      destruct r as [j k]; simpl in *; omega.
    
  - eapply at_range in H2; eauto.
    repeat destruct_disjunct; subst.
    + eapply ex_intro; split; auto.
    + apply IHwell_formed with (p:=p) in H2.
      destruct H2 as [v].
      destruct H2; subst.
      exists v; split; auto.
    + eapply ex_intro; split.
      apply evtsattrpy; auto.
      * rewrite H1; auto.
      * simpl; auto.
  - apply lin_range with (i:=i) in H2; eauto.
    destruct H2.
    + apply IHwell_formed1 with (p:=p) in H2; auto.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + apply IHwell_formed2 with (p:=p) in H2; auto.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + omega.
  - apply bra_range with (i:=i) (r:=r) in H2; eauto.
    repeat destruct_disjunct; subst.
    + eapply ex_intro; split; auto.
    + apply IHwell_formed1 with (p:=p) in H2.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + apply IHwell_formed2 with (p:=p) in H2.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + eapply ex_intro; split.
      * apply evtsbseqjoin; auto.
        rewrite H3; auto.
      * simpl; auto.
  - apply bra_range with (i:=i) (r:=r) in H2; eauto.
    repeat destruct_disjunct; subst.
    + eapply ex_intro; split; auto.
    + apply IHwell_formed1 with (p:=p) in H2.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + apply IHwell_formed2 with (p:=p) in H2.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + eapply ex_intro; split.
      * apply evtsbparjoin; auto.
        rewrite H3; auto.
      * simpl; auto.
Qed.


Ltac events_event_range :=
  repeat match goal with
         | [ H: events _ _ _ |- _ ] =>
           apply events_range in H; auto
         end; omega.

Lemma events_injective:
  forall t p v1 v2,
    well_formed t ->
    events t p v1 ->
    events t p v2 ->
    ev v1 = ev v2 ->
    v1 = v2.
Proof.
  intros t p v1 v2 H; revert v2; revert v1;
    revert p.
  induction H; intros.
  - inv H0; inv H1; auto.
  - pose proof H as G.
    apply well_formed_range in G.
    inv H2; inv H3; simpl in *; subst; auto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + eauto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
  - pose proof H as G.
    pose proof H0 as G0.
    apply well_formed_range in G.
    apply well_formed_range in G0.
    inv H4; inv H5; simpl in *; auto.
    + eauto.
    + events_event_range.
    + events_event_range.
    + eauto.
  - pose proof H as G.
    pose proof H0 as G0.
    apply well_formed_range in G.
    apply well_formed_range in G0.
    inv H4; inv H5; simpl in *; subst; auto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + eapply IHwell_formed1 in H13; eauto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + eapply IHwell_formed2 in H13; eauto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
  - pose proof H as G.
    pose proof H0 as G0.
    apply well_formed_range in G.
    apply well_formed_range in G0.
    inv H4; inv H5; simpl in *; subst; auto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + eapply IHwell_formed1 in H13; eauto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + eapply IHwell_formed2 in H13; eauto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
Qed.

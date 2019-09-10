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

(** * Terms and Evidence

    A term is either an atomic ASP, a remote call, a sequence of terms
    with data a dependency, a sequence of terms with no data
    dependency, or parallel terms. *)

(** [Plc] represents a place. *)

Notation Plc := nat (only parsing).

(** An argument to a userspace or kernel measurement. *)

(*
Inductive Arg: Set :=
| arg: nat -> Arg
| pl: Plc -> Arg.*)
Notation Arg := nat (only parsing).
Notation ASP_ID := nat (only parsing).
Notation N_ID := nat (only parsing).
Notation BS := nat (only parsing).

Definition eq_arg_dec:
  forall x y: Arg, {x = y} + {x <> y}.
Proof.
  intros;
  decide equality; decide equality.
Defined.
Hint Resolve eq_arg_dec.

Inductive ASP: Set :=
| CPY: ASP
| KIM: ASP_ID -> Plc -> (list Arg) -> ASP
| USM: ASP_ID -> (list Arg) -> ASP
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
| sp: SP -> Evidence -> Evidence
| kk: ASP_ID -> (list Arg) -> Plc -> Plc -> Evidence -> Evidence
| uu: ASP_ID -> (list Arg) -> Plc -> Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: Plc -> N_ID -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.

(** * Concrete Evidence *)
Inductive EvidenceC: Set :=
| mtc: EvidenceC
(*| sp: EvidenceC -> EvidenceC -> EvidenceC*)
| kkc: ASP_ID -> (list Arg) -> (*Plc ->*) Plc -> BS -> EvidenceC -> EvidenceC
| uuc: ASP_ID -> (list Arg) -> (*Plc ->*) BS -> EvidenceC -> EvidenceC
| ggc: (*Plc ->*) EvidenceC -> BS -> EvidenceC
| hhc: (*Plc ->*) BS -> EvidenceC -> EvidenceC
| nnc: (*Plc ->*) N_ID -> BS -> EvidenceC -> EvidenceC
| ssc: EvidenceC -> EvidenceC -> EvidenceC
| ppc: EvidenceC -> EvidenceC -> EvidenceC.

(** * Place-holder axioms for IO operations *)
Definition invokeKIM (i:ASP_ID) (q:Plc) (args:list Arg) : BS.
Admitted.
Definition invokeUSM (i:ASP_ID) (args:list Arg) : BS.
Admitted.
Definition signEv (e:EvidenceC) : BS.
Admitted.
Definition hashEv (e:EvidenceC) : BS.
Admitted.
Definition toRemote (t:Term) (pTo:Plc) (e:EvidenceC) : EvidenceC.
Admitted.
Definition parallel_eval_thread (t:Term) (e:EvidenceC) : EvidenceC.
Admitted.

Fixpoint et_fun (p:Plc) (ec:EvidenceC) : Evidence :=
  match ec with
  | mtc => mt
  | kkc i A q _ ec' => kk i A p q (et_fun p ec')
  | uuc i A _ ec' => uu i A p (et_fun p ec')
  | ggc ec' _ => gg p (et_fun p ec')
  | hhc _ ec' => hh p (et_fun p ec')
  | nnc n _ ec' => nn p n (et_fun p ec')
  | ssc ec1 ec2 => ss (et_fun p ec1) (et_fun p ec2)
  | ppc ec1 ec2 => pp (et_fun p ec1) (et_fun p ec2)
  end.
    
(** * Types *)
Inductive ET: Plc -> EvidenceC -> Evidence -> Prop :=
| mtt: forall p, ET p mtc mt
| kkt: forall id A p q bs e et,
    ET p e et -> 
    ET p (kkc id A q bs e) (kk id A p q et)
| uut: forall id A p bs e et,
    ET p e et -> 
    ET p (uuc id A bs e) (uu id A p et)
| ggt: forall p bs e et,
    ET p e et ->
    ET p (ggc e bs) (gg p et)
| hht: forall p bs e et,
    ET p e et ->
    ET p (hhc bs e) (hh p et)
| nnt: forall p bs e et i,
    ET p e et ->
    ET p (nnc i bs e) (nn p i et)
| sst: forall p e1 e2 e1t e2t,
    ET p e1 e1t ->
    ET p e2 e2t ->
    ET p (ssc e1 e2) (ss e1t e2t)
| ppt: forall p e1 e2 e1t e2t,
    ET p e1 e1t ->
    ET p e2 e2t ->
    ET p (ppc e1 e2) (pp e1t e2t).
Hint Constructors ET.

Theorem et_et_fun : forall p ec,
    ET p ec (et_fun p ec).
Proof.
  intros.
  generalize dependent p.
  induction ec; intros; try (simpl; eauto).
Defined.

Fixpoint typeof_asp t p e :=
  match t with
  | CPY => e
  | KIM i q A => kk i A p q e
  | USM i A => uu i A p e
  | SIG => gg p e
  | HSH => hh p e
  end.

(** The evidence associated with a term, a place, and some initial evidence. *)

Fixpoint typeof (t:Term) (p:Plc) (e:Evidence) : Evidence :=
  match t with
  | asp a => typeof_asp a p e
  | att q t1 => typeof t1 q e
  | lseq t1 t2 => typeof t2 p (typeof t1 p e)
  | bseq s t1 t2 => ss (typeof t1 p (sp (fst s) e))
                       (typeof t2 p (sp (snd s) e))
  | bpar s t1 t2 => pp (typeof t1 p (sp (fst s) e))
                       (typeof t2 p (sp (snd s) e))
  end.


(** * Events

    There are events for each kind of action. This includes ASP
    actions such as measurement or data processing. It also includes
    control flow actions: a [split] occurs when a thread of control
    splits, and a [join] occurs when two threads join.  Each event is
    distinguished using a unique natural number.

 *)

(*
Inductive Ev: Set :=
| copy: nat -> Plc -> Evidence -> Ev
| kmeas: nat -> ASP_ID -> Plc -> (list Arg) -> Evidence -> Evidence -> Ev
| umeas: nat -> ASP_ID -> (*Plc ->*) (list Arg) -> Evidence -> Evidence -> Ev
| sign: nat -> (*Plc ->*) Evidence -> Evidence -> Ev
| hash: nat -> (*Plc ->*) Evidence -> Evidence -> Ev
| req: nat -> Plc -> Plc -> (*Evidence*) Term -> Ev
| rpy: nat -> Plc -> Plc -> Evidence -> Ev
| split: nat -> Plc -> Evidence -> Evidence -> Evidence -> Ev
| join: nat -> Plc -> Evidence -> Evidence -> Evidence -> Ev.*)

Inductive Ev: Set :=
| copy: nat -> (*Plc -> Evidence ->*) Ev
| kmeas: nat -> ASP_ID -> Plc -> (list Arg) -> (*Evidence -> Evidence ->*) Ev
| umeas: nat -> ASP_ID -> (*Plc ->*) (list Arg) -> (*Evidence -> Evidence ->*) Ev
| sign: nat -> (*Plc ->*) (*Evidence -> Evidence ->*) Ev
| hash: nat -> (*Plc ->*) (*Evidence -> Evidence ->*) Ev
| req: nat -> (*Plc ->*) Plc -> (*Evidence*) Term -> Ev
| rpy: nat -> (*Plc ->*) Plc -> (*Evidence ->*) Ev
| split: nat -> (*Plc -> Evidence -> Evidence -> Evidence ->*) Ev
| join:  nat -> (*Plc -> Evidence -> Evidence -> Evidence ->*) Ev.

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
  | copy i => i
  | kmeas i _ _ _ => i
  | umeas i _ _ => i
  | sign i => i
  | hash i => i
  | req i _ _ => i
  | rpy i _ => i
  | split i => i
  | join i => i
  end.

(** Events are used in a manner that ensures that
[[
    forall e0 e1, ev e0 = ev e1 -> e0 = e1.
]]
See Lemma [events_injective].
*)

Definition asp_event i x (*p e*) :=
  match x with
  | CPY => copy i (* p e *)
  | KIM id q A => kmeas i id q A (*e (eval_asp (KIM id q A) p e)*)
  | USM id A => umeas i id A (*e (eval_asp (USM id A) p e)*)
  | SIG => sign i (*e (eval_asp SIG p e)*)
  | HSH => hash i (*e (eval_asp HSH p e)*)
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

Lemma well_formed_range:
  forall t,
    well_formed t ->
    snd (range t) = fst (range t) + esize t.
Proof.
  induction t; intros; simpl; inv H; simpl.
  - rewrite Nat.add_1_r; auto.
  - apply IHt in H3; omega.
  - apply IHt1 in H3.
    apply IHt2 in H4.
    omega.
  - apply IHt1 in H4.
    apply IHt2 in H5.
    omega.
  - apply IHt1 in H4.
    apply IHt2 in H5.
    omega.
Qed.

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
  | aasp _ x => typeof (asp x) p e
  | aatt _ q x => aeval x q e
  | alseq _ t1 t2 => aeval t2 p (aeval t1 p e)
  | abseq _ s t1 t2 => ss (aeval t1 p ((sp (fst s)) e))
                          (aeval t2 p ((sp (snd s)) e))
  | abpar _ s t1 t2 => pp (aeval t1 p ((sp (fst s)) e))
                          (aeval t2 p ((sp (snd s)) e))
  end.

Lemma eval_aeval:
  forall t p e i,
    typeof t p e = aeval (snd (anno t i)) p e.
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

Inductive events: AnnoTerm -> (*Plc -> Evidence ->*) Ev -> Prop :=
| evtscpy:
    forall r i (*p e*),
      fst r = i ->
      events (aasp r CPY) (*p e*) (copy i (*p e*))
| evtskim:
    forall i id r a q,
      fst r = i ->
      (*kk id a p q e = e' -> *)
      events (aasp r (KIM id q a)) (*p e*) (kmeas i id q a (*e e'*))
| evtsusm:
    forall i id r a,
      fst r = i ->
      (*uu id a p e = e' ->*)
      events (aasp r (USM id a)) (*p e*) (umeas i id a (*e e'*))
| evtssig:
    forall r i,
      fst r = i ->
      (*gg p e = e' -> *)
      events (aasp r SIG) (*p e*) (sign i (*e e'*))
| evtshsh:
    forall r i,
      fst r = i ->
      (*hh p e = e' -> *)
      events (aasp r HSH) (*p e*) (hash i (*e e'*))

| evtsattreq:
    forall r q t i,
      fst r = i ->
      events (aatt r q t) (*p e*) (req i q (unanno t))
| evtsatt:
    forall r q t ev,
      events t ev (*q e ev*) ->
      events (aatt r q t) ev (*p e ev*)
| evtsattrpy:
    forall r q t i,
      snd r = S i ->
      (*aeval t q e = e' -> *)
      events (aatt r q t) (*p e*) (rpy i q (*e'*))

| evtslseql:
    forall r t1 t2 ev,
      events t1 (*p e*) ev ->
      events (alseq r t1 t2) (*p e*) ev
| evtslseqr:
    forall r t1 t2 ev,
      events t2 (*p (aeval t1 p e)*) ev ->
      events (alseq r t1 t2) (*p e*) ev

| evtsbseqsplit:
    forall r i s t1 t2,
      fst r = i ->
      events (abseq r s t1 t2) (*p e*)
             (split i (*p e (sp (fst s) e) (sp (snd s) e)*))
| evtsbseql:
    forall r s t1 t2 ev,
      events t1 (*p (sp (fst s) e)*) ev ->
      events (abseq r s t1 t2) (*p e*) ev
| evtsbseqr:
    forall r s t1 t2 ev,
      events t2 (*p (sp (snd s) e)*) ev ->
      events (abseq r s t1 t2) (*p e*) ev
| evtsbseqjoin:
    forall r i s t1 t2,
      snd r = S i ->
      (*aeval t1 p (sp (fst s) e) = e1 ->
      aeval t2 p (sp (snd s) e) = e2 -> *)
      events (abseq r s t1 t2) (*p e*)
             (join i (*p e1 e2 (ss e1 e2)*))

| evtsbparsplit:
    forall r i s t1 t2,
      fst r = i ->
      events (abpar r s t1 t2) (*p e*)
             (split i (*p e (sp (fst s) e) (sp (snd s) e)*))
| evtsbparl:
    forall r s t1 t2 ev,
      events t1 (*p (sp (fst s) e)*) ev ->
      events (abpar r s t1 t2) (*p e*) ev
| evtsbparr:
    forall r s t1 t2 ev,
      events t2 (*p (sp (snd s) e)*) ev ->
      events (abpar r s t1 t2) (*p e*) ev
| evtsbparjoin:
    forall r i s t1 t2,
      snd r = S i ->
      (*aeval t1 p (sp (fst s) e) = e1 ->
      aeval t2 p (sp (snd s) e) = e2 ->*)
      events (abpar r s t1 t2) (*p e*)
             (join i (*p e1 e2 (pp e1 e2)*)).
Hint Constructors events.

Lemma events_range:
  forall t v,
    well_formed t ->
    events t (*p e*) v ->
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
  forall t i,
    well_formed t ->
    fst (range t) <= i < snd (range t) ->
    exists v, events t v /\ ev v = i.
Proof.
  intros t i H; revert i;
  induction H; intros; simpl in *.
  - destruct x; eapply ex_intro; split; auto;
      destruct r as [j k]; simpl in *; omega.
  - eapply at_range in H2; eauto.
    repeat destruct_disjunct; subst.
    + eapply ex_intro; split; auto.
    + apply IHwell_formed in H2.
      destruct H2 as [v].
      destruct H2; subst.
      exists v; split; auto.
    + eapply ex_intro; split.
      apply evtsattrpy; auto.
      * rewrite H1; auto.
      * simpl; auto.
  - apply lin_range with (i:=i) in H2; eauto.
    destruct H2.
    + apply IHwell_formed1 in H2; auto.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + apply IHwell_formed2 in H2; auto.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + omega.
  - apply bra_range with (i:=i) (r:=r) in H2; eauto.
    repeat destruct_disjunct; subst.
    + eapply ex_intro; split; auto.
    + apply IHwell_formed1 in H2.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + apply IHwell_formed2 in H2.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + eapply ex_intro; split.
      * apply evtsbseqjoin; auto.
        rewrite H3; auto.
      * simpl; auto.
  - apply bra_range with (i:=i) (r:=r) in H2; eauto.
    repeat destruct_disjunct; subst.
    + eapply ex_intro; split; auto.
    + apply IHwell_formed1 in H2.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + apply IHwell_formed2 in H2.
      destruct H2 as [v]; destruct H2; subst.
      exists v; split; auto.
    + eapply ex_intro; split.
      * apply evtsbparjoin; auto.
        rewrite H3; auto.
      * simpl; auto.
Qed.

Ltac events_event_range :=
  repeat match goal with
         | [ H: events _ _ |- _ ] =>
           apply events_range in H; auto
         end; omega.

Lemma events_injective:
  forall t v1 v2,
    well_formed t ->
    events t v1 ->
    events t v2 ->
    ev v1 = ev v2 ->
    v1 = v2.
Proof.
  intros t v1 v2 H.
  generalize dependent v1.
  generalize dependent v2.
    induction H; intros; try (inv v1; inv v2; tauto).
  - inv H0; inv H1; auto.
  - pose proof H as G.
    apply well_formed_range in H.
    inv H2; inv H3; simpl in *; auto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
  - pose proof H as G.
    pose proof H0 as G0.
    apply well_formed_range in G.
    apply well_formed_range in G0.
    inv H4; inv H5; simpl in *.
    + auto.
    + events_event_range.
    + events_event_range.
    + auto.
  - pose proof H as G.
    pose proof H0 as G0.
    apply well_formed_range in G.
    apply well_formed_range in G0.
    inv H4; inv H5; simpl in *; try auto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
  - pose proof H as G.
    pose proof H0 as G0.
    apply well_formed_range in G.
    apply well_formed_range in G0.
    inv H4; inv H5; simpl in *; try auto.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
    + events_event_range.
Qed.


(** * Eval function definition *)
Definition splitEv (sp:SP) (e:EvidenceC) : EvidenceC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.

Definition eval_asp (a:ASP) (e:EvidenceC) : EvidenceC :=
  match a with
  | CPY => e
  | KIM i q args =>
    let bs := invokeKIM i q args in
    (kkc i args q bs e)
  | USM i args =>
    let bs := invokeUSM i args in
    (uuc i args bs e)
  | SIG =>
    let bs := signEv e in
    (ggc e bs)
  | HSH =>
    let bs := hashEv e in
    (hhc bs e)
  end.

Fixpoint eval (t:Term) (e:EvidenceC) : EvidenceC :=
  match t with
  | asp a => eval_asp a e
  | att q t1 => toRemote t1 q e
  | lseq t1 t2 =>
    let e1 := eval t1 e in
    eval t2 e1
  | bseq (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := eval t1 e1 in
    let e2' := eval t2 e2 in
    (ssc e1' e2')
  | bpar (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := parallel_eval_thread t1 e1 in
    let e2' := parallel_eval_thread t2 e2 in
    (ppc e1' e2')
  end.
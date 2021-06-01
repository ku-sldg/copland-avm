(* Copland terms, events, and annotated terms *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** This module contains the basic definitions for Copland terms,
    events, and annotated terms. *)

Require Import PeanoNat Nat Compare_dec Lia.
Require Import Preamble StructTactics Defs.

Require Import List.
Import List.ListNotations.

Require Import Coq.Arith.Even Coq.Program.Tactics Coq.Program.Equality.

Require Import Coq.Lists.List Coq.Bool.Bool.

Import Coq.Lists.List.ListNotations.

(*
Require Import List_Facts
*)


(*

Require Import Lists.List.
*)

Set Nested Proofs Allowed.

(*
Require Import OptMonad.
 *)


(** * Terms and Evidence

    A term is either an atomic ASP, a remote call, a sequence of terms
    with data a dependency, a sequence of terms with no data
    dependency, or parallel terms. *)

(** [Plc] represents a place. *)

Notation Plc := nat (only parsing).
(*Notation Loc := nat (only parsing). *)
Notation ASP_ID := nat (only parsing).
Notation TARG_ID := nat (only parsing).
Notation N_ID := nat (only parsing).
Notation Arg := nat (only parsing).

Inductive ASP: Set :=
| CPY: ASP
| ASPC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP
| SIG: ASP
(*| HSH: ASP*) .

Inductive Split: Set :=
| LEFT
| RIGHT
| ALL.

(*
Definition Split: Set := (SP * SP).
*)

Inductive Term: Set :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: Split -> Term -> Term -> Term
| bpar: Split -> Term -> Term -> Term.

(*
Definition LocRange: Set := list Loc.


Definition getTwoLocs (ls:list Loc) (b:bool): option (Loc*Loc) :=
  match b with
  | true => 
    match ls with
    | x :: y :: ls' => ret (x,y)
    | _ => None
    end
  | false => ret (0,0)
  end.
*)

(** The structure of evidence. *)

Inductive Evidence: Set :=
| mt: Evidence
| uu: (*Plc ->*) ASP_ID -> (list Arg) -> Plc -> TARG_ID -> Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
(*| hh: Plc -> Evidence -> Evidence *)
| nn: N_ID -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.

Definition eq_evidence_dec:
  forall x y: Evidence, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality.
Defined.
Hint Resolve eq_evidence_dec : core.

Search (andb).



Scheme Equality for list.
Check list_beq.
Check list_eq_dec.

Lemma eqb_eq_list {A:Type}:
  forall x y f,
    list_beq A f x y = true <-> x = y.
Admitted.

Fixpoint eqb_evidence (e:Evidence) (e':Evidence): bool :=
  match (e,e') with
  | (mt,mt) => true
  | (uu i args p tid e1, uu i' args' p' tid' e2) =>
    (Nat.eqb i i') && (list_beq nat Nat.eqb args args') && (Nat.eqb p p')
    && (Nat.eqb tid tid') && (eqb_evidence e1 e2)
  | (gg p e1, gg p' e2) =>
    (Nat.eqb p p') && (eqb_evidence e1 e2)
  | (nn i e1, nn i' e2) =>
    (Nat.eqb i i') && (eqb_evidence e1 e2)
  | (ss e1 e2, ss e1' e2') =>
    (eqb_evidence e1 e1') && (eqb_evidence e2 e2')
  | (pp e1 e2, pp e1' e2') =>
    (eqb_evidence e1 e1') && (eqb_evidence e2 e2')
  | _ => false
  end.

Lemma eqb_eq_evidence: forall e1 e2,
    eqb_evidence e1 e2 = true <-> e1 = e2.
Proof.
  intros.
  split.
  -
    generalizeEverythingElse e1.
    induction e1; destruct e2; intros;
      try (ff; eauto; tauto).
    +
      ff.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      rewrite eqb_eq_list in H3.

      Search eqb.
      Locate "=?".
      Search Nat.eqb.
      apply EqNat.beq_nat_true in H1.
      apply EqNat.beq_nat_true in H2.
      apply EqNat.beq_nat_true in H.
      subst.
      specialize IHe1 with e2.
      concludes.
      congruence.
    +
      ff.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      apply EqNat.beq_nat_true in H.
      specialize IHe1 with e2.
      concludes.
      congruence.
    +
      ff.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      apply EqNat.beq_nat_true in H.
      specialize IHe1 with e2.
      concludes.
      congruence.
    +
      ff.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      
      specialize IHe1_1 with e2_1.
      specialize IHe1_2 with e2_2.
      concludes.
      concludes.
      congruence.
    +
      ff.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      
      specialize IHe1_1 with e2_1.
      specialize IHe1_2 with e2_2.
      concludes.
      concludes.
      congruence.
  -
    generalizeEverythingElse e1.
    induction e1; destruct e2; intros;
      try (ff; eauto; tauto).
    +
      ff.
      repeat rewrite Bool.andb_true_iff.
      split.
      split.
      split.
      split.
      Search Nat.eqb.
      apply Nat.eqb_refl.

      rewrite eqb_eq_list.
      auto.
      apply Nat.eqb_refl.
      apply Nat.eqb_refl.
      eauto.
    +
      ff.
      repeat rewrite Bool.andb_true_iff.
      split.
      Search Nat.eqb.
      apply Nat.eqb_refl.
      eauto.
    +
      ff.
      repeat rewrite Bool.andb_true_iff.
      split.
      Search Nat.eqb.
      apply Nat.eqb_refl.
      eauto.
    +
      ff.
      repeat rewrite Bool.andb_true_iff.
      split;
        eauto.
    +
      ff.
      repeat rewrite Bool.andb_true_iff.
      split;
      eauto. 
Defined.
  
    

Definition splitEv_T_l (sp:Split) (e:Evidence) : Evidence :=
  match sp with
  | RIGHT => mt
  | _ => e
  end.

Definition splitEv_T_r (sp:Split) (e:Evidence) : Evidence :=
  match sp with
  | LEFT => mt
  | _ => e
  end.

Definition eval_asp t p e :=
  match t with
  | CPY => e 
  | ASPC i l upl targi => uu i l upl targi e
  | SIG => gg p e
  (*| HSH => hh p e *)
  end.

(** The evidence associated with a term, a place, and some initial evidence. *)

Fixpoint eval (t:Term) (p:Plc) (e:Evidence) : Evidence :=
  match t with
  | asp a => eval_asp a p e
  | att q t1 => eval t1 q e
  | lseq t1 t2 => eval t2 p (eval t1 p e)
  | bseq s t1 t2 => ss (eval t1 p (splitEv_T_l s e))
                      (eval t2 p (splitEv_T_r s e))
  | bpar s t1 t2 => pp (eval t1 p (splitEv_T_l s e))
                      (eval t2 p (splitEv_T_r s e))
  end.

(** * Events

    There are events for each kind of action. This includes ASP
    actions such as measurement or data processing. It also includes
    control flow actions: a [split] occurs when a thread of control
    splits, and a [join] occurs when two threads join.  Each event is
    distinguished using a unique natural number.

 *)

Inductive Ev: Set :=
| copy:  nat -> Plc -> Ev 
| umeas: nat -> Plc -> ASP_ID -> (list Arg) -> Plc -> TARG_ID -> Ev
| sign: nat -> Plc -> Ev
(*| hash: nat -> Plc -> Ev *)
| req: nat -> (*Loc ->*) Plc -> Plc -> Term -> Evidence -> Ev
| rpy: nat -> (*Loc -> *) Plc -> Plc -> Ev 
| split: nat -> Plc -> Ev
(*| splitp: nat -> (*Loc ->*) Loc -> Plc -> Ev *)
| join:  nat -> Plc -> Ev
(*| joinp: nat -> Loc -> Loc -> Plc -> Ev *).

Definition eq_ev_dec:
  forall x y: Ev, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality.
Defined.
Hint Resolve eq_ev_dec : core.

(** The natural number used to distinguish events. *)

Definition ev x : nat :=
  match x with
  | copy i _ => i
  | umeas i _ _ _ _ _  => i
  | sign i _ => i
  (*| hash i _ => i *)
  | req i _ _ _ _ => i
  | rpy i _ _ => i 
  | split i _ => i
  (* | splitp i _ _ => i *)
  | join i _ => i
  (* | joinp i _ _ _ => i *)
  end.

(** The natural number indicating the place where an event occured. *)
Definition pl x : Plc :=
  match x with
  | copy _ p => p
  | umeas _ p _ _ _ _  => p
  | sign _ p => p
  (*| hash _ p => p *)
  | req _ p _ _ _ => p
  | rpy _ p _ => p
  | split _ p => p
  (*| splitp _ _ p => p *)
  | join _ p => p
  (* | joinp _ _ _ p => p *)
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
  | ASPC id l upl tid => umeas i p id l upl tid
  | SIG => sign i p
  (*| HSH => hash i p *)
  end.


(** * Annotated Terms

    Annotated terms are used to ensure that each distinct event has a
    distinct natural number.  To do so, each term is annotated by a
    pair of numbers called a range.  Let [(i, k)] be the label for
    term [t].  The labels will be chosen to have the property such
    that for each event in the set of events associated with term [t],
    its number [j] will be in the range [i <= j < k].  *)

Definition Range: Set := nat * nat.

Inductive AnnoTerm: Set :=
| aasp: Range -> (*LocRange ->*) ASP -> AnnoTerm
| aatt: Range -> (*LocRange -> (Loc*Loc) ->*) Plc -> AnnoTerm -> AnnoTerm
| alseq: Range -> (*LocRange ->*) AnnoTerm -> AnnoTerm -> AnnoTerm
| abseq: Range -> (*LocRange ->*) Split -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abpar: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm.

Fixpoint esize t :=
  match t with
  | aasp _ _ => 1
  | aatt _ _ t1 => 2 + (*remote_esize t1*) esize t1
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

(*
Definition lrange x :=
  match x with
  | aasp _ lr _ => lr
  | aatt _ lr _ _ _ => lr
  | alseq _ lr _ _ => lr
  (*| abseq _ lr _ _ _ => lr
  | abpar _ lr _ _ _ _ => lr *)
  end.

Fixpoint anss (t:AnnoTerm) :=
  match t with
  | aasp _ _ _ => 0
  | aatt _ _ _ _ t => 2 (* + (remote_anss t) (*(anss t) + 2*) *)
  | alseq _ _ t1 t2 => anss t1 + anss t2
  (*| abseq _ _ _ t1 t2 => anss t1 + anss t2
  | abpar _ _ _ _ t1 t2 => 2 + anss t1 + anss t2 *)
  end.

(* nss = "num store slots" *)
Fixpoint nss (t:Term) :=
  match t with
  | asp _ => 0
  | att _ t => (*nss t +*) 2
  | lseq t1 t2 => nss t1 + nss t2
  (*| bseq _ t1 t2 => nss t1 + nss t2
  | bpar  _ t1 t2 => 2 + nss t1 + nss t2 *)
  end.

Lemma nss_even: forall t n,
    nss t = n ->
    Nat.even n = true.
Proof.
  induction t; intros.
  -
    destruct a;
    
      cbn in *;
      subst;
      tauto.
  -
    cbn in *.
    eauto.
  -
    cbn in *.
    subst.
    assert (Nat.even (nss t1) = true) by eauto.
    assert (Nat.even (nss t2) = true) by eauto.
    eapply both_args_even; eauto.
    (*
  -
    cbn in *.
    subst.
    assert (Nat.even (nss t1) = true) by eauto.
    assert (Nat.even (nss t2) = true) by eauto.
    eapply both_args_even; eauto.
  -
    cbn in *.
    subst.
    assert (Nat.even (nss t1) = true) by eauto.
    assert (Nat.even (nss t2) = true) by eauto.
    eapply both_args_even; eauto. *)
Defined.
*)

(*
(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *) *)

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
    (*
    ylocs <- getTwoLocs ls b ;;
    (*ylocs <- getTwoLocs (skipn 2 ls) b ;; *) *)
    let '(j,a) := anno x (S i) in
    let '(k,b) := anno y j in
    (S k, abpar (i, S k) s a b)
    (*(fst xlocs :: snd xlocs :: fst ylocs :: snd ylocs :: (lrange a) ++ (lrange bt))*)
  end.

(*
Definition anno' t i ls := fromSome (0, aasp (0,0) [] CPY) (anno t i ls true).
*)

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

  (*
  forall x,
    In x l1 ->
    In x l2.
*)

(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)

(*
Lemma unique_req_events (t:AnnoTerm) : forall p i i0 p1 p2 q q0 t0 t1,
       events t p (req i  loc p1 q  t0) ->
    not (events t p (req i0 loc p2 q0 t1)).
 *)

Inductive well_formed_r: AnnoTerm -> Prop :=
| wf_asp_r: forall r x,
    snd r = S (fst r) ->
    well_formed_r (aasp r x)
| wf_att_r: forall r p x,
    well_formed_r x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->
    well_formed_r (aatt r p x)
                  
| wf_lseq_r: forall r x y,
    well_formed_r x -> well_formed_r y ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) -> 
    well_formed_r (alseq r x y)               
| wf_bseq_r: forall r s x y,
    well_formed_r x -> well_formed_r y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->  
    well_formed_r (abseq r s x y)              
| wf_bpar_r: forall r s x y,
    well_formed_r x -> well_formed_r y ->  
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    (*fst (range y) > fst (range x) -> *)
    well_formed_r (abpar r s x y).
Hint Constructors well_formed_r : core.

(*
Inductive well_formed: AnnoTerm -> Prop :=
| wf_asp: forall r x,
    snd r = S (fst r) ->
    well_formed (aasp r [] x)
| wf_att: forall r ls locs p x,
    well_formed_r x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->

    
    fst locs <> snd locs ->
     
    
    
    In (fst locs) ls ->
    In (snd locs) ls ->

    (*
    NoDup ls ->
     *)
    
    (*
    length ls = 2 ->
     *)
    
    
    well_formed (aatt r ls locs p x)
                
| wf_lseq: forall r ls x y,
    well_formed x -> well_formed y ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) ->

    (*
    NoDup ls ->
     *)
    
     
    
    list_subset (lrange x) ls ->
    list_subset (lrange y) ls ->
    
    
     
    
    (*
    NoDup (lrange x) ->
    NoDup (lrange y) ->
     *)
    

    
    NoDup ((lrange x) ++ (lrange y)) ->
     
    

    (*length ls >= length (lrange x) + length (lrange y) ->  *)
    well_formed (alseq r ls x y)
     (*           
| wf_bseq: forall r ls s x y,
    well_formed x -> well_formed y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->

    (*
    NoDup ls ->
     *)
    
     
    
    list_subset (lrange x) ls ->
    list_subset (lrange y) ls ->

    (*
    NoDup (lrange x) ->
    NoDup (lrange y) ->
     *)
    
    
    NoDup ((lrange x) ++ (lrange y)) ->
     
    

    (*length ls >= length (lrange x) + length (lrange y) ->*)
    well_formed (abseq r ls s x y)
                
| wf_bpar: forall r ls (*xlocs*) ylocs s x y,
    well_formed x -> well_formed y -> 
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    fst (range y) > fst (range x) -> 

    (*
    NoDup ls ->
     *)
    
     
    
    list_subset (lrange x) ls ->
    list_subset (lrange y) ls ->

    list_subset [(*fst xlocs; snd xlocs;*) fst ylocs; snd ylocs] ls ->
    (*
    In (fst xlocs) ls ->
    In (snd xlocs) ls ->
    In (fst ylocs) ls ->
    In (snd ylocs) ls ->
     *)
    
(*
    ~ In (fst xlocs) ([(snd xlocs); (fst ylocs); (snd ylocs)] ++ (lrange x) ++ (lrange y)) ->
    ~ In (snd xlocs) ([(*(fst xlocs);*) (fst ylocs); (snd ylocs)] ++ (lrange x) ++ (lrange y)) ->
    ~ In (fst ylocs) ([(*(fst xlocs); (snd xlocs);*) (snd ylocs)] ++ (lrange x) ++ (lrange y)) ->
    ~ In (snd ylocs) ((*[(fst xlocs); (snd xlocs); (fst ylocs)] ++ *) (lrange x) ++ (lrange y)) ->
 *)
    

    (*
    NoDup (lrange x) ->
    NoDup (lrange y) ->
     *)


    NoDup ([(*(fst xlocs); (snd xlocs);*) (fst ylocs); (snd ylocs)] ++ (lrange x) ++ (lrange y)) ->
    

                (*
    NoDup ((lrange x) ++ (lrange y)) ->
                 *)
                
    (*length ls >= 4 + length (lrange x) + length (lrange y) ->*)
    well_formed (abpar r ls (*xlocs*) ylocs s x y) *) .
Hint Constructors well_formed : core.
*)

Ltac afa :=
  match goal with   
  | [H : forall _, _, H2: Term, H3: nat |- _] => pose_new_proof (H H2 H3)
  end.

Ltac afa' :=
  match goal with   
  | [H : forall _, _, H2: Term, H3: nat |- _] => pose_new_proof (H H2 (S H3))
  end.

Ltac afa'' :=
  match goal with   
  | [H : forall _, _, H2: Term, H3: nat, H4:nat, H5: AnnoTerm |- _] =>
    pose_new_proof (H H2 (H3)(H4) H5)
  end.





Ltac same_index :=
  match goal with
  | [H: anno ?t _ = (?n, _),
        H': anno ?t _ = (?n', _) |- _] =>
    assert_new_proof_by (n = n') eauto
  end.

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
Defined.

(*
    (* Full automation causes proof to take ~3x longer *)
    (*
    try
      (destruct a;
       ff; tauto);
    try (ff; tauto);
    try (
        ff;
        repeat (same_index; subst);
        congruence).
     *)
  -
    destruct a; ff.
  -
    ff.
  -
    ff.
  -
    ff.
Defined.
  
    (*
    repeat (same_index; subst);
      congruence.
     *)
    
    (*
  -
    ff;
    repeat (same_index; subst);
    congruence.
  -
    ff;
      repeat (same_index; subst);
      congruence. *)
 Defined.
*)
  
Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm),
  anno t i = (j,t') ->
  j > i.
Proof.
  induction t; intros; (*i j t' ls b H; *)
    ff;
    repeat find_apply_hyp_hyp;
    lia.
Defined.
Hint Resolve anno_mono : core.

Lemma anno_range:
  forall x i j t',
     anno x i = (j,t') ->
    range (t') = (i, j).
Proof.
  induction x; intros; ff.
Defined.

Ltac haha :=
  let asdff := eapply anno_mono; eauto in
  match goal with
  | [H: anno _ ?x = (?y,_) |- _] => assert_new_proof_by (y > x) (asdff)
  end.

Ltac hehe :=
  match goal with
  | [H: anno ?x ?y = (_,_) |- _] => pose_new_proof (anno_range x y)
  end.

Ltac hehe' :=
  match goal with
  | [x: Term, y:nat |- _] => pose_new_proof (anno_range x (S y))
  end.

Ltac hehe'' :=
  match goal with
  | [x: Term, y:nat |- _] => pose_new_proof (anno_range x y)
  end.

Ltac do_list_empty :=
  match goal with
    [H: length ?ls = 0 |- _] =>
    assert_new_proof_by (ls = []) ltac:(destruct ls; solve_by_inversion)
  end.

(*
Lemma anno_lrange:
  forall x i j ls t' b,
    length ls = nss x ->
    anno x i ls b = Some (j,t') ->
    list_subset ls (lrange t').
Proof.
  induction x; intros;
    try (ff';
         try do_list_empty;
         ff';
         try tauto;
         congruence).
Defined.

Lemma anno_lrange'
  : forall (x : Term) (i j : nat) (ls : list nat) 
      (t' : AnnoTerm),
    (*length ls = nss x -> *)
    anno x i ls true = Some (j, t') ->
    list_subset (lrange t') ls.
Proof.
  intros.
  generalizeEverythingElse x.
  induction x; intros;
    try (ff'; tauto).
Defined.

Lemma both_anno_lrange
  : forall (x : Term) (i j : nat) (ls : list nat) 
      (ls' : LocRange) (t' : AnnoTerm),
    length ls = nss x ->
    anno x i ls true = Some (j,t') ->
    list_subset (lrange t') ls /\ list_subset ls (lrange t').
Proof.
  split.
  - eapply anno_lrange'; eauto.
  - eapply anno_lrange; eauto.
Defined.

Lemma false_succeeds: forall t i ls,
    anno t i ls false = None ->
    False.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try destruct a;
    ff;
    eauto.
Defined.

Lemma nss_iff_anss: forall t i ls n a b,
    anno t i ls b = Some (n,a) ->
    nss t = anss a.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try destruct a;
    ff;
    try eauto;
    try (
        repeat find_apply_hyp_hyp;
        lia).
Defined.

Ltac list_facts' :=
  do_firstn_skipn_len;
  (*do_anno_some_fact; *)
  do_firstn_factt;
  do_firstn_skipn;
  nodup_list_firstn;
  nodup_list_skipn;
  do_nodup_firstn;
  do_nodup_skipn;
  do_nodup_contra.

Lemma anno_some_fact: forall t i ls n a,
    anno t i ls true = Some (n, a) ->
    length ls >= nss t.
Proof.
  induction t; intros.
  -
    ff.
    destruct ls; ff; lia.
  -
    ff.
    lia.
  -
    ff.
    list_facts'.
    
    assert (length ((firstn (nss t1) ls)) >= nss t1) by eauto.
    assert (length (skipn (nss t1) ls) >= nss t2) by eauto.

    (*

    assert (length ls = length (firstn (nss t1) ls) +
                        length (skipn (nss t1) ls)).
    {
      eapply firstn_skipn_len.
    } *)
    lia.
    (*
  -
    ff.
    list_facts'.
    assert (length ((firstn (nss t1) ls)) >= nss t1) by eauto.
    assert (length (skipn (nss t1) ls) >= nss t2) by eauto.
    lia.

  (*

    assert (length ls = length (firstn (nss t1) ls) +
                        length (skipn (nss t1) ls)).
    {
      eapply firstn_skipn_len.
    }
    lia. *)
  -
    ff.
    +
      
      list_facts'.
      assert (length ((firstn (nss t1) l0)) >= nss t1) by eauto.
      assert (length (skipn (nss t1) l0) >= nss t2) by eauto.
      ff.
      lia.

      (*

    +
      list_facts'.
      assert (length ((firstn (nss t1) [])) >= nss t1) by eauto.
      assert (length (skipn (nss t1) []) >= nss t2) by eauto.
      ff.
      lia.
    +
      list_facts'.
      assert (length ((firstn (nss t1) l2)) >= nss t1) by eauto.
      assert (length (skipn (nss t1) l2) >= nss t2) by eauto.
      ff.
      lia. *)
*)
Defined.

Ltac do_anno_some_fact :=
  repeat
    match goal with
    | [H: anno ?t _ ?ls _ = Some (_,_) |- _] =>
      assert_new_proof_by (length ls >= nss t) ltac:(eapply anno_some_fact; apply H)
    end.

Ltac list_facts :=
  do_firstn_skipn_len;
  do_anno_some_fact;
  do_firstn_factt;
  do_firstn_skipn;
  nodup_list_firstn;
  nodup_list_skipn;
  do_nodup_firstn;
  do_nodup_skipn;
  do_nodup_contra.

Lemma list_too_short: forall t i ls,
      anno t i ls true = None ->
      length ls < nss t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff.
  -
    ff.
    exfalso.
    eapply false_succeeds; eauto.
  -
    ff.
    list_facts.
    
    +

      
      assert (length (skipn (nss t1) ls) < nss t2) by eauto.
      lia.

      (*

      assert (length (firstn (nss t1) ls) >= nss t1).
      {
        eapply anno_some_fact; eauto.
      }

      assert (length (firstn (nss t1) ls) = nss t1).
      {
        eapply firstn_factt; eauto.
      }

      assert (length ls = length (firstn (nss t1) ls) + length (skipn (nss t1) ls)).
      {
        eapply firstn_skipn_len; eauto.
      }
      lia. *)

    +
      assert (length (firstn (nss t1) ls) < nss t1) by eauto.
      

      assert (length ls < (nss t1)).
      {
        eapply firstn_fact'; eauto.
      }

      lia.
      (*
  -
    ff.
    list_facts.
    +    
      assert (length (skipn (nss t1) ls) < nss t2) by eauto.
      lia.
      (*

      assert (length (firstn (nss t1) ls) >= nss t1).
      {
        eapply anno_some_fact; eauto.
      }

      assert (length (firstn (nss t1) ls) = nss t1).
      {
        eapply firstn_factt; eauto.
      }

      assert (length ls = length (firstn (nss t1) ls) + length (skipn (nss t1) ls)).
      {
        eapply firstn_skipn_len; eauto.
      }
      lia. *)

    +
      assert (length (firstn (nss t1) ls) < nss t1) by eauto.

      assert (length ls < (nss t1)).
      {
        eapply firstn_fact'; eauto.
      }

      lia.
  -
    ff;
      try (
      list_facts;
      lia).

      
    +
      list_facts.
      assert (length (skipn (nss t1) l0) < nss t2) by eauto.
      ff.
      lia.

      (*

      assert (length (firstn (nss t1) []) = (nss t1)).
      {
        assert (length (firstn (nss t1) l2) >= (nss t1)).
        {
          eapply anno_some_fact; eauto.
        }

        eapply firstn_factt; eauto.
      }

      assert (length l2 = length (firstn (nss t1) l2) + length (skipn (nss t1) l2)).
      {
        eapply firstn_skipn_len; eauto.
      }
      lia. *)
    +

      assert (length (firstn (nss t1) l0) < nss t1) by eauto.
      ff.
      assert (nss t1 > length l0).
      {
        eapply firstn_fact'; eauto.
      }
      
      lia.
*)
Defined.

Lemma anno_some: forall t i l b,
  length l = nss t ->
  exists res,
    anno t i l b = Some res.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff;
      eauto.
  -
    cbn in *.
    assert (exists x y, l = [x; y]).
    {
      destruct l; try solve_by_inversion.
      invc H.
      destruct l; try solve_by_inversion.
      invc H1.
      assert (l = []) by (destruct l; solve_by_inversion).
      subst.
      eauto.
    }
    destruct_conjs.
    subst.
    ff.
    +
      eauto.
    +
      exfalso.
      eapply false_succeeds; eauto.
    +
      destruct b;
        ff.
        
  -
    ff.
    +
      eauto.
    +
      
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto).
    ++
      assert (length ((skipn (nss t1) l)) < nss t2).
      {
        eapply list_too_short; eauto.
      }

      assert (length (firstn (nss t1) l) = nss t1).
      {
        assert (length (firstn (nss t1) l) >= nss t1).
        {
          eapply anno_some_fact; eauto.
        }
        eapply firstn_factt; eauto.
      }

      assert (length l = length (firstn (nss t1) l) + length (skipn (nss t1) l)).
      {
        eapply firstn_skipn_len; eauto.
      }
      lia.
    +
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto).
      ++
        
        assert (length ((firstn (nss t1) l)) < nss t1).
        {
          eapply list_too_short; eauto.
        }
        (*
         assert (length l = length (firstn (nss t1) l) + length (skipn (nss t1) l)).
        {
          eapply firstn_skipn_len; eauto.
        }
         *)
        assert (length l < nss t1).
        {
          eapply firstn_fact'; eauto.
        }
        lia.
        (*

  -
    ff.
    +
      eauto.
    +
      
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto).
      ++
        assert (length ((skipn (nss t1) l)) < nss t2).
        {
          eapply list_too_short; eauto.
        }

        assert (length (firstn (nss t1) l) = nss t1).
        {
          assert (length (firstn (nss t1) l) >= nss t1).
          {
            eapply anno_some_fact; eauto.
          }
          eapply firstn_factt; eauto.
        }

        assert (length l = length (firstn (nss t1) l) + length (skipn (nss t1) l)).
        {
          eapply firstn_skipn_len; eauto.
        }
        lia.
    +
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto).
      ++
        
        assert (length ((firstn (nss t1) l)) < nss t1).
        {
          eapply list_too_short; eauto.
        }
        (*
         assert (length l = length (firstn (nss t1) l) + length (skipn (nss t1) l)).
        {
          eapply firstn_skipn_len; eauto.
        }
         *)
        assert (length l < nss t1).
        {
          eapply firstn_fact'; eauto.
        }
        lia.
  -
    ff;
      try (eauto; tauto);
      try lia.
    +
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto; tauto).
      ++
      
      assert (length (skipn (nss t1) l1) < nss t2).
      {
        eapply list_too_short; eauto.
      }

      assert (length (firstn (nss t1) l1) = nss t1).
      {

        assert (length (firstn (nss t1) l1) >= nss t1).
        {
          eapply anno_some_fact; eauto.
        }

        eapply firstn_factt; eauto.
      }
      list_facts.

      lia.

      (*

      assert (length l3 = length (firstn (nss t1) l3) + length (skipn (nss t1) l3)).
        {
          eapply firstn_skipn_len; eauto.
        }
        lia. *)
    +
       destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto; tauto).
       ++
         assert (length (firstn (nss t1) l1) < nss t1).
         {
           eapply list_too_short; eauto.
         }

         assert (length l1 < nss t1).
         {
           eapply firstn_fact'; eauto.
         }

         lia.
    +
      destruct b.
      ++
        ff.
      ++
        ff.
        (*
    +
      destruct b;
        ff. *)
         *)

        Grab Existential Variables.
        
     
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      (*
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto. *)
Defined.

(*
Lemma anno_len_exact:
  forall t i j ls t',
    anno t i ls true = Some (j, ([], t')) ->
    length ls = anss t'.
Proof.
  intros.
  assert (length ls = anss t' + (length ([]:list nat))).
  {
    eapply anno_len; eauto.
  }
  simpl in *.
  lia.
Defined.
*)



Lemma lrange_nss: forall t i ls  n a,
    length ls = nss t ->
    anno t i ls true = Some (n, a) ->
    length (lrange a) = nss t. (* + length ls'. *)
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    ff.
Defined.

(*

    
    
    ff; eauto.

    assert (length (lrange a0) = nss t1) by eauto.

    assert (length (lrange a1) = nss t2) by eauto.

    assert (length (firstn (nss t1) ls) = nss t1).
    {
      assert (length (firstn (nss t1) ls) >= nss t1).
      {
        eapply anno_some_fact; eauto.
      }

      eapply firstn_factt; eauto.
    }

    (*
    assert (length (skipn (nss t1) ls) = nss t2).
    {
      assert (length (skipn (nss t1) ls) >= nss t2).
      {
        eapply anno_some_fact; eauto.
      }

      
      
      admit.
    }
     *)
    

     assert (length ls = length (firstn (nss t1) ls) + length (skipn (nss t1) ls)).
        {
          eapply firstn_skipn_len; eauto.
        }
    
        lia.
  -
    
    
      
    

    (*assert (length (lrange a0) = nss t1) by eauto. *)

    assert (length ls = anss a0 + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a1).
    {
    
      assert (anss a1 = anss a1 + (length ([]:list nat))).
      {
        eauto.
      }
      rewrite H1.
      
      eapply anno_len; eauto.
    }

    

    


    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    lia.
  -
    ff.
    ff.
    ff; eauto.

    assert (length (lrange a1) = nss t2) by eauto.

    assert (length ls = anss a0 + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a1).
    {
      assert (anss a1 = anss a1 + (length ([]:list nat))).
      {
        eauto.
      }
      rewrite H1.
      
      eapply anno_len; eauto.
    }

    


    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    lia.
  -
    ff.
    ff; eauto.

    assert (length (lrange a1) = nss t2) by eauto.

    assert (length l4 = anss a0 + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a1).
    {
      assert (anss a1 = anss a1 + (length ([]:list nat))).
      {
        eauto.
      }
      rewrite H1.
      
      eapply anno_len; eauto.
    }

    


    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    lia.
Defined.
*)


*)







Lemma anno_well_formed_r:
  forall t i j t',
    (* length ls = nss t ->
    NoDup ls -> *)
    anno t i = (j, t') ->
    well_formed_r t'.
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
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      assert (n0 > S i) by (eapply anno_mono; eauto).
      lia.
      (*
    +
      econstructor.
      eauto.
      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      assert (n0 > S i) by (eapply anno_mono; eauto).
      lia.
    +
      econstructor.
      eauto.
      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      assert (n0 > S i) by (eapply anno_mono; eauto).
      lia. *)
  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
      
  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      (*
      Check anno_range.
      Check anno_mono.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      simpl.

      eapply anno_mono; eauto.
       *)
      
Defined.



      
      (*
  -  
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia.

      econstructor.
      eauto.
      eauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

       assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia.

      econstructor.
      eauto.
      eauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

       assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia.

      (*

            econstructor.
      eauto.
      eauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

       assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia.


            econstructor.
      eauto.
      eauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

       assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia. *)
Defined.
*)




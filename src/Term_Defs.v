(* Copland terms, events, and annotated terms *)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(** This module contains the basic definitions for Copland terms,
    events, and annotated terms. *)

Require Import PeanoNat Compare_dec Lia.
Require Import Preamble StructTactics Term_Facts Defs.

Require Import List.
Import List.ListNotations.

Require Import Coq.Arith.Even Coq.Program.Tactics Coq.Program.Equality.

Require Import OptMonad.



Set Nested Proofs Allowed.

(** * Terms and Evidence

    A term is either an atomic ASP, a remote call, a sequence of terms
    with data a dependency, a sequence of terms with no data
    dependency, or parallel terms. *)

(** [Plc] represents a place. *)

Notation Plc := nat (only parsing).
Notation Loc := nat (only parsing).
Notation ASP_ID := nat (only parsing).
Notation N_ID := nat (only parsing).
Notation Arg := nat (only parsing).

Inductive ASP: Set :=
| CPY: ASP
| ASPC: ASP_ID -> list Arg -> ASP
| SIG: ASP
| HSH: ASP.

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

(** The structure of evidence. *)

Inductive Evidence: Set :=
| mt: Evidence
| uu: ASP_ID -> list Arg -> Plc -> Evidence -> Evidence
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

Definition eval_asp t p e :=
  match t with
  | CPY => e 
  | ASPC i args => uu i args p e
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

(** * Events

    There are events for each kind of action. This includes ASP
    actions such as measurement or data processing. It also includes
    control flow actions: a [split] occurs when a thread of control
    splits, and a [join] occurs when two threads join.  Each event is
    distinguished using a unique natural number.

 *)

Inductive Ev: Set :=
| copy:  nat -> Plc -> Ev 
| umeas: nat -> Plc -> ASP_ID -> list Arg -> Ev
| sign: nat -> Plc -> Ev
| hash: nat -> Plc -> Ev
| req: nat -> Loc -> Plc -> Plc -> Term -> Ev
| rpy: nat -> Loc -> Plc -> Plc -> Ev 
| split: nat -> Plc -> Ev
| splitp: nat -> Loc -> Loc -> Plc -> Ev
| join:  nat -> Plc -> Ev
| joinp: nat -> Loc -> Loc -> Plc -> Ev.

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
  | umeas i _ _ _  => i
  | sign i _ => i
  | hash i _ => i
  | req i _ _ _ _ => i
  | rpy i _ _ _ => i 
  | split i _ => i
  | splitp i _ _ _ => i
  | join i _ => i
  | joinp i _ _ _ => i
  end.

(** The natural number indicating the place where an event occured. *)
Definition pl x : Loc :=
  match x with
  | copy _ p => p
  | umeas _ p _ _  => p
  | sign _ p => p
  | hash _ p => p
  | req _ _ p _ _ => p
  | rpy _ _ p _ => p
  | split _ p => p
  | splitp _ _ _ p => p
  | join _ p => p
  | joinp _ _ _ p => p
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
  | ASPC id args => umeas i p id args
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

Inductive AnnoTerm: Set :=
| aasp: Range -> LocRange -> ASP -> AnnoTerm
| aatt: Range -> LocRange -> (Loc*Loc) -> Plc -> AnnoTerm -> AnnoTerm
| alseq: Range -> LocRange -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abseq: Range -> LocRange -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abpar: Range -> LocRange -> (Loc*Loc) -> (Loc*Loc) -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm.

Fixpoint esize t :=
  match t with
  | aasp _ _ _ => 1
  | aatt _ _ _ _ t1 => 2 + (*remote_esize t1*) esize t1
  | alseq _ _ t1 t2 => esize t1 + esize t2
  | abseq _ _ _ t1 t2 => 2 + esize t1 + esize t2
  | abpar _ _ _ _ _ t1 t2 => 2 + esize t1 + esize t2
  end.

Definition range x :=
  match x with
  | aasp r _ _ => r
  | aatt r _ _ _ _ => r
  | alseq r _ _ _ => r
  | abseq r _ _ _ _ => r
  | abpar r _ _ _ _ _ _ => r
  end.

Definition lrange x :=
  match x with
  | aasp _ lr _ => lr
  | aatt _ lr _ _ _ => lr
  | alseq _ lr _ _ => lr
  | abseq _ lr _ _ _ => lr
  | abpar _ lr _ _ _ _ _ => lr
  end.

Fixpoint anss (t:AnnoTerm) :=
  match t with
  | aasp _ _ _ => 0
  | aatt _ _ _ _ t => 2 (* + (remote_anss t) (*(anss t) + 2*) *)
  | alseq _ _ t1 t2 => anss t1 + anss t2
  | abseq _ _ _ t1 t2 => anss t1 + anss t2
  | abpar _ _ _ _ _ t1 t2 => 4 + anss t1 + anss t2
  end.

(* nss = "num store slots" *)
Fixpoint nss (t:Term) :=
  match t with
  | asp _ => 0
  | att _ t => (*nss t +*) 2
  | lseq t1 t2 => nss t1 + nss t2
  | bseq _ t1 t2 => nss t1 + nss t2
  | bpar  _ t1 t2 => 4 + nss t1 + nss t2
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
    eapply both_args_even; eauto.
Defined.

(*
(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *) *)

Fixpoint anno (t: Term) (i:nat) (ls:LocRange) (b:bool) : option (nat * (* (LocRange **) AnnoTerm)(* ) *) :=
  match t with
  | asp x => ret (S i, (aasp (i, S i) [] x))

  | att p x =>
    '(req_loc,rpy_loc) <- getTwoLocs ls b ;;
    '(j,a) <- anno x (S i) [] false  ;;
    (* TODO: does ls matter here?  Should it be []? *)
    ret (S j, aatt (i, S j) (firstn 2 ls) (req_loc,rpy_loc) p a)

  | lseq x y =>
    '(j,a) <- anno x i (firstn (nss x) ls) b  ;;
    '(k,bt) <- anno y j (skipn (nss x) ls ) b  ;;
    ret (k, alseq (i, k) ls (*(lrange a ++ lrange bt)*) a bt)
 
  | bseq s x y =>
    '(j,a) <- anno x (S i) (firstn (nss x) ls) b  ;;
    '(k,bt) <- anno y j (skipn (nss x) ls ) b  ;;
    ret (S k, abseq (i, S k) ls (*(lrange a ++ lrange bt)*) s a bt)
        
  | bpar s x y =>
    xlocs <- getTwoLocs ls b ;;
    ylocs <- getTwoLocs (skipn 2 ls) b ;;
    '(j,a) <- anno x (S i) (firstn (nss x) (skipn 4 ls)) b  ;;
    '(k,bt) <- anno y j (skipn (nss x) (skipn 4 ls)) b  ;;
    ret (S k, abpar (i, S k) ls xlocs ylocs s a bt)
    (*(fst xlocs :: snd xlocs :: fst ylocs :: snd ylocs :: (lrange a) ++ (lrange bt))*)
  end.

Definition anno' t i ls := fromSome (0, aasp (0,0) [] CPY) (anno t i ls true).

Definition annotated x ls :=
  snd (anno' x 0 ls).

Fixpoint unanno a :=
  match a with
  | aasp _ _ a => asp a
  | aatt _ _ _ p t => att p (unanno t)
  | alseq _ _ a1 a2 => lseq (unanno a1) (unanno a2)
                         
  | abseq _ _ spl a1 a2 => bseq spl (unanno a1) (unanno a2) 
  | abpar _ _ _ _ spl a1 a2 => bpar spl (unanno a1) (unanno a2)
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
| wf_asp_r: forall r x ls,
    snd r = S (fst r) ->
    well_formed_r (aasp r ls x)
| wf_att_r: forall r ls locs p x,
    well_formed_r x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->
    well_formed_r (aatt r ls locs p x)
                  
| wf_lseq_r: forall r ls x y,
    well_formed_r x -> well_formed_r y ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) -> 
    well_formed_r (alseq r ls x y)
                  
| wf_bseq_r: forall r ls s x y,
    well_formed_r x -> well_formed_r y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->  
    well_formed_r (abseq r ls s x y)
                  
| wf_bpar_r: forall r ls xlocs ylocs s x y,
    well_formed_r x -> well_formed_r y ->  
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    fst (range y) > fst (range x) ->     
    well_formed_r (abpar r ls xlocs ylocs s x y).
Hint Constructors well_formed_r : core.

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
                
| wf_bpar: forall r ls xlocs ylocs s x y,
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

    list_subset [fst xlocs; snd xlocs; fst ylocs; snd ylocs] ls ->
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


    NoDup ([(fst xlocs); (snd xlocs); (fst ylocs); (snd ylocs)] ++ (lrange x) ++ (lrange y)) ->
    

                (*
    NoDup ((lrange x) ++ (lrange y)) ->
                 *)
                
    (*length ls >= 4 + length (lrange x) + length (lrange y) ->*)
    well_formed (abpar r ls xlocs ylocs s x y).
Hint Constructors well_formed : core.

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

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

Require Import Coq.Bool.Bool.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.


(** * Terms and Evidence

    A term is either an atomic ASP, a remote call, a sequence of terms
    with data a dependency, a sequence of terms with no data
    dependency, or parallel terms. *)

(** [Plc] represents a place. *)

Notation Plc := nat (only parsing).
Notation ASP_ID := nat (only parsing).
Notation TARG_ID := nat (only parsing).
Notation N_ID := nat (only parsing).
Notation Arg := nat (only parsing).

(*
Definition BS := nat.
 *)

Inductive ASP_PARAMS: Set :=
| asp_paramsC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP_PARAMS.

Inductive ASP: Set :=
| CPY: ASP
| ASPC: ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP.

Inductive SP: Set :=
| ALL
| NONE.

Definition Split: Set := (SP * SP).
(*
Inductive Split: Set :=
| LEFT
| RIGHT
| ALL.
*)

Inductive Term: Set :=
| asp: ASP -> Term
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: Split -> Term -> Term -> Term
| bpar: Split -> Term -> Term -> Term.

(** The structure of evidence. *)

Inductive Evidence: Set :=
| mt: Evidence
| uu: ASP_PARAMS -> Plc -> Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: N_ID -> (*Evidence ->*) Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.

Fixpoint et_size (e:Evidence): nat :=
  match e with
  | mt => 0
  | uu _ _ e' => 1 + (et_size e')
  | gg _ e' => 1 + (et_size e')
  | hh _ _ => 1
  | nn _ => 1
  | ss e1 e2 => (et_size e1) + (et_size e2)
  | pp e1 e2 => (et_size e1) + (et_size e2)
  end.

Fixpoint thread_count (t:Term) : nat :=
  match t with
  | asp _ => 0
  | att _ _ => 0
  | lseq t1 t2 => max (thread_count t1) (thread_count t2)
  | bseq _ t1 t2 => max (thread_count t1) (thread_count t2)
  | bpar _ t1 t2 => 1 + (thread_count t1) + (thread_count t2)
  end.

(*
Fixpoint thread_count' (t:Term) (n:nat) : nat :=
  match t with
  | asp _ => n
  | att _ _ => n
  | lseq t1 t2 => max (thread_count' t1 0) (thread_count' t2 0)
  | bseq _ t1 t2 => max (thread_count' t1 0) (thread_count' t2 0)
  | bpar _ t1 t2 => 1 + (thread_count' t1 0) + (thread_count' t2 0)
  end.

Definition thread_count (t:Term) : nat :=
  thread_count' t 0.
*)

(*
Compute (thread_count (bpar (ALL,ALL) (asp SIG) (asp CPY))).
*)
    
    
Definition splitEv_T_l (sp:Split) (e:Evidence) : Evidence :=
  match sp with
  | (ALL,_) => e
  |  _ => mt
  end.

Definition splitEv_T_r (sp:Split) (e:Evidence) : Evidence :=
  match sp with
  | (_,ALL) => e
  |  _ => mt
  end.

(*
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
 *)

Definition eval_asp t p e :=
  match t with
  | CPY => e 
  | ASPC params => uu params p e
  | SIG => gg p e
  | HSH => hh p e
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

(*
Definition userAM: Plc := 2.
Definition platAM: Plc := 1.
Definition heliAM: Plc := 0.

Definition im_terms: Term :=
  bpar ALL (ASPC 

Definition platSub: Term := 

Definition case_phrase :=
  att userAM 
 *)

(** * Annotated Terms

    Annotated terms are used to ensure that each distinct event has a
    distinct natural number.  To do so, each term is annotated by a
    pair of numbers called a range.  Let [(i, k)] be the label for
    term [t].  The labels will be chosen to have the property such
    that for each event in the set of events associated with term [t],
    its number [j] will be in the range [i <= j < k].  *)

Definition Range: Set := nat * nat.

Inductive AnnoTerm: Set :=
| aasp: Range -> ASP -> AnnoTerm
| aatt: Range -> Plc -> AnnoTerm -> AnnoTerm
| alseq: Range -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abseq: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm
| abpar: Range -> Split -> AnnoTerm -> AnnoTerm -> AnnoTerm.

(** * Events

    There are events for each kind of action. This includes ASP
    actions such as measurement or data processing. It also includes
    control flow actions: a [split] occurs when a thread of control
    splits, and a [join] occurs when two threads join.  Each event is
    distinguished using a unique natural number.

 *)

Definition Loc: Set := nat.
Definition Locs: Set := list Loc.

Inductive Ev: Set :=
| copy:  nat -> Plc -> Ev 
| umeas: nat -> Plc -> ASP_ID -> (list Arg) -> Plc -> TARG_ID -> Ev
| sign: nat -> Plc -> Evidence -> Ev
| hash: nat -> Plc -> Evidence -> Ev
| req: nat -> Plc -> Plc -> Term -> Evidence -> Ev
| rpy: nat -> Plc -> Plc -> Evidence -> Ev 
| split: nat -> Plc -> Ev
| cvm_thread_start: nat -> Loc -> Plc -> AnnoTerm -> Evidence -> Ev
(*| splitp: nat -> (*Loc ->*) Loc -> Plc -> Ev *)
| join:  nat -> Plc -> Ev
| cvm_thread_end:  nat -> Loc -> Plc -> AnnoTerm -> Ev
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
  | sign i _ _ => i
  | hash i _ _ => i
  | req i _ _ _ _ => i
  | rpy i _ _ _ => i 
  | split i _ => i
  | cvm_thread_start i _ _ _ _ => i
  (* | splitp i _ _ => i *)
  | join i _ => i
  | cvm_thread_end i _ _ _ => i
  (* | joinp i _ _ _ => i *)
  end.

(** The natural number indicating the place where an event occured. *)
Definition pl x : Plc :=
  match x with
  | copy _ p => p
  | umeas _ p _ _ _ _  => p
  | sign _ p _ => p
  | hash _ p _ => p
  | req _ p _ _ _ => p
  | rpy _ p _ _ => p
  | split _ p => p
  | cvm_thread_start _ _ p _ _ => p
  (*| splitp _ _ p => p *)
  | join _ p => p
  | cvm_thread_end _ _ p _ => p
  (* | joinp _ _ _ p => p *)
  end.

(** Events are used in a manner that ensures that
[[
    forall e0 e1, ev e0 = ev e1 -> e0 = e1.
]]
See Lemma [events_injective].
 *)


Definition asp_event i x p e :=
  match x with
  | CPY => copy i p
  | ASPC (asp_paramsC id l upl tid) => umeas i p id l upl tid
  | SIG => sign i p e
  | HSH => hash i p e
  end.




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

Inductive AnnoTermPar: Set :=
| aasp_par: Range -> ASP -> AnnoTermPar
| aatt_par: Range -> Plc -> AnnoTerm -> AnnoTermPar
| alseq_par: Range -> AnnoTermPar -> AnnoTermPar -> AnnoTermPar
| abseq_par: Range -> Split -> AnnoTermPar -> AnnoTermPar -> AnnoTermPar
| abpar_par:
    Range -> Loc -> Split -> AnnoTermPar -> AnnoTerm -> AnnoTermPar.

Fixpoint unannoPar (t:AnnoTermPar) : AnnoTerm :=
  match t with
  | aasp_par r a => aasp r a
  | aatt_par r p t => aatt r p t
  | alseq_par r a1 a2 => alseq r (unannoPar a1) (unannoPar a2)                 
  | abseq_par r spl a1 a2 => abseq r spl (unannoPar a1) (unannoPar a2) 
  | abpar_par r _ spl a1 a2 => abpar r spl (unannoPar a1) a2
  end.
  

Definition range_par x :=
  match x with
  | aasp_par r _ => r
  | aatt_par r _ _ => r
  | alseq_par r _ _ => r
  | abseq_par r _ _ _ => r
  | abpar_par r _ _ _ _ => r
  end.

Fixpoint anno_par (t:AnnoTerm) (loc:Loc) : (Loc * AnnoTermPar)  :=
  match t with
  | aasp r a => (loc, aasp_par r a)
  | aatt r p t => (loc, aatt_par r p t)
                     
  | alseq r t1 t2 =>
    let '(loc', t1') := anno_par t1 loc in
    let '(loc'', t2') := anno_par t2 loc' in

    (loc'', alseq_par r t1' t2')
      
  | abseq r spl t1 t2 =>
    let '(loc', t1') := anno_par t1 loc in
    let '(loc'', t2') := anno_par t2 loc' in

    (loc'', abseq_par r spl t1' t2')
      
 
  | abpar r spl t1 t2 =>
    let '(loc', t1') := anno_par t1 (S loc) in
    
    (loc', abpar_par r loc spl t1' t2)

  end.

Definition annotated_par x :=
  snd (anno_par x 0).

Inductive term_sub : AnnoTerm -> AnnoTerm -> Prop :=
| termsub_refl_annt: forall t: AnnoTerm, term_sub t t
| aatt_sub_annt: forall t t' r p,
    term_sub t' t ->
    term_sub t' (aatt r p t)
| alseq_subl_annt: forall t' t1 t2 r,
    term_sub t' t1 ->
    term_sub t' (alseq r t1 t2)
| alseq_subr_annt: forall t' t1 t2 r,
    term_sub t' t2 ->
    term_sub t' (alseq r t1 t2)
| abseq_subl_annt: forall t' t1 t2 r s,
    term_sub t' t1 ->
    term_sub t' (abseq r s t1 t2)
| abseq_subr_annt: forall t' t1 t2 r s,
    term_sub t' t2 ->
    term_sub t' (abseq r s t1 t2)
| abpar_subl_annt: forall t' t1 t2 r s,
    term_sub t' t1 ->
    term_sub t' (abpar r s t1 t2)
| abpar_subr_annt: forall t' t1 t2 r s,
    term_sub t' t2 ->
    term_sub t' (abpar r s t1 t2).
Hint Constructors term_sub : core.

Lemma termsub_transitive: forall t t' t'',
    term_sub t t' ->
    term_sub t' t'' ->
    term_sub t t''.
Proof.  
  generalizeEverythingElse t''.
  induction t'';
    intros H H0; ff.
    (* try (invc H0; eauto). *)
Defined.

(*
Inductive term_sub : AnnoTermPar -> AnnoTermPar -> Prop :=
| termsub_refl: forall t: AnnoTermPar, term_sub t t
| aatt_sub: forall t r loc p tr ta,
    (*term_sub_annt t' t -> *)
    tr = snd (anno_par t loc) ->
    term_sub ta tr ->
    term_sub ta (aatt_par r p t)
| alseq_subl: forall t' t1 t2 r,
    term_sub t' t1 ->
    term_sub t' (alseq_par r t1 t2)
| alseq_subr: forall t' t1 t2 r,
    term_sub t' t2 ->
    term_sub t' (alseq_par r t1 t2)
| abseq_subl: forall t' t1 t2 r s,
    term_sub t' t1 ->
    term_sub t' (abseq_par r s t1 t2)
| abseq_subr: forall t' t1 t2 r s,
    term_sub t' t2 ->
    term_sub t' (abseq_par r s t1 t2)
| abpar_subl: forall t' t1 t2 r loc s,
    term_sub t' t1 ->
    term_sub t' (abpar_par r loc s t1 t2)
| abpar_subr: forall t1 t2 r loc s tpar ta,
    (*term_sub_annt t' t2 -> *)
    tpar = snd (anno_par t2 loc) ->
    term_sub ta tpar ->
    term_sub ta (abpar_par r loc s t1 t2).
Hint Constructors term_sub : core.

Lemma termsub_transitive: forall t t' t'',
    term_sub t t' ->
    term_sub t' t'' ->
    term_sub t t''.
Proof.
  intros.

  assert (term_sub_annt (unannoPar t) (unannoPar t')).
  {
    admit.
  }
  assert (term_sub_annt (unannoPar t') (unannoPar t'')).
  {
    admit.
  }

  Lemma annt_to_termsub: forall t1 t2,
    term_sub_annt (unannoPar t1) (unannoPar t2) ->
    term_sub t1 t2.
  Proof.
  Admitted.

  assert (term_sub_annt (unannoPar t) (unannoPar t'')).
  {
    eapply termsub_transitive_annt; eauto.
  }
  eapply annt_to_termsub; eauto.
  

  find_apply_lem_hyp annt_to_termsub.
  find_apply_lem_hyp annt_to_termsub.
  
    
    
    

    
  eapply termsub_transitive_annt.
  
  




  
  generalizeEverythingElse t''.
  induction t''; intros t t' H H0; ff;
    try (inv H0; eauto; tauto).
  -
    inversion H0.
    +
      subst.
      eauto.
    +
      invc H0.
      eassumption.
      econstructor.
      reflexivity.
      eassumption.
      
    
    econstructor.
    reflexivity.
    eassumption.
    reflexivity.
    eassumption.
  
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

(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)

(*
Lemma unique_req_events (t:AnnoTerm) : forall p i i0 p1 p2 q q0 t0 t1,
       events t p (req i  loc p1 q  t0) ->
    not (events t p (req i0 loc p2 q0 t1)).
 *)



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
Hint Constructors well_formed_r_annt : core.

Inductive well_formed_r: AnnoTermPar -> Prop :=
| wf_asp_r: forall r x,
    snd r = S (fst r) ->
    well_formed_r (aasp_par r x)
| wf_att_r: forall r p x,
    well_formed_r_annt x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->
    well_formed_r (aatt_par r p x)
                  
| wf_lseq_r: forall r x y,
    well_formed_r x -> well_formed_r y ->
    fst r = fst (range_par x) ->
    snd (range_par x) = fst (range_par y) ->
    snd r = snd (range_par y) -> 
    well_formed_r (alseq_par r x y)               
| wf_bseq_r: forall r s x y,
    well_formed_r x -> well_formed_r y ->
    S (fst r) = fst (range_par x) ->
    snd (range_par x) = fst (range_par y) ->
    snd r = S (snd (range_par y)) ->  
    well_formed_r (abseq_par r s x y)              
| wf_bpar_r: forall r loc s x y,
    well_formed_r x -> well_formed_r_annt y ->  
    S (fst r) = fst (range_par x) ->
    snd (range_par x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    (*fst (range y) > fst (range x) -> *)
    well_formed_r (abpar_par r loc s x y).
Hint Constructors well_formed_r : core.

(*
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
      assert (n0 > S i) by (eapply anno_mono; eauto).
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
Defined.




(*
Inductive AnnoTerm_Par: Set :=
| aterm_par: AnnoTerm -> Loc -> AnnoTerm_Par.
 *)

(*

Require Import OptMonad.

Definition peel_loc (ls:Locs) : option (Loc * Locs) :=
  match ls with
  | bs :: ls' => Some (bs, ls')
  | _ => None
  end.

Lemma peel_fact': forall e x y H,
    length e = S x ->
    peel_loc e = Some (y, H) ->
    length H = x.
Proof.
  intros.
  destruct e;
    ff; eauto.
Defined.
 *)




    

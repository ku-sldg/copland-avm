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
Require Import Preamble StructTactics Term_Facts.

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

(*

Inductive TermLoc: Set :=
| lasp: LocRange -> ASP -> TermLoc
| latt: LocRange  -> (Loc*Loc) -> Plc -> Term -> TermLoc
| llseq: LocRange -> TermLoc -> TermLoc -> TermLoc
| lbseq: LocRange -> Split -> TermLoc -> TermLoc -> TermLoc
| lbpar: LocRange -> (Loc*Loc) -> (Loc*Loc) -> Split -> TermLoc -> TermLoc -> TermLoc.

Definition getTwoLocs (ls:list Loc): option (Loc*Loc) :=
  match ls with
  | [x ; y ; ls'] => ret (x,y)
  | _ => None
  end.

Fixpoint annoloc (t: Term) (ls: LocRange) : option (LocRange * TermLoc) :=
  match t with
  | asp x => ret (ls,lasp [] x)


                
  | att p x =>
    (*
    let req_loc := loc in
    let rpy_loc := S loc in
     *)
    '(req_loc,rpy_loc) <- getTwoLocs ls ;;

    ret (skipn 2 ls, latt (firstn 2 ls) (req_loc,rpy_loc) p x)
      

  | lseq x y =>
    '(l',a) <- annoloc x ls ;;
    (* let (l',a) := pr1 in *)
    '(l'',b) <- annoloc y l' ;;
    (* let (l'',b) := pr2 in *)
    ret (l'', llseq ls a b)
      
  | bseq s x y =>
    '(l',a) <- annoloc x ls ;;
    (* let (l',a) := pr1 in *)
    '(l'',b) <- annoloc y l' ;;
    (* let (l'',b) := pr2 in *)
    ret (l'',lbseq ls s a b)

      
  | bpar s x y =>

    '(req_loc,rpy_loc) <- getTwoLocs ls ;;
    '(req_loc',rpy_loc') <- getTwoLocs (skipn 2 ls) ;;

    (*
    let req_loc := loc in
    let rpy_loc := S loc in
    let req_loc' := S (S loc) in
    let rpy_loc' := S (S (S loc)) in
     *)
    
    (* let '(req_loc,rpy_loc) := hd_error l ;;
    let restl := tl l in
    '(req_loc',rpy_loc') <- hd_error restl ;;
    let restl' := tl restl in *)
    '(l',a) <- annoloc x (skipn 4 ls) ;;
    (* let (l',a) := pr1 in *)
    '(l'',b) <- annoloc y l' ;;
    (* let (l'',b) := pr2 in *)
    ret (l'',lbpar ls (req_loc,rpy_loc) (req_loc',rpy_loc') s a b) 
      (* ret (1,([], aasp (0,0) CPY)) *)

     
                
  end.

*)






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

(*
Inductive AnnoEvidence: Set :=
| amt: AnnoEvidence
| auu: nat -> ASP_ID -> Plc -> AnnoEvidence -> AnnoEvidence
| agg: nat -> Plc -> AnnoEvidence -> AnnoEvidence
| ahh: nat -> Plc -> AnnoEvidence -> AnnoEvidence
| ann: (*nat ->*) N_ID -> AnnoEvidence -> AnnoEvidence
| ass: AnnoEvidence -> AnnoEvidence -> AnnoEvidence
| app: AnnoEvidence -> AnnoEvidence -> AnnoEvidence.

Fixpoint eval_asp_i t p e i :=
  match t with
  | CPY => e
  | ASPC x args => auu i x p e
  | SIG => agg i p e
  | HSH => ahh i p e
  end.


Definition splitEv_T_i (sp:SP) (e:AnnoEvidence) : AnnoEvidence :=
  match sp with
  | ALL => e
  | NONE => amt
  end.

Fixpoint annoeval t p (e:AnnoEvidence) :=
  match t with
  | aasp (i,_) x => eval_asp_i x p e i
  | aatt _ q x => annoeval x q e
  | alseq _ t1 t2 => annoeval t2 p (annoeval t1 p e)
  | abseq _ s t1 t2 => ass (annoeval t1 p ((splitEv_T_i (fst s)) e))
                         (annoeval t2 p ((splitEv_T_i (snd s)) e)) 
  | abpar _ s t1 t2 => app (annoeval t1 p ((splitEv_T_i (fst s)) e))
                         (annoeval t2 p ((splitEv_T_i (snd s)) e)) 
  end.
*)

(** The number of events associated with a term.  The branching terms
add a split and a join to the events of their subterms. Similarly, the
remote calls add a request and receive to the events of their subterm.
 *)

Definition remote_esize (t:Term) : nat.
Admitted.

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

Definition remote_anss (t:Term): nat.
Admitted.

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
    (*
    subst.
    assert (Nat.even (nss t) = true) by eauto.
    eapply both_args_even; eauto. *)
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

Fixpoint anno (t: Term) (i:nat) (ls:LocRange) (b:bool) : option (nat * (LocRange * AnnoTerm)):=
  match t with
  | asp x => ret (S i, (ls, (aasp (i, S i) [] x)))

  | att p x =>
    (*
    let req_loc := loc in
    let rpy_loc := S loc in
     *)

    '(req_loc,rpy_loc) <- getTwoLocs ls b ;;

    '(j,(l',a)) <- anno x (S i) [] false  ;;  (* TODO: does ls matter here?  Should it be []? *)
    

    ret (S j, (skipn 2 ls, aatt (i, S j) (firstn 2 ls) (req_loc,rpy_loc) p a))
     
    

    (*
    '(req_loc,rpy_loc) <- getTwoLocs ls ;; *)
    






    
    (*
    '(req_loc,rpy_loc) <- hd_error l ;; *)
    (*let '(req_loc,rpy_loc) (req_loc:Loc) (rpy_loc:Loc) (locs:(Loc*Loc)) := locs in *)
   (* match opt_locs with
    | None => None
    | Some (req_loc,rpy_loc) => *)
    (*let restl := tl l in *)

    (*
    let '(j, a) := anno x (S i) in  (* TODO: 0 ok here?  arg irrelevant? *)
     *)
    
    (*let (j, pr) := res in *)
     (* match maybeRes with
      | None => None
      | Some (j, pr) => *)
        (*let (l',a) := pr in *)
        (*
    (S (S i), aatt (i, S (S i)) ls locs p x) *)

  | lseq x y =>
    '(j,(l',a)) <- anno x i ls b  ;;
    (* let (l',a) := pr1 in *)
    '(k,(l'',b)) <- anno y j l' b  ;;
    (* let (l'',b) := pr2 in *)
    ret (k, (l'', alseq (i, k) ls a b))
 
  | bseq s x y =>
    '(j,(l',a)) <- anno x (S i) ls b  ;;
    (* let (l',a) := pr1 in *)
    '(k,(l'',b)) <- anno y j l' b  ;;
    (* let (l'',b) := pr2 in *)
    ret (S k, (l'',abseq (i, S k) ls s a b))
        

  | bpar s x y =>
    (*
    let req_loc := loc in
    let rpy_loc := S loc in
    let req_loc' := S (S loc) in
    let rpy_loc' := S (S (S loc)) in *)
    (* let '(req_loc,rpy_loc) := hd_error l ;;
    let restl := tl l in
    '(req_loc',rpy_loc') <- hd_error restl ;;
    let restl' := tl restl in *)

    (* '(req_loc,rpy_loc) *)  xlocs <- getTwoLocs ls b ;;
    (* '(req_loc',rpy_loc')*) ylocs <- getTwoLocs (skipn 2 ls) b ;;


    
    '(j,(l',a)) <- anno x (S i) (skipn 4 ls) b  ;;
    (* let (l',a) := pr1 in *)
    '(k,(l'',b)) <- anno y j l' b  ;;
    (* let (l'',b) := pr2 in *)
    ret (S k, (l'', abpar (i, S k) ls xlocs ylocs s a b))
      (* ret (1,([], aasp (0,0) CPY)) *)


           
                
     
       (*         
  | _ => ret (0, ([], aasp (0,0) [] CPY))
        *)
        
      
      
  end.



        
   


(*
(** This function annotates a term.  It feeds a natural number
    throughout the computation so as to ensure each event has a unique
    natural number. *)


    

Fixpoint anno (t: TermLoc) (i:nat) : (nat * AnnoTerm):=
  match t with
  | lasp ls x => (S i, (aasp (i, S i) ls x))


                

  | latt ls locs p x =>
    (*
    let req_loc := loc in
    let rpy_loc := S loc in
     *)

    (*
    '(req_loc,rpy_loc) <- getTwoLocs ls ;; *)
    






    
    (*
    '(req_loc,rpy_loc) <- hd_error l ;; *)
    (*let '(req_loc,rpy_loc) (req_loc:Loc) (rpy_loc:Loc) (locs:(Loc*Loc)) := locs in *)
   (* match opt_locs with
    | None => None
    | Some (req_loc,rpy_loc) => *)
    (*let restl := tl l in *)

    (*
    let '(j, a) := anno x (S i) in  (* TODO: 0 ok here?  arg irrelevant? *)
     *)
    
    (*let (j, pr) := res in *)
     (* match maybeRes with
      | None => None
      | Some (j, pr) => *)
    (*let (l',a) := pr in *)
    (S (S i), aatt (i, S (S i)) ls locs p x)



      

  | llseq ls x y =>
    let '(j,a) := anno x i in
    (* let (l',a) := pr1 in *)
    let '(k,b) := anno y j in
    (* let (l'',b) := pr2 in *)
    (k, alseq (i, k) ls a b)

      
  | lbseq ls s x y =>
    let '(j,a) := anno x (S i) in
    (* let (l',a) := pr1 in *)
    let '(k,b) := anno y j in
    (* let (l'',b) := pr2 in *)
    (S k, abseq (i, S k) ls s a b)

  | lbpar ls xlocs ylocs s x y =>
    (*
    let req_loc := loc in
    let rpy_loc := S loc in
    let req_loc' := S (S loc) in
    let rpy_loc' := S (S (S loc)) in *)
    (* let '(req_loc,rpy_loc) := hd_error l ;;
    let restl := tl l in
    '(req_loc',rpy_loc') <- hd_error restl ;;
    let restl' := tl restl in *)
    let '(j,a) := anno x (S i) in
    (* let (l',a) := pr1 in *)
    let '(k,b) := anno y j in
    (* let (l'',b) := pr2 in *)
    (S k, abpar (i, S k) ls xlocs ylocs s a b)
      (* ret (1,([], aasp (0,0) CPY)) *)

     
     (*           
  | _ => (0, aasp (0,0) [] CPY)
      *)
      
  end.
 *)

Definition anno' t i ls := fromSome (0, ([], aasp (0,0) [] CPY)) (anno t i ls true).




(*
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      cbn in *;
      inv H;
      lia.
  -
    cbn in *.
    repeat break_let.
    subst.
    inv H.
    assert (loc' = S (S loc) + (nss t)) by eauto.
    lia.
  -
    cbn in *;
      repeat break_let.
    subst.
    inv H.
    assert (n0 = loc + (nss t1)) by eauto.
    assert (loc' = n0 + (nss t2)) by eauto.

    lia.
  -
    cbn in *;
      repeat break_let.
    subst.
    inv H.
    assert (n0 = loc + (nss t1)) by eauto.
    assert (loc' = n0 + (nss t2)) by eauto.

    lia.
  -
    cbn in *;
      repeat break_let.
    subst.
    invc H.
    assert (n0 = (S (S (S (S loc)))) + (nss t1)) by eauto.
    assert (loc' = n0 + (nss t2)) by eauto.
    lia.
Defined.
*)

(*
Lemma anno_some: forall t i l,
  length l = nss t ->
  exists res,
    anno t i l = Some res.
Proof.
Admitted.

Definition fromSome{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | None => default
  end.
*)


    

  
  
    

(*    
      
  | lseq x y =>
    let (j, pr1) := anno x i l in
    let (l',a) := pr1 in
    let (k, pr2) := anno y j l' in
    let (l'',b) := pr2 in
    (k, (l'',alseq (i, k) a b))
  | bseq s x y =>
    let (j, pr1) := anno x (S i) l in
    let (l',a) := pr1 in
    let (k, pr2) := anno y j l' in
    let (l'',b) := pr2 in
    (S k, (l'',abseq (i, S k) s a b))
  | bpar s x y =>
    let (req_loc,rpy_loc) := hd (0,0) l in
    let restl := tl l in
    let (req_loc',rpy_loc') := hd (0,0) restl in
    let restl' := tl restl in
    let (j, pr1) := anno x (S i) restl' in
    let (l',a) := pr1 in
    let (k, pr2) := anno y j l' in
    let (l'',b) := pr2 in
    (S k, (l'',abpar (i, S k) (req_loc,rpy_loc) (req_loc',rpy_loc') s a b))
  end.
 *)


Ltac asdf :=
  match goal with
  | [H: _, H2: _ |- _] => apply H in H2
  end.

Ltac ff :=
  repeat (cbn in *;
    repeat break_match; try solve_by_inversion;
    repeat find_inversion).

Lemma same_anno_range: forall t i l l' l2 l2' a b n n' bo bo',
    anno t i l bo = Some (n, (l',a)) ->
    anno t i l2 bo' = Some (n', (l2',b)) ->
    n = n'.
Proof.
Admitted.
  
Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm) (ls ls':LocRange) b,
  anno t i ls b = Some (j, (ls',t')) ->
  j > i.
Proof.
  induction t; intros i j t' ls ls' b H;
    try (
        simpl in *;
        try destruct b;
        repeat break_let;
        repeat break_match;
        try solve_by_inversion;
        find_inversion;
        repeat find_apply_hyp_hyp;
        lia).
Defined.
Hint Resolve anno_mono : core.

Lemma anno_range:
  forall x i j ls ls' t' b,
     anno x i ls b = Some (j, (ls',t')) ->
    
    range (t') = (i, j).
Proof.
  induction x; intros; simpl in *; auto;
    repeat expand_let_pairs;
    repeat break_match;
    try solve_by_inversion;
    simpl; auto.
Defined.

Definition list_subset{A:Type} (l1:list A) (l2:list A) : Prop :=
  forall x,
    In x l1 ->
    In x l2.

Lemma anno_lrange:
  forall x i j ls ls' t' b,
    length ls = nss x ->
    anno x i ls b = Some (j, (ls',t')) ->

    list_subset ls (lrange t').
  (*
    lrange (t') = ls. (* (loc, fst (snd ((anno x i loc)))). *) *)
Proof.
  induction x; intros;
    try (
        simpl in *; auto;
        repeat break_match; try solve_by_inversion;
        repeat find_inversion;
        simpl in *;
        repeat expand_let_pairs;
        repeat break_match; try solve_by_inversion;
        try unfold list_subset;
        simpl in *; tauto).

 (* 
  -
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
*)
      
    
  
  -
    destruct a;
      simpl in *;
      repeat expand_let_pairs;
      repeat break_match;
      find_inversion;
      simpl;
      assert (ls' = []) by (destruct ls'; solve_by_inversion);
      congruence.
  -
    ff.
    assert (ls' = []) by (destruct ls'; solve_by_inversion);
      congruence.
Defined.


Definition annotated x ls :=
  snd (snd (anno' x 0 ls)).

Lemma pairsinv : forall (a a' b b':nat),
    a <> a' -> (a,b) <> (a',b').
Proof.
  intros.
  congruence.
Defined.

Ltac fail_if_in_hyps H := 
  let t := type of H in 
  lazymatch goal with 
  | [G : t |- _ ] => fail "There is already a hypothesis of this proof"
  | [_ : _ |- _ ] => idtac
  end.

Ltac pose_new_proof H := 
  fail_if_in_hyps H;
  pose proof H.

Ltac fail_if_in_hyps_type t := 
  lazymatch goal with 
  | [G : t |- _ ] => fail "There is already a hypothesis of this type"
  | [_ : _ |- _ ] => idtac
  end.

Ltac assert_new_proof_by H tac := 
  fail_if_in_hyps_type H;
  assert H by tac.


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

Ltac find_apply_hyp_hyp' :=
  match goal with
  | [ H : _ -> _ , H' : _ |- _ ] =>
    (*let x := fresh in *)
    pose_new_proof (H H')
  end.

Ltac find_apply_lem_hyp lem :=
  match goal with
    | [ H : _ |- _ ] => apply lem in H
  end.

Ltac find_apply_lem_hyp_new lem :=
  match goal with
    | [ H : _ |- _ ] => pose_new_proof (lem H) (*apply lem in H *)
  end.

Ltac jkjk :=
  match goal with
  | [H: ?X = _ |-  context[?X] ] => rewrite H
  end.

Ltac jkjk' :=
  match goal with
  | [H: ?X = _ |-  context[?X] ] => rewrite <- H
  end.

Fixpoint unanno a :=
  match a with
  | aasp _ _ a => asp a
  | aatt _ _ _ p t => att p (unanno t)
  | alseq _ _ a1 a2 => lseq (unanno a1) (unanno a2)
                         
  | abseq _ _ spl a1 a2 => bseq spl (unanno a1) (unanno a2) 
  | abpar _ _ _ _ spl a1 a2 => bpar spl (unanno a1) (unanno a2)
  end.

(** This predicate determines if an annotated term is well formed,
    that is if its ranges correctly capture the relations between a
    term and its associated events. *)

(*
Lemma unique_req_events (t:AnnoTerm) : forall p i i0 p1 p2 q q0 t0 t1,
       events t p (req i  loc p1 q  t0) ->
    not (events t p (req i0 loc p2 q0 t1)).
 *)

Inductive well_formed: AnnoTerm -> Prop :=
| wf_asp: forall r x,
    snd r = S (fst r) ->
    well_formed (aasp r [] x)
| wf_att: forall r ls locs p x,
    well_formed x ->
    S (fst r) = fst (range x) ->
    snd r = S (snd (range x)) ->
    Nat.pred (snd r) > fst r ->

    In (fst locs) ls ->
    In (snd locs) ls ->
    NoDup ls ->

    length ls = 2 ->

    
    (*
    fst lr = fst locs ->
    snd locs = S (fst locs) ->
    fst (lrange x) = (fst lr) + 2 ->
    snd lr > fst lr ->
    snd (lrange x) = snd lr ->
    (*snd lr = (fst lr) + 2 -> *)
     *)
    
    well_formed (aatt r ls locs p x)
| wf_lseq: forall r ls x y,
    well_formed x -> well_formed y ->
    fst r = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = snd (range y) ->

    NoDup ls ->
    list_subset (lrange x) ls ->
    list_subset (lrange y) ls ->

    length ls = length (lrange x) + length (lrange y) ->
    
    (*
    fst lr = fst (lrange x) ->
    snd (lrange x) = fst (lrange y) ->
    snd lr = snd (lrange y) ->
     *)
    
    well_formed (alseq r ls x y)
| wf_bseq: forall r ls s x y,
    well_formed x -> well_formed y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->

    NoDup ls ->
    list_subset (lrange x) ls ->
    list_subset (lrange y) ls ->

    length ls = length (lrange x) + length (lrange y) ->
    

    (*
    fst lr = fst (lrange x) ->
    snd (lrange x) = fst (lrange y) ->
    snd lr = snd (lrange y) ->
     *)
    
    
    well_formed (abseq r ls s x y)
| wf_bpar: forall r ls xlocs ylocs s x y,
    well_formed x -> well_formed y ->
    (*(rx1,rx2) = (range x) ->
    (ry1,ry2) = (range y) -> *)  
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    (snd r) = S (snd (range y)) ->
    fst (range y) > fst (range x) -> 
    (*r2 > r1 -> *)

    NoDup ls ->
    list_subset (lrange x) ls ->
    list_subset (lrange y) ls ->

    In (fst xlocs) ls ->
    In (snd xlocs) ls ->

    In (fst ylocs) ls ->
    In (snd ylocs) ls ->

    length ls = 4 + length (lrange x) + length (lrange y) ->
    
    

    (*

    fst (lrange x) = S (S (S (S (fst lr)))) ->
    snd xlocs = S (fst xlocs) ->
    fst ylocs = S (snd xlocs) ->
    snd ylocs = S (fst ylocs) ->
    fst lr = fst xlocs ->
    snd lr = snd (lrange y) ->
    S (snd ylocs) = fst (lrange x) ->
    snd (lrange x) = fst (lrange y) ->
     *)
    
    well_formed (abpar r ls xlocs ylocs s x y).

                (*
| wf_bpar: forall r s x y,
    well_formed x -> well_formed y ->
    S (fst r) = fst (range x) ->
    snd (range x) = fst (range y) ->
    snd r = S (snd (range y)) ->
    well_formed (abpar r s x y). *)
Hint Constructors well_formed : core.

Lemma wf_lseq_pieces: forall r lr t1 t2,
    well_formed (alseq r lr t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_at_pieces: forall t r lr locs p,
    well_formed (aatt locs r lr p t) ->
    well_formed t.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_bseq_pieces: forall r lr s t1 t2,
    well_formed (abseq r lr s t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_bpar_pieces: forall r lr xlocs ylocs s t1 t2,
    well_formed (abpar r lr xlocs ylocs s t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Ltac do_wf_pieces :=
  match goal with
  | [H: well_formed (alseq _ _ _ _) |- _] =>
    (edestruct wf_lseq_pieces; eauto)
  | [H: well_formed (aatt _ _ _ _ ?t) |- _] =>   
    assert (well_formed t)
      by (eapply wf_at_pieces; eauto)
  | [H: well_formed (abseq _ _ _ _ _) |- _] =>
    (edestruct wf_bseq_pieces; eauto)
  | [H: well_formed (abpar _ _ _ _ _ _ _) |- _] =>
    (edestruct wf_bpar_pieces; eauto)     
  end.

Lemma well_formed_range:
  forall t,
    well_formed t ->
    snd (range t) = fst (range t) + esize t.
Proof.
  induction t; intros H; simpl; inv H; simpl;
    repeat find_apply_hyp_hyp; lia.
Defined.

Lemma well_formed_lrange:
  forall t,
    well_formed t ->
    length (lrange t) = anss t.
  (*
    snd (lrange t) = fst (lrange t) + anss t. *)
Proof.
  induction t; intros H;
    try (simpl; inv H; simpl; repeat concludes; lia).

  (*
  -
    inv H.
    simpl in *.
    assert (snd l = snd (lrange t)).
    {
      
      admit.
    }
    repeat concludes.
    lia.
    
    inv H.
    repeat concludes.
    subst.
    simpl in *.
    rewrite IHt in *.
*)
    
    
    
Defined.


  (*
  -
    simpl; inv H; simpl.
    repeat concludes.
    
    destruct p; destruct p0; destruct l; destruct r.
    simpl in *.
    subst.
    rewrite <- H9 in *; clear H9.
    rewrite <- H18 in *; clear H18.
    rewrite H19 in *; clear H19.
    rewrite <- H10 in *; clear H10.
*)
    
    

  (*
  -
    cbn.
    inv H.
    rewrite H11.

    repeat concludes.
    lia.
  -
    
    
    
    


  
  -
    destruct p.
    simpl in *.
    subst.
    
    repeat find_apply_hyp_hyp; lia.
*)

Lemma esize_nonempty: forall t, esize t > 0.
Proof.
  intros.
  induction t; intros;
    try (destruct a);
    (cbn; lia).
Defined.

Lemma wf_mono: forall t,
    well_formed t ->
    snd (range t) > fst (range t).
Proof.
  intros.
  rewrite well_formed_range.
  pose (esize_nonempty t).
  lia.
  eauto.
Defined.


(*
Lemma lrange_anno_mono': forall (t:Term) (i j:nat) (t':AnnoTerm) (ls ls':LocRange),
    length ls = nss t ->
    anno t i ls = Some (j, (ls', t')) ->
    length ls = length (lrange t') /\ list_subset ls' ls.
    (* fst (lrange t') >= loc. *)
Proof.
  intros.
  rewrite H in *.
  generalizeEverythingElse t.
  induction t; intros.
  -
    simpl in *.
    destruct a;
      simpl in *;
      repeat find_inversion;
            split;
      try unfold list_subset;
      eauto.    

  -
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    simpl in *.
    repeat break_match; try solve_by_inversion.
  -
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    simpl in *.
    split; try eauto.

    assert (list_subset ls' l).
    {
      eapply IHt2.
      Focus 2.
      eassumption.
      destruct t2.
      +
        cbn in *.
          repeat find_inversion
      

    

    assert 


    
    destruct t; cbn in *; repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    rewrite H in *.
    split; try auto.



    assert (length l = length (lrange t'1) /\ length l0 <= length l).
    {
      eapply IHt'1.


    
    auto.
    
    edestruct IHt1.
    Focus 2.
    eassumption.
    cbn in *.

    edestruct IHt2.
    admit.
    eassumption.
    lia.
    +
      
      
    simpl in *.
    repeat break_match; try solve_by_inversion.
    split.
    
    
      simpl in *.
      lia.
      rewrite H in *.
      lia.
      tauto.
  (*
  induction t; intros i j t' loc loc' H;
    try (
        simpl in *;
        repeat break_let;
        find_inversion;
        repeat find_apply_hyp_hyp;
        simpl;
        lia).
Defined.
   *)
Admitted.
*)


(*
Lemma lrange_anno_mono: forall (t:Term) (i j:nat) (t':AnnoTerm) (loc loc':Loc),
    anno t i loc = (j, (loc', t')) ->
    loc' >= loc.
Proof.
    induction t; intros i j t' loc loc' H;
    try (
        simpl in *;
        repeat break_let;
        find_inversion;
        repeat find_apply_hyp_hyp;
        simpl;
        lia).
Defined.
*)



(*
Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm) (loc loc':Loc),
  anno t i loc = (j, (loc',t')) ->
  j > i.
Proof.
  induction t; intros i j t' loc loc' H;
    try (
        simpl in *;
        repeat break_let;
        find_inversion;
        repeat find_apply_hyp_hyp;
        lia).
Defined.
Hint Resolve anno_mono : core.
 *)



(*
  induction t; intros H;
    try (simpl; inv H; simpl; repeat concludes; lia).
 *)

Lemma anno_len:
  forall t i j ls ls' t',
    anno t i ls true = Some (j, (ls', t')) ->
    length ls = anss t' + length ls'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff.
  -
    ff.
      
  -
    ff.
    assert (length ls = anss a + length l) by eauto.
    assert (length l = anss a0 + length ls') by eauto.
    lia.
  -
    ff.
    assert (length ls = anss a + length l) by eauto.
    assert (length l = anss a0 + length ls') by eauto.
    lia.
  -
    ff.
    assert (length l4 = anss a + length l) by eauto.
    assert (length l = anss a0 + length ls') by eauto.
    lia.
Defined.

Lemma false_succeeds: forall t i ls,
    anno t i ls false = None ->
    False.
Proof.
Admitted.

Lemma nss_iff_anss: forall t i ls n l a b,
    anno t i ls b = Some (n, (l, a)) ->
    nss t = anss a.
Proof.
Admitted.



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
      admit.
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
    eauto.
    destruct b.
    +
      assert (length l0 < nss t2).
      {
        admit.
      }

      assert (length l = anss a + length l0).
      {
        eapply anno_len; eauto.
      }

      assert (nss t1 = anss a).
      {
        eapply nss_iff_anss; eauto.
      }
      lia.
    +
      exfalso.
      eapply false_succeeds; eauto.
    +
      destruct b.
      ++
        assert (length l < nss t1).
        {
          admit.
        }
        lia.
      ++
        exfalso.
        eapply false_succeeds; eauto.
  -
        ff.
    eauto.
    destruct b.
    +
      assert (length l0 < nss t2).
      {
        admit.
      }

      assert (length l = anss a + length l0).
      {
        eapply anno_len; eauto.
      }

      assert (nss t1 = anss a).
      {
        eapply nss_iff_anss; eauto.
      }
      lia.
    +
      exfalso.
      eapply false_succeeds; eauto.
    +
      destruct b.
      ++
        assert (length l < nss t1).
        {
          admit.
        }
        lia.
      ++
        exfalso.
        eapply false_succeeds; eauto.
  -
    ff;
      try (eauto; tauto).
    +
      destruct b.
      ++
        assert (length l0 < nss t2).
        {
          admit.
        }

        assert (length l4 = anss a + length l0).
        {
          eapply anno_len; eauto.
        }
        assert (nss t1 = anss a).
        {
          eapply nss_iff_anss; eauto.
        }
        lia.
      ++
        exfalso.
        eapply false_succeeds; eauto.
    +
      destruct b.
      ++
        assert (length l3 < nss t1).
        {
          admit.
        }

        lia.
      ++
        exfalso.
        eapply false_succeeds; eauto.
    +
      destruct b.
      ++
        assert (length l1 < nss t1).
        {
          admit.
        }
        lia.
      ++
        ff.

    +
      destruct b.
      ++
        assert (length l < 2).
        {
          admit.
        }
        lia.
      ++
        ff.
Admitted.

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

(*
Lemma loc_size: forall t i i' ls ls' annt res,
    anno t i ls = Some (i', (ls', annt)) ->
    res = length (lrange annt) ->
    res = nss t.
Proof.
Admitted.
*)

Lemma lrange_nss: forall t i ls n l a b,
    anno t i ls b = Some (n, (l, a)) ->
    length (lrange a) = nss t.
Proof.
Admitted.

Lemma asp_lrange_irrel: forall a i l l' l2 l2' a0 a1 n n' b,
    anno (asp a) i l b = Some (n, (l',a0)) ->
    anno (asp a) i l2 b= Some(n', (l2',a1)) ->
    a0 = a1.
Proof.
Admitted.

Lemma anno_sub: forall t i n ls l a,
    anno t i ls true = Some (n, (l, a)) ->
    anno t i (lrange a) true = Some (n, ([],a)).
Proof.
  intros.
  edestruct anno_some with (l:=(lrange a)) (t:=t) (i:=i) (b:=true).
  eapply lrange_nss; eauto.
  destruct x; destruct p.
  assert (length (lrange a) = anss a0 + length l0).
  eapply anno_len; eauto.
  assert (length ls = anss a + length l).
  eapply anno_len; eauto.

  (*
  assert (length ls = nss t + (length l)).
  {
    assert (nss t = anss a).
    {
      eapply nss_iff_anss; eauto.
    }
    rewrite H3; clear H3.
    eauto.
  }

  assert (length (lrange a) = nss t + (length l0)).
  {
    assert (nss t = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }
    rewrite H4; clear H4.
    eauto. 
  }
   *)
  


  assert (anss a = nss t).
  {
    symmetry.
    eapply nss_iff_anss; eauto.
  }
  rewrite H3 in *; clear H3.

  assert (anss a0 = nss t).
  {
    symmetry.
    eapply nss_iff_anss; eauto.
  }
  rewrite H3 in *; clear H3.
  
  

  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a.
    +
      assert (ls = l) by ff.
      subst.
      assert (lrange a0 = l0) by ff.
      subst.
      assert (lrange a0 = []) by ff.
      
      rewrite H3 in *. clear H3.
      ff.
    +
       assert (ls = l) by ff.
      subst.
      assert (lrange a0 = l0) by ff.
      subst.
      assert (lrange a0 = []) by ff.
      
      rewrite H3 in *. clear H3.
      ff.
    +
       assert (ls = l) by ff.
      subst.
      assert (lrange a0 = l0) by ff.
      subst.
      assert (lrange a0 = []) by ff.
      
      rewrite H3 in *. clear H3.
      ff.
    +
       assert (ls = l) by ff.
      subst.
      assert (lrange a0 = l0) by ff.
      subst.
      assert (lrange a0 = []) by ff.
      
      rewrite H3 in *. clear H3.
      ff.
  -
    ff.
  -

    assert (length l0 = 0).
    {
      assert (length (lrange a) = nss (lseq t1 t2)).
      {
        eapply lrange_nss; eauto.
      }
      ff.
      lia.
    }
    assert (l0 = []) by (destruct l0; try solve_by_inversion).
    subst.
    clear H3.
    
    
      


    
    ff.

    assert (n3 = n1).
    {
      eapply same_anno_range; eauto.
    }
    subst.
    
    

    assert (n0 = n).
    {
      eapply same_anno_range; eauto.
    }
    subst.

    assert (l2 = l0) by congruence.
    assert (a3 = a1) by congruence.

    assert (l = []) by congruence.
    assert (a4 = a2) by congruence.
    subst.
    eauto.
  -


    assert (length l0 = 0).
    {
      assert (length (lrange a) = nss (bseq s t1 t2)).
      {
        eapply lrange_nss; eauto.
      }
      ff.
      lia.
    }
    assert (l0 = []) by (destruct l0; try solve_by_inversion).
    subst.
    clear H3.

        ff.

    assert (n3 = n1).
    {
      eapply same_anno_range; eauto.
    }
    subst.
    
    

    

    assert (l2 = l0) by congruence.
    assert (a3 = a1) by congruence.

    assert (l = []) by congruence.
    assert (a4 = a2) by congruence.
    subst.
    assert (n2 = n4) by congruence.
    subst.
    eauto.
  -

    assert (length l0 = 0).
    {
      assert (length (lrange a) = nss (bpar s t1 t2)).
      {
        eapply lrange_nss; eauto.
      }
      ff.
      lia.
     
    }
    assert (l0 = []) by (destruct l0; try solve_by_inversion).
    subst.
    clear H3.

    ff.
    assert (n2 = n8) by congruence.
    assert (a1 = a3) by congruence.
    assert (a2 = a4) by congruence.
    subst.
    eauto.
Defined.

Lemma anno_lrange'
  : forall (x : Term) (i j : nat) (ls : list nat) 
      (ls' : LocRange) (t' : AnnoTerm),
    (*length ls = nss x -> *)
    anno x i ls true = Some (j, (ls', t')) -> list_subset (lrange t') ls.
Proof.
  intros.
  generalizeEverythingElse x.
  induction x; intros.
  -
    destruct a;
    
      ff;
      unfold list_subset;
      intros;
      solve_by_inversion.
  -
    ff.
    unfold list_subset.
    intros.
    invc H.
    econstructor.
    eauto.
    invc H0.
    right.
    left.
    eauto.
    solve_by_inversion.
  -
    ff.
    unfold list_subset.
    eauto.
  -
    ff.
    unfold list_subset.
    eauto.
  -
    ff.
    unfold list_subset.
    eauto.
Defined.

(*
Lemma anno_len:
  forall t i j ls ls' t',
    anno t i ls = Some (j, (ls', t')) ->
    length ls = anss t' + length ls'.
 *)

(*
Lemma lrange_nss: forall t i ls n l a,
    anno t i ls = Some (n, (l, a)) ->
    length (lrange a) = nss t.
 *)

(*
Lemma nss_iff_anss: forall t i ls n l a,
    anno t i ls = Some (n, (l, a)) ->
    nss t = anss a.
Proof.
Admitted.
*)


Lemma lrange_len: forall t i ls n l a,
    anno t i ls true = Some (n, (l,a)) ->
    length ls = length (lrange a) + (length l).
Proof.
  intros.
  erewrite lrange_nss.
  Focus 2.
  eassumption.
  erewrite nss_iff_anss.
  Focus 2.
  eassumption.
  eapply anno_len; eauto.
Defined.

Lemma anno_sub': forall t i ls n l a,
    anno t i ls true = Some (n, (l, a)) ->
    list_subset l ls.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
    
      ff;
      unfold list_subset; eauto.
  -
    ff.
    unfold list_subset.
    intros.
    right.
    right.
    eauto.
    (*
    invc H.
    right.
    right.
    econstructor. eauto.
    solve_by_inversion. *)
  -
    ff.
    unfold list_subset.
    intros.

    assert (list_subset l l0) by eauto.

    unfold list_subset in *.
    specialize H0 with (x:=x).
    concludes.

    assert (forall x:nat, In x l0 -> In x ls).
    {
      eapply IHt1; eauto.
    }
    eauto.
  -
    ff.
    unfold list_subset.
    intros.

    assert (list_subset l l0) by eauto.

    unfold list_subset in *.
    specialize H0 with (x:=x).
    concludes.

    assert (forall x:nat, In x l0 -> In x ls).
    {
      eapply IHt1; eauto.
    }
    eauto.
  -

    ff.
    unfold list_subset.
    intros.

    assert (list_subset l l0) by eauto.

    unfold list_subset in *.
    specialize H0 with (x:=x).
    concludes.

    assert (forall x:nat, In x l0 -> In x l5).
    {
      eapply IHt1; eauto.
    }
    right.
    right.
    right.
    right.
    eauto.
    
Defined.

Lemma nodup_sub{A:Type}: forall ls ls':list A,
    NoDup ls ->
    list_subset ls' ls ->
    NoDup ls'.
Proof.
Admitted.

Lemma anno_well_formed:
  forall t i j ls ls' t',
    length ls = nss t ->
    NoDup ls ->
    anno t i ls true = Some (j, (ls', t')) ->
    well_formed t'.
Proof.
  
  induction t; intros; simpl;
    try (auto;
    repeat expand_let_pairs;
    econstructor; simpl; auto;
    repeat rewrite anno_lrange;
    repeat rewrite anno_range; simpl; reflexivity).
  -
   
    destruct a;
    
      cbn in *;
      find_inversion;
      eauto;
    
      assert (ls' = []) by (destruct ls'; solve_by_inversion);
      solve_by_inversion.
  -
    ff.
    (*
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion. *)
    assert (ls' = []) by (destruct ls'; try solve_by_inversion).
    
    subst.
    econstructor.
    admit.

    simpl.
    erewrite anno_range.
    Focus 2.
    eassumption.
    simpl.
    tauto.
    simpl.

    assert (n2 = snd (range a)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      simpl.
      tauto.
    }
    congruence.
    simpl.

    assert (n2 > S i).
    {

      eapply anno_mono.
      eassumption.
    }
    lia.
    simpl.
    tauto.
    simpl.
    tauto.
    eassumption.
    tauto.

  -
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    
    econstructor;
      try tauto;
      try solve_by_inversion.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }
    rewrite H2 in H1.

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4.
    
    



    assert (length ls' = 0).
    {
      lia.
    }

    rewrite H3 in *.

    eapply IHt1 with (ls:=(lrange a)).
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a) ls).
    {
      eapply anno_lrange'; eauto.
    }

    eapply nodup_sub; eauto.
    
    



    eapply anno_sub; eauto.

    eapply IHt2 with (ls:=(lrange a0)).   
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a0) ls).
    {
      assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l ls).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.
    }

    eapply nodup_sub; eauto.

    eapply anno_sub; eauto.

        simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

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

(*
    assert (n0 = snd (range a0)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
    }
    congruence. *)



  




    eapply anno_lrange'.
    apply Heqo.

    assert (list_subset l ls).
    {
      eapply anno_sub'; eauto.
    }

    assert (list_subset (lrange a0) l).
    {
      eapply anno_lrange'; eauto.
    }

    unfold list_subset in *.
    eauto.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    (*
    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4. *)
    assert (nss t2 = length l) by lia.

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }

    rewrite H5 in H4.
    assert (length ls' = 0) by lia.

    

    rewrite H1.

    rewrite <- H2 in *; clear H2.
    rewrite <- H3 in *; clear H3.

    rewrite H5.

    assert (length ls = length (lrange a) + (length l)).
    {
      eapply lrange_len; eauto.
    }

    assert (length l = length (lrange a0) + (length ls')).
    {
      eapply lrange_len; eauto.
    }

    lia.
  -

    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    
    econstructor;
      try tauto;
      try solve_by_inversion.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }
    rewrite H2 in H1.

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4.
    
    



    assert (length ls' = 0).
    {
      lia.
    }

    rewrite H3 in *.

    eapply IHt1 with (ls:=(lrange a)).
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a) ls).
    {
      eapply anno_lrange'; eauto.
    }

    eapply nodup_sub; eauto.
    
    



    eapply anno_sub; eauto.

    eapply IHt2 with (ls:=(lrange a0)).   
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a0) ls).
    {
      assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l ls).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.
    }

    eapply nodup_sub; eauto.

    eapply anno_sub; eauto.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    erewrite anno_range.
    Focus 2.
    eassumption.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    simpl.


    assert (n0 = snd (range a0)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
    }
    congruence.

  




    eapply anno_lrange'.
    apply Heqo.

    assert (list_subset l ls).
    {
      eapply anno_sub'; eauto.
    }

    assert (list_subset (lrange a0) l).
    {
      eapply anno_lrange'; eauto.
    }

    unfold list_subset in *.
    eauto.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    (*
    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4. *)
    assert (nss t2 = length l) by lia.

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }

    rewrite H5 in H4.
    assert (length ls' = 0) by lia.

    

    rewrite H1.

    rewrite <- H2 in *; clear H2.
    rewrite <- H3 in *; clear H3.

    rewrite H5.

    assert (length ls = length (lrange a) + (length l)).
    {
      eapply lrange_len; eauto.
    }

    assert (length l = length (lrange a0) + (length ls')).
    {
      eapply lrange_len; eauto.
    }

    lia.
  -
    ff.



    econstructor;
      try tauto;
      try solve_by_inversion.

    assert (length l4 = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }
    rewrite H1 in H.

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4.
    
    



    assert (length ls' = 0).
    {
      lia.
    }

    rewrite H3 in *.

    eapply IHt1 with (ls:=(lrange a)).
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a) l4).
    {
      eapply anno_lrange'; eauto.
    }

    Check nodup_sub.
    eapply nodup_sub with (ls:=l4); eauto.
    invc H0. invc H8.  invc H9. invc H10.
    eauto.
    
    



    eapply anno_sub; eauto.

    eapply IHt2 with (ls:=(lrange a0)).   
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a0) l4).
    {
      assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l l4).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.
    }

    eapply nodup_sub; eauto.
    unfold list_subset in *.
    intros.
    right.
    right.
    right.
    right.
    eauto.

    eapply anno_sub; eauto.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    erewrite anno_range.
    Focus 2.
    eassumption.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    simpl.


    assert (n0 = snd (range a0)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
    }
    congruence.

    erewrite anno_range.
    Focus 2.
    eassumption.
    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    simpl.

    eapply anno_mono; eauto.

    assert (list_subset (lrange a) l4).
    {
      eapply anno_lrange'; eauto.
    }
    unfold list_subset in *.
    intros.
    right.
    right.
    right.
    right.
    eauto.


    assert (list_subset (lrange a0) l).
    {
      eapply anno_lrange'; eauto.
    }

    assert (list_subset l l4).
    {
      eapply anno_sub'; eauto.
    }
    unfold list_subset in *.
    intros.
    right.
    right.
    right.
    right.
    eauto.
    

    simpl.
    tauto.
    simpl.
    tauto.
    simpl.
    tauto.
    simpl.
    tauto.

    simpl.

    assert (length (lrange a) = nss t1).
    {
      eapply lrange_nss; eauto.
    }

    assert (length (lrange a0) = nss t2).
    {
      eapply lrange_nss; eauto.
    }
    lia.
Defined.














    



































    
    ff.

    econstructor.
    
    

    
    
    
    

    assert (length (lrange a) = nss t1).
    {
      eapply lrange_nss; eauto.
    }

    eapply IHt1.
    eassumption.

    
    

    erewrite anno_len.
    Focus 2.
    apply Heqo.

    erewrite anno_len.
    Focus 2.
    apply Heqo0.

    assert (length ls = length (lrange a) + (length l)).
    {
      admit.
    }

    assert (length l = length (lrange a0) + (length ls')).
    {
      admit.
    }

    assert (nss t1 + (nss t2 + length ls') = length ls + length ls').
    {
      lia.
    }

    rewrite H2; clear H2.

    rewrite H0; clear H0.

    rewrite H1; clear H1.
    
    

    assert (nss t1 + (nss t2 + length ls') = length (lrange a) + length l + length ls').
    {
      admit.
    }

    rewrite H2.

    rewrite H1.
    

    lia.
    
    
    
    

    eapply anno_lrange'.
    apply Heqo0.


    

    eapply IHt1.
    Focus 2.
    eassumption.
    

    Lemma anno_subterm:
      anno t1 i ls = Some (n, (l,a)) ->
      exists ls' l' a',
        anno t1 i ls' = Some(n, (l',a'))
      well_formed a
    
    

    

    eapply IHt1.
    eassumption.
    

    (*
    assert (ls' = []).
    {
      admit.
    }
     *)

    (*
    subst.
    eapply IHt.
    Focus 2.
    eassumption.
    Check anno_lrange.
    assert (list_subset [] (lrange a)).
    {
      eapply anno_lrange.
      Focus 2.
      eassumption.
      

      
      admit.
    }
     *)
    

    solve_by_inversion.
    solve_by_inversion.
    
    
    simpl.
    erewrite anno_range; simpl; try reflexivity.
    eassumption.
    simpl.
    erewrite anno_range; simpl; try reflexivity.
    eassumption.
    simpl.
    assert (n2 > (S i)).
    {
      eapply anno_mono; eauto.
    }
    lia.
    simpl.
    cbn in *.
    repeat break_match; try solve_by_inversion.
    simpl.
    cbn in *.
    repeat break_match; try solve_by_inversion.
    cbn in *.
    repeat break_match; try solve_by_inversion.
  -
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    econstructor.
    
    admit.
    admit.
    
    admit.
    admit.
    admit.

    admit.

    admit.
    admit.

    

    Check anno_lrange.

    




    
    eapply IHt1.
    Focus 2.
    eassumption.
    
    
    
    
    
    eapply IHt.
    Focus 2.
    eassumption.
    Check anno_lrange.

    simpl.
    try solve_by_inversion.
      




  
  -
    auto.
    repeat break_let.
    simpl.
    econstructor;
      try (simpl; lia).
    +
      pose (IHt (S i) (S (S loc))).
      rewrite Heqp in *. eassumption.
    +
      simpl.
      assert (a = snd (snd (anno t (S i) (S (S loc))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_range.
      tauto.
    +
      simpl.
      assert (a = snd (snd (anno t (S i) (S (S loc))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_range.
      simpl.
      rewrite Heqp.
      tauto.
    +
      simpl.
      assert (n0 > (S i)).
      eapply anno_mono; eauto.
      lia.
    +
       simpl.
      assert (a = snd (snd (anno t (S i) (S (S loc))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_lrange.
      simpl.
      lia.

      (*
      rewrite Heqp.
      tauto.



      
      simpl in *.
      Check lrange_anno_mono.
      Check anno_lrange.

      assert (
      
      assert (fst (lrange a) >= (S (S loc))).
      {
        eapply lrange_anno_mono'; eauto.
      }
      
      assert (n1 >= (S (S loc))).
      {
        eapply lrange_anno_mono; eauto.
      }
      lia. *)
      
      
      (*
  -
    repeat break_let.
    simpl in *.
    econstructor;
      try (simpl; lia).
    +
      pose (IHt1 i loc).
      rewrite Heqp in *. eassumption.
    +
      pose (IHt2 n n0).
      rewrite Heqp1 in *. eassumption.
    +
      simpl.
       *)
    
      
    +
      simpl.
      assert (n1 >= S (S loc)).
      {  
        eapply lrange_anno_mono; eauto.   
      }
      lia.
    +
      simpl in *.

      simpl.
      assert (a = snd (snd (anno t (S i) (S (S loc))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_lrange.
      simpl.
      rewrite Heqp.
      simpl.
      lia.
      
      
      
    
  -
    repeat break_let.
    simpl in *.
    econstructor;
      try (simpl; lia).

    +  
      pose (IHt1 (S i) (S (S (S (S loc))))).
      rewrite Heqp in *. eassumption.
    +
      pose (IHt2 n n0).
      rewrite Heqp1 in *. eassumption.
    +
      simpl.
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_range.
      simpl.
      tauto.
    +
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
      subst.
      rewrite anno_range.
      rewrite anno_range.
      simpl.
      rewrite Heqp.
      simpl.
      tauto.
    +
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
      subst.
      simpl.
      rewrite Heqp1.
      simpl.
      rewrite anno_range.
      simpl.
      rewrite Heqp1.
      simpl.
      tauto.
    +
      assert (n1 > n).
      eapply anno_mono; eauto.
      assert (n > (S i)).
      eapply anno_mono; eauto.
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
      subst.
      rewrite anno_range.
      rewrite anno_range.
      simpl.
      lia.
    +
      simpl.
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_lrange.
      
      simpl.
      lia.
    +
      simpl.
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
     
      subst.
      rewrite anno_lrange.
      
      simpl.
      rewrite Heqp1.
      simpl.
      lia.
    +
      simpl.
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_lrange.
      
      simpl.
      lia.
    +
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
      subst.
      repeat (rewrite anno_lrange).
      simpl.
      rewrite Heqp.
      simpl.
      lia.      
Defined.
   *)
Admitted.


Lemma anno_well_formed':
  forall t ls,
    length ls = nss t ->
    well_formed (annotated t ls).
Proof.
  intros.
  edestruct anno_some with (t := t) (i:=0).
  eassumption.
  destruct x.
  destruct p.
  unfold annotated.
  eapply anno_well_formed.
  eassumption.
  unfold anno'.
  rewrite H0 at 2.
  simpl.
  rewrite H0.
  reflexivity.
Defined.

(** Eval for annotated terms. *)

Fixpoint aeval t p e :=
  match t with
  | aasp _ _ x => eval (asp x) p e
  | aatt _ _ _ q x => aeval x q e
  | alseq _ _ t1 t2 => aeval t2 p (aeval t1 p e)
  | abseq _ _ s t1 t2 => ss (aeval t1 p ((splitEv_T (fst s)) e))
                         (aeval t2 p ((splitEv_T (snd s)) e)) 
  | abpar _ _ _ _ s t1 t2 => pp (aeval t1 p ((splitEv_T (fst s)) e))
                         (aeval t2 p ((splitEv_T (snd s)) e))
  end. 

(*
Lemma eval_aeval:
  forall t p e i loc,
    eval t p e = aeval (snd (snd ((anno t i loc)))) p e.
Proof.
  induction t; intros; simpl; auto;
    repeat expand_let_pairs; simpl;
      try (repeat jkjk; auto;congruence);
      try (repeat jkjk'; auto).
Defined.
*)

(** This predicate specifies when a term, a place, and some initial
    evidence is related to an event.  In other words, it specifies the
    set of events associated with a term, a place, and some initial
    evidence. *)

Inductive events: AnnoTerm -> Plc -> Ev -> Prop :=
| evtscpy:
    forall r lr i p,
      fst r = i ->
      events (aasp r lr CPY) p (copy i p)
| evtsusm:
    forall i id args r lr p,
      fst r = i ->
      events (aasp r lr (ASPC id args)) p (umeas i p id args)
| evtssig:
    forall r lr i p,
      fst r = i ->
      events (aasp r lr SIG) p (sign i p) 
| evtshsh:
    forall r lr i p,
      fst r = i ->
      events (aasp r lr HSH) p (hash i p)
| evtsattreq:
    forall r lr q t i p req_loc rpy_loc,
      fst r = i ->
      events (aatt r lr (req_loc, rpy_loc) q t) p (req i req_loc p q (unanno t))
| evtsatt:
    forall r lr q t ev p locs,
      events t q ev ->
      events (aatt r lr locs q t) p ev
| evtsattrpy:
    forall r lr q t i p req_loc rpy_loc,
      snd r = S i ->
      events (aatt r lr (req_loc, rpy_loc) q t) p (rpy i rpy_loc p q)
| evtslseql:
    forall r lr t1 t2 ev p,
      events t1 p ev ->
      events (alseq r lr t1 t2) p ev
| evtslseqr:
    forall r lr t1 t2 ev p,
      events t2 p ev ->
      events (alseq r lr t1 t2) p ev
| evtsbseqsplit:
    forall r lr i s t1 t2 p,
      fst r = i ->
      events (abseq r lr s t1 t2) p
             (split i p)
| evtsbseql:
    forall r lr s t1 t2 ev p,
      events t1 p ev ->
      events (abseq r lr s t1 t2) p ev
| evtsbseqr:
    forall r lr s t1 t2 ev p,
      events t2 p ev ->
      events (abseq r lr s t1 t2) p ev
| evtsbseqjoin:
    forall r lr i s t1 t2 p,
      snd r = S i ->
      events (abseq r lr s t1 t2) p
             (join i p)

| evtsbparsplit:
    forall r lr i s t1 t2 p xi xi' yi yi',
      fst r = i ->
      events (abpar r lr (xi,xi') (yi,yi') s t1 t2) p
             (splitp i xi yi p)
| evtsbparl:
    forall r lr s t1 t2 ev p xlocs ylocs,
      events t1 p ev ->
      events (abpar r lr xlocs ylocs s t1 t2) p ev
| evtsbparr:
    forall r lr s t1 t2 ev p xlocs ylocs,
      events t2 p ev ->
      events (abpar r lr xlocs ylocs s t1 t2) p ev
| evtsbparjoin:
    forall r lr i s t1 t2 p xi xi' yi yi',
      snd r = S i ->
      events (abpar r lr (xi,xi') (yi,yi') s t1 t2) p
             (joinp i (xi') (yi') p).
Hint Constructors events : core.

Lemma events_range:
  forall t v p,
    well_formed t ->
    events t p v ->
    fst (range t) <= ev v < snd (range t).
Proof.
  
  intros t v p H H0.
  pose proof H as G.
  apply well_formed_range in G.
  rewrite G.
  clear G.
  induction H0; inv H; simpl in *; auto;
    try (repeat find_apply_hyp_hyp;
         repeat (find_apply_lem_hyp well_formed_range); lia).
Defined.

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
  destruct G as [G|G]; [left; lia| right].
  pose proof lt_dec i (snd x) as F.
  destruct F as [F|F]; [left; lia| right].
  lia.
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
  destruct G; lia.
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
  destruct G as [G|G]; [left; lia| right].
  pose proof lt_dec i (snd x) as F.
  destruct F as [F|F]; [left; lia| right].
  pose proof lt_dec i (snd y) as E.
  destruct E; lia.
Qed.

Require Import Coq.Program.Tactics.
(** Properties of events. *)

Lemma events_range_event:
  forall t p i,
    well_formed t ->
    fst (range t) <= i < snd (range t) ->
    exists v, events t p v /\ ev v = i.
Proof.
  intros t p i H; revert i; revert p.
  induction H; intros; simpl in *.
  - destruct x; eapply ex_intro; split; auto;
      (*destruct r as [j k];*) simpl in *; lia.
  - find_eapply_lem_hyp at_range; eauto.
    (*eapply at_range in H2; eauto. *)
    destruct r; destruct locs.
    repeat destruct_disjunct; subst; eauto.
    (* + eapply ex_intro; split; auto. *)
    Ltac find_eapply_hyp_hyp :=
      match goal with
      | [ H : forall _, _ -> _,
            H' : _ |- _ ] =>
        eapply H in H'; [idtac]
      | [ H : _ -> _ , H' : _ |- _ ] =>
        eapply H in H'; auto; [idtac]
      end.
    + 
      find_eapply_hyp_hyp.
      (*apply IHwell_formed with (p:=p) in H2. *)
      destruct_conjs.
      eauto.
      (*
      destruct H2 as [v].
      destruct H2; subst.
      exists v; split; eauto. 
    + eapply ex_intro; split.
      apply evtsattrpy; auto.
      * rewrite H1; auto.
      * simpl; auto.
      *)
      
  - eapply lin_range with (i:=i) in H2; eauto;
    repeat destruct_disjunct;
      try lia;
      try (find_eapply_hyp_hyp; eauto;
        destruct_conjs;
        eauto).

    

  - 
    apply bra_range with (i:=i) (r:=r) in H2; eauto;
      repeat destruct_disjunct; subst;
        try lia;
        try (find_eapply_hyp_hyp; eauto;
             destruct_conjs;
             eauto; tauto).
      

    + eapply ex_intro; split; try (auto; eauto;tauto).
    + eapply ex_intro; split; try (eauto; auto; tauto).

  -
    destruct xlocs; destruct ylocs.
    apply bra_range with (i:=i) (r:=r) in H2; eauto;
      repeat destruct_disjunct; subst;
        try lia;
        try (find_eapply_hyp_hyp; eauto;
             destruct_conjs;
             eauto; tauto).

    + eapply ex_intro; split; auto.
    + eapply ex_intro; split; eauto.
Qed.


Ltac events_event_range :=
  repeat match goal with
         | [ H: events _ _ _ |- _ ] =>
           apply events_range in H; auto
         end; lia.

Ltac aba :=
  match goal with
  | [H: events _ _ _, H': events _ _ _ |- _] => inv H; inv H'
  end.

Ltac wfr :=
  match goal with
  | [H: AnnoTerm, H': well_formed ?H |- _] => pose_new_proof (well_formed_range H H')
  end.

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
  induction H; intros;
    try (
        repeat wfr;
        aba; simpl in *; subst; auto;
        try (events_event_range; tauto);
        try (find_eapply_hyp_hyp; eauto);
        eauto).
Qed.

(*
repeat find_apply_lem_hyp well_formed_range.

find_apply_lem_hyp well_formed_range.
find_apply_lem_hyp well_formed_range
apply well_formed_range in G.
apply well_formed_range in G0.
Check well_formed_range.
 *)


Inductive splitEv_T_R : SP -> Evidence -> Evidence -> Prop :=
| spAll: forall e, splitEv_T_R ALL e e
| spNone: forall e, splitEv_T_R NONE e mt.

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

Ltac jkjke :=
  match goal with
  | [H: _ |-  _ ] => erewrite H; eauto
  end.
Ltac kjkj :=
  match goal with
  | [H: evalR ?t ?p ?e ?e' |- _] => assert_new_proof_by (eval t p e = e') eauto
  end.


Ltac do_split :=
  match goal with
  | [H: Split |- _] => destruct H
  end.
      
Ltac do_sp :=
  match goal with
  | [H: SP |- _] => destruct H
  end.

Lemma eval_iff_evalR: forall t p e e',
    evalR t p e e' <-> eval t p e = e'.
Proof.
  split.
  - (* -> case *)
    intros.
    generalize dependent p.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros;
      try (
          inv H;
          simpl;
          repeat kjkj;
          

          try (do_split;
               repeat do_sp);
          try (inv H3; inv H4; reflexivity);
          repeat jkjk;
          eauto).

  (*try (
    inv H;
    simpl;
    repeat kjkj). *)
    
 (*         
    + destruct a; solve_by_inversion.
    + 
      inv H. simpl.
      eauto.
    + inv H.

      simpl.
      repeat kjkj.
      eauto.
      (*
      repeat jkjk.
      eauto. *)

    
    +
      inv H.
      simpl.
      repeat kjkj.

      do_split;
        do_sp;
        try (inv H3; inv H4; reflexivity).
    +
      inv H.
      simpl.
      repeat kjkj.
      
      do_split;
        do_sp;
        try (inv H3; inv H4; reflexivity).
*)
    

  - (* <- case *)
    intros.
    generalize dependent p.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros;
      inv H;
      try (destruct a);
      try (do_split; repeat do_sp);
      repeat econstructor; eauto.
Defined.


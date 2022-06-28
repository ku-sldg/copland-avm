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
Require Import Preamble StructTactics Defs OptMonad_Coq.
(*Require Import AutoPrim. *)

Require Export BS.
Require Export String.

Require Import List.
Import List.ListNotations.

Require Import Coq.Arith.Even Coq.Program.Tactics Coq.Program.Equality.

Require Import Coq.Bool.Bool.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)


(** * Terms and Evidence

    A term is either an atomic ASP, a remote call, a sequence of terms
    with data a dependency, a sequence of terms with no data
    dependency, or parallel terms. *)

(** [Plc] represents a place. *)

Definition Plc: Set := nat.
Definition N_ID: Set := nat.

Definition Event_ID: Set := nat.


Definition ASP_ID: Set := string.
Definition TARG_ID: Set := string.
Definition Arg: Set.
Admitted.

(*
Inductive ASP_PARAMS': Set :=
| asp_paramsC': ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP_PARAMS'.

Definition eqb_asp_params': ASP_PARAMS' -> ASP_PARAMS' -> bool.
Admitted.

Definition eq_asp_params'_dec:
  forall x y: ASP_PARAMS', {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality.
  eapply eq_targid_dec.
  eapply eq_arg_dec.
  eapply eq_aspid_dec.
Defined.
*)

(** The structure of evidence. *)

Inductive ASP_PARAMS: Set :=
| asp_paramsC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> ASP_PARAMS.

Inductive Evidence: Set :=
| mt: Evidence
| uu: (*ASP_PARAMS ->*) ASP_PARAMS ->
      (*Evidence ->*) Plc -> Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: N_ID -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.

Inductive ASP: Set :=
| NULL: ASP
| CPY: ASP
| ASPC: ASP_PARAMS -> ASP
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

(* Adapted from Imp language Notation in Software Foundations (Pierce) *)
Declare Custom Entry copland_entry.
Declare Scope cop_ent_scope.
Notation "<{ e }>" := e (at level 0, e custom copland_entry at level 99) : cop_ent_scope.
Notation "( x )" := x (in custom copland_entry, x at level 99) : cop_ent_scope.
Notation "x" := x (in custom copland_entry at level 0, x constr at level 0) : cop_ent_scope.
(* Branches*)
Notation "x -<- y" := (bseq (NONE, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +<- y" := (bseq (ALL, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x -<+ y" := (bseq (NONE, ALL) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +<+ y" := (bseq (ALL, ALL) x y) (in custom copland_entry at level 70, right associativity).
Notation "x -~- y" := (bpar (NONE, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +~- y" := (bpar (ALL, NONE) x y) (in custom copland_entry at level 70, right associativity).
Notation "x -~+ y" := (bpar (NONE, ALL) x y) (in custom copland_entry at level 70, right associativity).
Notation "x +~+ y" := (bpar (ALL, ALL) x y) (in custom copland_entry at level 70, right associativity).
(* ARROW sequences *)
Notation "x -> y" := (lseq x y) (in custom copland_entry at level 99, right associativity).
(* ASP's *)
Notation "!" := (asp SIG) (in custom copland_entry at level 98).
Notation "#" := (asp HSH) (in custom copland_entry at level 98).
Notation "'_'" := (asp CPY) (in custom copland_entry at level 98).
Notation "'{''}'" := (asp NULL) (in custom copland_entry at level 98).
Notation "'<<' x y z '>>'" := (asp (ASPC (asp_paramsC x nil y z))) 
                      (in custom copland_entry at level 98).
(* @ plc phrase *)
Notation "@ p [ ph ]" := (att p ph) (in custom copland_entry at level 50).





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

Fixpoint top_level_thread_count (t:Term) : nat :=
  match t with
  | asp _ => 0
  | att _ _ => 0
  | lseq t1 t2 => (top_level_thread_count t1) + (top_level_thread_count t2)
  | bseq _ t1 t2 => (top_level_thread_count t1) + (top_level_thread_count t2)
  | bpar _ t1 t2 => 1 + (top_level_thread_count t1) (* + (thread_count t2) *)
  end.

(*
Compute (thread_count (bpar (ALL,ALL) (asp SIG) (asp CPY))).
 *)

Definition RawEv := list BS.

Inductive EvC: Set :=
| evc: RawEv -> Evidence -> EvC.

Definition mt_evc: EvC := (evc [] mt).

Definition get_et (e:EvC) : Evidence :=
  match e with
  | evc ec et => et
  end.

Definition get_bits (e:EvC): list BS :=
  match e with
  | evc ls _ => ls
  end.

Inductive wf_ec : EvC -> Prop :=
| wf_ec_c: forall ls et,
    length ls = et_size et ->
    wf_ec (evc ls et).
    
    
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
Inductive ASP_PARAMS: Set :=
| asp_paramsC: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> Evidence -> ASP_PARAMS.
*)

Definition eval_asp t p e :=
  match t with
  | NULL => mt
  | CPY => e 
  | ASPC params (*(asp_paramsC i args tpl tid tet)*) =>
      uu (*i args tpl tid tet*) params p e
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
| null: nat -> Plc -> Ev
| copy:  nat -> Plc -> Ev 
| umeas: nat -> Plc -> ASP_PARAMS -> Evidence -> Ev
| sign: nat -> Plc -> Evidence -> Ev
| hash: nat -> Plc -> Evidence -> Ev
| req: nat -> Plc -> Plc -> Term -> Evidence -> Ev
| rpy: nat -> Plc -> Plc -> Evidence -> Ev 
| split: nat -> Plc -> Ev
| join:  nat -> Plc -> Ev
| cvm_thread_start: Loc -> Plc -> Term -> Evidence -> Ev
| cvm_thread_end: Loc -> Ev.

(** The natural number used to distinguish events. *)

Definition ev x : nat :=
  match x with
  | null i _ => i
  | copy i _ => i
  | umeas i _ _ _ => i
  | sign i _ _ => i
  | hash i _ _ => i
  | req i _ _ _ _ => i
  | rpy i _ _ _ => i 
  | split i _ => i
  | join i _ => i
  | cvm_thread_start _ _ _ _ => 42
  | cvm_thread_end _ => 43
  end.

(** The natural number indicating the place where an event occured. *)
Definition pl x : Plc :=
  match x with
  | null _ p => p
  | copy _ p => p
  | umeas _ p _ _ => p
  | sign _ p _ => p
  | hash _ p _ => p
  | req _ p _ _ _ => p
  | rpy _ p _ _ => p
  | split _ p => p
  | join _ p => p
  | cvm_thread_start _ p _ _ => p
  | cvm_thread_end _ => 45
  end.

(** Events are used in a manner that ensures that
[[
    forall e0 e1, ev e0 = ev e1 -> e0 = e1.
]]
See Lemma [events_injective].
 *)


Definition asp_event i x p e :=
  match x with
  | NULL => null i p
  | CPY => copy i p
  | ASPC ps => umeas i p ps e
  | SIG => sign i p e
  | HSH => hash i p e
  end.




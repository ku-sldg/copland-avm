(** Basic definitions for Copland terms, Core terms, 
   Evidence Types, and Copland events. *)

(*
   These definitions have been adapted from an earlier version, archived 
   here:  https://ku-sldg.github.io/copland/resources/coplandcoq.tar.gz 

   with License:

LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

Require Export BS.

Require Import AbstractedTypes Maps EqClass.

(** * Terms and Evidence *)

(** [Plc] represents a place (or attestation domain). *)
Definition Plc: Set := ID_Type.
Definition Plc_to_stringT (p: Plc) : StringT := ID_Type_to_stringT p.
Definition stringT_to_Plc (s: StringT) : ResultT Plc StringT := stringT_to_ID_Type s.
(** [N_ID] represents a nonce identifier.  *)
Definition N_ID: Set := nat.
(** [Event_ID] represents Event identifiers *)
Definition Event_ID: Set := nat.

(** [ASP_ID], [TARG_ID], and [Arg] are all identifiers and parameters to ASP terms
    [ASP_ID] identifies the procedure invoked.
    [TARG_ID] identifies the target (when a target makes sense).
    [Arg] represents a custom argument for a given ASP 
          (defined and interpreted per-scenario/implementaiton).
*)
Definition ASP_ID: Set := ID_Type.
Definition ASP_ID_to_stringT (a:ASP_ID) : StringT := ID_Type_to_stringT a.
Definition stringT_to_ASP_ID (s:StringT) : ResultT ASP_ID StringT := stringT_to_ID_Type s.
Definition TARG_ID: Set := ID_Type.

Definition TARG_ID_to_stringT (t:TARG_ID) : StringT := ID_Type_to_stringT t.
Definition stringT_to_TARG_ID (s:StringT) : ResultT TARG_ID StringT := stringT_to_ID_Type s.

Definition ASP_ARGS := MapC StringT StringT.
Definition ASP_Info := StringT.

(* Inductive Resource_ID_Arg: Set := 
| Rid_Arg_C1
| Rid_Arg_C2.

Inductive Arg: Set := 
| Arg_ID : ID_Type -> Arg
| Arg_ResID : Resource_ID_Arg -> Arg. *)

(** Grouping ASP parameters into one constructor *)
Inductive ASP_PARAMS: Type :=
| asp_paramsC: ASP_ID -> ASP_ARGS -> Plc -> TARG_ID -> ASP_PARAMS.

(** Evidence extension types for ASPs:
      COMP:  Compact evidence down to a single value (i.e. a hash).
      ENCR:  Like COMP, but the single value is semantically an ENCRYPTED one.
      EXTD:  Extend bundle (non-destructively) by prepending the new ASP result to the front.
      KILL:  Ignore evidence produced by an ASP and put Mt evidence.
      KEEP:  Ignore evidence produced by an ASP and keep the input evidence unchanged.


COMP:  [b1, b2, ..., bn] ==> [hash([b1, b2, ..., bn])]
ENCR:  [b1, b2, ..., bn] ==> [encrypt([b1, b2, ..., bn])]
EXTD:  [b1, b2, ..., bn] ==> [f([b1, b2, ..., bn]), b1, b2, ..., bn]], 
            where f represents the ASP's functional result over an input evidence bundle.
KILL:  [b1, b2, ..., bn] ==> []
KEEP:  [b1, b2, ..., bn] ==> [b1, b2, ..., bn]
*)
Inductive FWD: Set :=
| COMP
| ENCR
| EXTD
| KILL
| KEEP.

(** The structure of evidence. 

    mt:  Empty evidence 
    nn:  Nonce evidence (with an ID)
    uu:  ASP evidence bundle
    ss:  evidence pairing (composition)
*)
Inductive Evidence :=
| mt: Evidence
| nn: N_ID -> Evidence
| uu: Plc -> FWD -> ASP_PARAMS -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence.

(** Evidene routing types:  
      ALL:   pass through all evidence
      NONE   pass through empty evidence
*)
Inductive SP: Set :=
| ALL
| NONE.


(** Primitive Copland phases 

    NULL:    Empty out evidence (optionally with a strong "zeroize" effect)
    CPY:     Copy evidence (leave input evidence unchanged)
    ASPC sp fwd ps:    
        Arbitrary ASPs:
          sp indicates passing ALL or NONE as input evidence.
          fwd indicates how to extend output evidence.
          ps indicates the asp parameters structure
    SIG:     Signature primitive
    HSH:     Hash primitive 
    ENC q:   Encryption primitive using public key associated with place q.
*)
Inductive ASP :=
| NULL: ASP
| CPY: ASP
| ASPC: SP -> FWD -> ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP
| ENC: Plc -> ASP.

(** Pair of evidence splitters that indicate routing evidence to subterms 
    of branching phrases *)
Definition Split: Set := (SP * SP).

(** Main Copland phrase datatype definition.
        A term is either an atomic ASP (Attestation Service Provider), 
        a remote call (att), a sequence of terms with data a dependency (lseq),
        a sequence of terms with no data dependency, or parallel terms. *)
Inductive Term :=
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
Notation "* p" := (asp (ENC p)) (in custom copland_entry at level 98).
Notation "$" := (asp KILL) (in custom copland_entry at level 98).
Notation "'__'" := (asp CPY) (in custom copland_entry at level 98).
Notation "'{}'" := (asp NULL) (in custom copland_entry at level 98).
Notation "'<<' x y z '>>'" := (asp (ASPC ALL EXTD (asp_paramsC x nil y z))) 
                      (in custom copland_entry at level 98).


(* @ plc phrase *)
Notation "@ p [ ph ]" := (att p ph) (in custom copland_entry at level 50).

(*
Notation "'\t1<' T a1 '>'" := (T a1) (in custom copland_entry at level 99).
Notation "'\t2<' T a1 a2 '>'" := (T a1 a2) (in custom copland_entry at level 99).
Notation "'\t3<' T a1 a2 a3 '>'" := (T a1 a2 a3) (in custom copland_entry at level 99).
Notation "'\t4<' T a1 a2 a3 a4 '>'" := (T a1 a2 a3 a4) (in custom copland_entry at level 99).
Notation "'\t5<' T a1 a2 a3 a4 a5 '>'" := (T a1 a2 a3 a4 a5) (in custom copland_entry at level 99).
Notation "'\t6<' T a1 a2 a3 a4 a5 a6 '>'" := (T a1 a2 a3 a4 a5 a6) (in custom copland_entry at level 99).
*)
Open Scope cop_ent_scope.
Definition test1 := <{ __ -> {} }>.
Example test1ex : test1 = (lseq (asp CPY) (asp NULL)). reflexivity. Defined.
Definition test_enc := <{ __ -> * min_id_type}>.
Example testencex : test_enc = (lseq (asp CPY) (asp (ENC min_id_type))). reflexivity. Defined.

Close Scope cop_ent_scope.

(** Copland Core_Term primitive datatypes *)
Inductive ASP_Core :=
| NULLC: ASP_Core
| CLEAR: ASP_Core
| CPYC: ASP_Core
| ASPCC: FWD -> ASP_PARAMS -> ASP_Core.

(** Abstract Location identifiers used to aid in management and execution 
    of parallel Copland phrases. *)
Definition Loc: Set := nat.
Definition Locs: Set := list Loc.

(** Copland Core_Term definition.  Compilation target of the Copland Compiler, 
    execution language of the Copland VM (CVM). *)
Inductive Core_Term :=
| aspc: ASP_Core -> Core_Term
| attc: Plc -> Term -> Core_Term
| lseqc: Core_Term -> Core_Term -> Core_Term
| bseqc: Core_Term -> Core_Term -> Core_Term
| bparc: Loc -> Core_Term -> Core_Term -> Core_Term.

Declare Custom Entry core_copland_entry.
Declare Scope core_cop_ent_scope.
Notation "<<core>{ e }>" := e (at level 0, e custom core_copland_entry at level 99) : core_cop_ent_scope.
Notation "( x )" := x (in custom core_copland_entry, x at level 99) : core_cop_ent_scope.
Notation "x" := x (in custom core_copland_entry at level 0, x constr at level 0) : core_cop_ent_scope.
(* Branches*)
Notation "x < y" := (bseqc x y) (in custom core_copland_entry at level 70, right associativity).
Notation "x ~ l y" := (bparc l x y) (in custom core_copland_entry at level 70, right associativity).
(* ARROW sequences *)
Notation "x -> y" := (lseqc x y) (in custom core_copland_entry at level 99, right associativity).
(* ASP_CORE's *)
Notation "'__'" := (aspc CPYC) (in custom core_copland_entry at level 98).
Notation "'{}'" := (aspc NULLC) (in custom core_copland_entry at level 98).
Notation "'CLR'" := (aspc CLEAR) (in custom core_copland_entry at level 98).
Notation "'<<' F x y z '>>'" := (aspc (ASPCC F (asp_paramsC x nil y z))) 
                      (in custom core_copland_entry at level 98).
(* @ plc phrase *)
Notation "@ p [ ph ]" := (attc p ph) (in custom core_copland_entry at level 50).


Open Scope core_cop_ent_scope.
Definition test2 := <<core>{ __ -> {} }>.
Example test2ex : test2 = (lseqc (aspc CPYC) (aspc NULLC)). reflexivity. Defined.
Example test3 : <<core>{ CLR -> {}}> = (lseqc (aspc CLEAR) (aspc NULLC)). reflexivity. Defined.


Inductive AppResultC :=
| mtc_app: AppResultC
| nnc_app: N_ID -> BS -> AppResultC
| ggc_app: Plc -> ASP_PARAMS -> BS -> AppResultC -> AppResultC
| hhc_app: Plc -> ASP_PARAMS -> BS -> AppResultC -> (* Evidence -> *) AppResultC
| eec_app: Plc -> ASP_PARAMS -> BS -> AppResultC ->(* Evidence -> *) AppResultC
| ssc_app: AppResultC -> AppResultC -> AppResultC.


Fixpoint appresultc_size (res:AppResultC) : nat :=
  match res with
  | mtc_app => 0
  | nnc_app _ _ => 1
  | ggc_app _ _ _ res' => Nat.add 1 (appresultc_size res')
  | hhc_app _ _ _ res' => Nat.add 1 (appresultc_size res')
  | eec_app _ _ _ res' => Nat.add 1 (appresultc_size res')
  | ssc_app res1 res2 => Nat.add (appresultc_size res1) (appresultc_size res2)
  end.

Definition appres_size_lt_zero (res:AppResultC) : bool :=
  Nat.ltb (appresultc_size res) 0.



(*
End Term_Defs_Core.
*)

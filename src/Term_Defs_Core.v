(** Basic definitions for Copland terms, Core terms, 
   EvidenceT Types, and Copland events. *)

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

Require Import List ID_Type Maps EqClass JSON Stringifiable Stringifiable_Class_Admits StructTactics.
Import ListNotations.

(** * Terms and EvidenceT *)

(** [Plc] represents a place (or attestation domain). *)
Definition Plc: Set := ID_Type.
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
Definition ASP_Compat_MapT := MapC ASP_ID ASP_ID.
Definition ASP_ARGS := MapC string string.

Definition TARG_ID: Set := ID_Type.

Open Scope string_scope.


(** Grouping ASP parameters into one constructor *)
Inductive ASP_PARAMS: Type :=
| asp_paramsC: ASP_ID -> ASP_ARGS -> Plc -> TARG_ID -> ASP_PARAMS.

(** EvidenceT extension types for ASPs:
      COMP:  Compact EvidenceT down to a single value (i.e. a hash).
      ENCR:  Like COMP, but the single value is semantically an ENCRYPTED one.
      EXTD:  Extend bundle (non-destructively) by prepending the new ASP result to the front.
      KILL:  Ignore EvidenceT produced by an ASP and put Mt EvidenceT.
      KEEP:  Ignore EvidenceT produced by an ASP and keep the input EvidenceT unchanged.


COMP:  [b1, b2, ..., bn] ==> [hash([b1, b2, ..., bn])]
ENCR:  [b1, b2, ..., bn] ==> [encrypt([b1, b2, ..., bn])]
EXTD:  [b1, b2, ..., bn] ==> f([b1, b2, ..., bn]) ++ [b1, b2, ..., bn]], 
            where f represents the ASP's functional result over an input EvidenceT bundle.
KILL:  [b1, b2, ..., bn] ==> []
KEEP:  [b1, b2, ..., bn] ==> [b1, b2, ..., bn]
*)
Inductive FWD: Set :=
| COMP
| ENCR
| EXTD : nat -> FWD
| KILL
| KEEP.

(** The structure of EvidenceT. 

    mt_evt:  Empty EvidenceT 
    nn:  Nonce EvidenceT (with an ID)
    uu:  ASP EvidenceT bundle
    ss:  EvidenceT pairing (composition)
*)
Inductive EvidenceT :=
| mt_evt      : EvidenceT
| nonce_evt   : N_ID -> EvidenceT
| asp_evt     : Plc -> FWD -> ASP_PARAMS -> EvidenceT -> EvidenceT
| appr_evt    : EvidenceT -> EvidenceT -> EvidenceT
| split_evt   : EvidenceT -> EvidenceT -> EvidenceT.

(** Evidene routing types:  
      ALL:   pasplit_evt through all EvidenceT
      NONE   pasplit_evt through empty EvidenceT
*)
Inductive SP: Set :=
| ALL
| NONE.

(** Primitive Copland phases 

    NULL:    Empty out EvidenceT (optionally with a strong "zeroize" effect)
    CPY:     Copy EvidenceT (leave input EvidenceT unchanged)
    ASPC sp fwd ps:    
        Arbitrary ASPs:
          sp indicates passing ALL or NONE as input EvidenceT.
          fwd indicates how to extend output EvidenceT.
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


(** Pair of EvidenceT splitters that indicate routing EvidenceT to subterms 
    of branching phrases *)
Definition Split: Set := (SP * SP).

(** Pair of EvidenceT splitters that indicate routing EvidenceT to subterms 
    of branching phrases *)

(** Main Copland phrase datatype definition.
        A term is either an atomic ASP (Attestation Service Provider), 
        a remote call (att), a sequence of terms with data a dependency (lseq),
        a sequence of terms with no data dependency, or parallel terms. *)
Inductive Term :=
| asp: ASP -> Term
| appr : Term
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
(* TODO: Surely we need something more robust than they are ALL EXTD 1, but uhhhh *)
Notation "'<<' x y z '>>'" := (asp (ASPC ALL (EXTD 1) (asp_paramsC x nil y z))) 
                      (in custom copland_entry at level 98).


(* @ plc phrase *)
Notation "@ p [ ph ]" := (att p ph) (in custom copland_entry at level 50).

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
| apprc : Core_Term
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
Example test2ex : test2 = (lseqc (aspc CPYC) (aspc NULLC)). reflexivity. Qed.
Example test3 : <<core>{ CLR -> {}}> = (lseqc (aspc CLEAR) (aspc NULLC)). reflexivity. Qed.

(** Raw EvidenceT representaiton:  a list of binary (BS) values. *)
Definition RawEv := list BS.

Close Scope string_scope.


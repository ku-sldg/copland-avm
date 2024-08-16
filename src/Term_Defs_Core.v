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
Import ListNotations ResultNotation.

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
| asp_evt     : Plc -> ASP_PARAMS -> EvidenceT -> EvidenceT
| split_evt   : EvidenceT -> EvidenceT -> EvidenceT.

(** Evidene routing types:  
      ALL:   pass through all EvidenceT
      NONE   pass through empty EvidenceT
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
| ASPC: SP -> ASP_PARAMS -> ASP
| SIG: ASP
| HSH: ASP
| APPR : ASP
| ENC: Plc -> ASP.

Definition ASP_Type_Env := MapC ASP_ID FWD.

Record GlobalContext := {
  asp_types: ASP_Type_Env;
  asp_comps: ASP_Compat_MapT
}.

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
| att: Plc -> Term -> Term
| lseq: Term -> Term -> Term
| bseq: Split -> Term -> Term -> Term
| bpar: Split -> Term -> Term -> Term.

(**  Calculate the size of an EvidenceT type *)
Fixpoint et_size (G : GlobalContext) (e:EvidenceT)
  : ResultT nat string :=
  match e with
  | mt_evt=> resultC 0
  | nonce_evt _ => resultC 1
  | asp_evt p par e' =>
    let '(asp_paramsC asp_id args targ_plc targ) := par in
    match (map_get (asp_types G) asp_id) with
    | None => errC "ASP Type Signature not found in Environment"%string
    | Some asp_fwd => 
      match asp_fwd with
      | COMP => resultC 1
      | ENCR => resultC 1
      | (EXTD n) => 
        s' <- et_size G e' ;;
        resultC (n + s')
      | KILL => resultC 0
      | KEEP => et_size G e'
      end 
    end
  | split_evt e1 e2 => 
    s1 <- et_size G e1 ;; 
    s2 <- et_size G e2 ;;
    resultC (s1 + s2)
  end.


(** Raw EvidenceT representaiton:  a list of binary (BS) values. *)
Definition RawEv := list BS.

(**  Type-Tagged Raw EvidenceT representation.  Used as the internal EvidenceT
     type managed by the CVM to track EvidenceT contents and its structure. *)
Inductive Evidence :=
| evc: RawEv -> EvidenceT -> Evidence.

Definition mt_evc: Evidence := (evc [] mt_evt).

Definition get_et (e:Evidence) : EvidenceT :=
  match e with
  | evc ec et => et
  end.

Definition get_bits (e:Evidence): list BS :=
  match e with
  | evc ls _ => ls
  end.

(** A "well-formed" Evidence value is where the length of its raw EvidenceT portion
    has the proper size (calculated over the EvidenceT Type portion). *)
Inductive wf_Evidence : GlobalContext -> Evidence -> Prop :=
| wf_Evidence_c: forall (ls:RawEv) et G n,
    List.length ls = n ->
    et_size G et = resultC n ->
    wf_Evidence G (evc ls et).

Inductive CopPhrase :=
| cop_phrase : Plc -> EvidenceT -> Term -> CopPhrase.

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

(** Abstract Location identifiers used to aid in management and execution 
    of parallel Copland phrases. *)
Definition Loc: Set := nat.
Definition Locs: Set := list Loc.

Close Scope string_scope.


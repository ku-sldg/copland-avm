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

Require Import List AbstractedTypes Maps EqClass JSON Serializable Serializable_Class_Admits.
Import ListNotations.

(** * Terms and Evidence *)

(** [Plc] represents a place (or attestation domain). *)
Definition Plc: Set := ID_Type.
Global Instance Serializable_Plc : Serializable Plc := {
  to_string := to_string;
  from_string := from_string;
}.
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
Global Instance Serializable_ASP_ID : Serializable ASP_ID := {
  to_string := to_string;
  from_string := from_string;
}.

Definition TARG_ID: Set := ID_Type.
Global Instance Serializable_TARG_ID : Serializable TARG_ID := {
  to_string := to_string;
  from_string := from_string;
}.

Open Scope string_scope.

Definition ASP_ARGS := MapC string string.
Global Instance Jsonifiable_ASP_ARGS : Jsonifiable ASP_ARGS := {
  to_JSON := string_string_map_to_JSON;
  from_JSON := JSON_to_string_string_map
}.

Definition ASP_Info := string.

(* Inductive Resource_ID_Arg: Set := 
| Rid_Arg_C1
| Rid_Arg_C2.

Inductive Arg: Set := 
| Arg_ID : ID_Type -> Arg
| Arg_ResID : Resource_ID_Arg -> Arg. *)

(** Grouping ASP parameters into one constructor *)
Inductive ASP_PARAMS: Type :=
| asp_paramsC: ASP_ID -> ASP_ARGS -> Plc -> TARG_ID -> ASP_PARAMS.

Global Instance Jsonifiable_ASP_Params : Jsonifiable ASP_PARAMS := {
  to_JSON := (fun asp_params => 
                match asp_params with
                | asp_paramsC asp_id args plc targ_id => 
                    JSON_Object [
                      ("ASP_ID", InJSON_String (to_string asp_id));
                      ("ASP_ARGS", InJSON_Object (to_JSON args));
                      ("ASP_PLC", InJSON_String (to_string plc));
                      ("ASP_TARG_ID", InJSON_String (to_string targ_id))
                    ]
                end);
  from_JSON := (fun js => 
                  match (JSON_get_string "ASP_ID" js), (JSON_get_Object "ASP_ARGS" js), 
                        (JSON_get_string "ASP_PLC" js), (JSON_get_string "ASP_TARG_ID" js) with
                  | resultC asp_id, resultC args, resultC plc, resultC targ_id => 
                      match (from_string asp_id), (from_JSON args), (from_string plc), (from_string targ_id) with
                      | resultC asp_id, resultC args, resultC plc, resultC targ_id => resultC (asp_paramsC asp_id args plc targ_id)
                      | _, _, _, _ => errC "Parsing ASP_PARAMS not successful"
                      end
                  | _, _, _, _ => errC "Invalid ASP_PARAMS JSON"
                  end)
}.

(** Evidence extension types for ASPs:
      COMP:  Compact evidence down to a single value (i.e. a hash).
      ENCR:  Like COMP, but the single value is semantically an ENCRYPTED one.
      EXTD:  Extend bundle (non-destructively) by prepending the new ASP result to the front.
      KILL:  Ignore evidence produced by an ASP and put Mt evidence.
      KEEP:  Ignore evidence produced by an ASP and keep the input evidence unchanged.


COMP:  [b1, b2, ..., bn] ==> [hash([b1, b2, ..., bn])]
ENCR:  [b1, b2, ..., bn] ==> [encrypt([b1, b2, ..., bn])]
EXTD:  [b1, b2, ..., bn] ==> f([b1, b2, ..., bn]) ++ [b1, b2, ..., bn]], 
            where f represents the ASP's functional result over an input evidence bundle.
KILL:  [b1, b2, ..., bn] ==> []
KEEP:  [b1, b2, ..., bn] ==> [b1, b2, ..., bn]
*)
Inductive FWD: Set :=
| COMP
| ENCR
| EXTD : nat -> FWD
| KILL
| KEEP.

Global Instance Jsonifiable_FWD : Jsonifiable FWD := {
  to_JSON := (fun fwd => 
                match fwd with
                | COMP => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "COMP")]
                | ENCR => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "ENCR")]
                | EXTD n => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "EXTD"); ("EXTD_N", InJSON_String (to_string n))]
                | KILL => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "KILL")]
                | KEEP => JSON_Object [("FWD_CONSTRUCTOR", InJSON_String "KEEP")]
                end);
  from_JSON := (fun js => 
                  match (JSON_get_string "FWD_CONSTRUCTOR" js) with
                  | resultC cons_name =>
                      if (eqb cons_name "COMP") 
                      then resultC COMP
                      else if (eqb cons_name "ENCR") 
                      then resultC ENCR
                      else if (eqb cons_name "KILL") 
                      then resultC KILL
                      else if (eqb cons_name "KEEP") 
                      then resultC KEEP
                      else if (eqb cons_name "EXTD")
                        then match (JSON_get_string "EXTD_N" js) with
                             | resultC n_str => 
                                match (from_string n_str) with
                                | resultC n => resultC (EXTD n)
                                | errC e => errC e
                                end
                             | _ => errC "Parsing EXTD not successful"
                             end
                      else errC "Invalid FWD JSON"
                  | errC e => errC e
                  end)
                  (* match (JSON_get_string "FWD_CONSTRUCTOR" js) with
                  | resultC "COMP" => resultC COMP
                  | resultC "ENCR" => resultC ENCR
                  | resultC "EXTD" => 
                      match (JSON_get_string "EXTD_N" js) with
                      | resultC n => 
                        match (from_string n) with
                        | resultC n => resultC (EXTD n)
                        | errC e => errC e
                        end
                      | _ => errC "Parsing EXTD not successful"
                      end
                  | resultC "KILL" => resultC KILL
                  | resultC "KEEP" => resultC KEEP
                  | _ => errC "Invalid FWD JSON"
                  end) *)
}.

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

Fixpoint Evidence_to_JSON (e : Evidence) : JSON := 
  match e with
  | mt => JSON_Object [("EVIDENCE_CONSTRUCTOR", InJSON_String "mt")]
  | nn n => 
      JSON_Object [
        ("EVIDENCE_CONSTRUCTOR", InJSON_String "nn"); 
        ("N_ID", InJSON_String (to_string n))
      ]
  | uu plc fwd ps e' => 
      JSON_Object [
        ("EVIDENCE_CONSTRUCTOR", InJSON_String "uu");
        ("PLC", InJSON_String (to_string plc));
        ("FWD", InJSON_Object (to_JSON fwd));
        ("ASP_PARAMS", InJSON_Object (to_JSON ps));
        ("EVIDENCE", InJSON_Object (Evidence_to_JSON e'))
      ]
  | ss e1 e2 =>
      JSON_Object [
        ("EVIDENCE_CONSTRUCTOR", InJSON_String "ss");
        ("EVIDENCE1", InJSON_Object (Evidence_to_JSON e1));
        ("EVIDENCE2", InJSON_Object (Evidence_to_JSON e2))
      ]
  end.

Fixpoint Evidence_from_JSON (js : JSON) : ResultT Evidence string :=
  match (JSON_get_string "EVIDENCE_CONSTRUCTOR" js) with
  | resultC cons_name =>
      if (eqb cons_name "mt") 
      then resultC mt
      else if (eqb cons_name "nn") 
      then  match (JSON_get_string "N_ID" js) with
            | resultC nVal => 
              match (from_string nVal) with
              | resultC n => resultC (nn n)
              | errC e => errC e
              end
            | _ => errC "Parsing nn not successful"
            end
      else if (eqb cons_name "uu") 
      then  match js with
            | JSON_Object [
                ev_cons; 
                (_,InJSON_String plc); 
                (_, InJSON_Object fwd); 
                (_, InJSON_Object asp_par); 
                (_, InJSON_Object ev')
              ] =>
                match (from_string plc), (from_JSON fwd), (from_JSON asp_par), (Evidence_from_JSON ev') with
                | resultC plc, resultC fwd, resultC ps, resultC e =>
                  resultC (uu plc fwd ps e)
                | _, _, _, _ => errC "Evidence_from_JSON: error parsing uu"
                end
            | _ => errC "Parsing uu not successful"
            end
      else if (eqb cons_name "ss") 
      then  match js with
            | JSON_Object [
                ev_cons; 
                (_,InJSON_Object ev1); 
                (_,InJSON_Object ev2)
              ] =>
                match (Evidence_from_JSON ev1), (Evidence_from_JSON ev2) with
                | resultC e1, resultC e2 => resultC (ss e1 e2)
                | _, _ => errC "Parsing ss not successful"
                end
            | _ => errC "Parsing ss not successful"
            end
      else errC "Invalid Evidence JSON constructor name"
  | errC e => errC e
  end.

Global Instance Jsonifiable_Evidence : Jsonifiable Evidence := {
  to_JSON := Evidence_to_JSON;
  from_JSON := Evidence_from_JSON
}.

(** Evidene routing types:  
      ALL:   pass through all evidence
      NONE   pass through empty evidence
*)
Inductive SP: Set :=
| ALL
| NONE.


Global Instance Serializable_SP : Serializable SP := {
  to_string := (fun sp => 
                  match sp with
                  | ALL => "ALL"
                  | NONE => "NONE"
                  end);
  from_string := (fun s => 
                    if (eqb s "ALL")
                    then resultC ALL
                    else if (eqb s "NONE")
                    then resultC NONE
                    else errC "Invalid SP string")
}.


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

Global Instance Jsonifiable_ASP : Jsonifiable ASP := {
  to_JSON := (fun a => 
                match a with
                | NULL => JSON_Object [("ASP_CONSTRUCTOR", InJSON_String "NULL")]
                | CPY => JSON_Object [("ASP_CONSTRUCTOR", InJSON_String "CPY")]
                | ASPC sp fwd ps => 
                    JSON_Object [
                      ("ASP_CONSTRUCTOR", InJSON_String "ASPC");
                      ("ASP_SP", InJSON_String (to_string sp));
                      ("ASP_FWD", InJSON_Object (to_JSON fwd));
                      ("ASP_PARAMS", InJSON_Object (to_JSON ps))
                    ]
                | SIG => JSON_Object [("ASP_CONSTRUCTOR", InJSON_String "SIG")]
                | HSH => JSON_Object [("ASP_CONSTRUCTOR", InJSON_String "HSH")]
                | ENC q => 
                    JSON_Object [
                      ("ASP_CONSTRUCTOR", InJSON_String "ENC");
                      ("ENC_PLC", InJSON_String (to_string q))
                    ]
                end);
  from_JSON := (fun js => 
                  match (JSON_get_string "ASP_CONSTRUCTOR" js) with
                  | resultC cons_name =>
                      if (eqb cons_name "NULL")
                      then resultC NULL
                      else if (eqb cons_name "CPY")
                      then resultC CPY
                      else if (eqb cons_name "ASPC")
                      then match (JSON_get_string "ASP_SP" js), (JSON_get_Object "ASP_FWD" js), (JSON_get_Object "ASP_PARAMS" js) with
                           | resultC sp, resultC fwd, resultC ps =>
                              match (from_string sp), (from_JSON fwd), (from_JSON ps) with
                              | resultC sp, resultC fwd, resultC ps => 
                                  resultC (ASPC sp fwd ps)
                              | _, _, _ => errC "Parsing ASPC not successful"
                              end
                           | _, _, _ => errC "Parsing ASPC not successful"
                           end
                      else if (eqb cons_name "SIG")
                      then resultC SIG
                      else if (eqb cons_name "HSH")
                      then resultC HSH
                      else if (eqb cons_name "ENC")
                      then match (JSON_get_string "ENC_PLC" js) with
                           | resultC q => 
                              match (from_string q) with
                              | resultC q => resultC (ENC q)
                              | _ => errC "Parsing ENC PLC from string not successful"
                              end
                           | _ => errC "Parsing ENC not successful"
                           end
                      else errC "Invalid JSON ASP Constructor Name"
                  | _ => errC "Invalid JSON ASP Constructor Name"
                  end)
}.


(** Pair of evidence splitters that indicate routing evidence to subterms 
    of branching phrases *)
Definition Split: Set := (SP * SP).

Global Instance Jsonifiable_Split : Jsonifiable Split := {
  to_JSON := (fun '(s1, s2) => 
                JSON_Object [
                  ("split1", InJSON_String (to_string s1));
                  ("split2", InJSON_String (to_string s2))
                ]);
  from_JSON := (fun js => 
                  match (JSON_get_string "split1" js), (JSON_get_string "split2" js) with
                  | resultC s1, resultC s2 => 
                      match (from_string s1), (from_string s2) with
                      | resultC s1, resultC s2 => resultC (s1, s2) 
                      | _, _ => errC "Parsing split not successful"
                      end
                  | _, _ => errC "Invalid Split JSON"
                  end)
}.

(** Pair of evidence splitters that indicate routing evidence to subterms 
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

(* NOTE: Very lame on Coq's part, we have to do a list
encoding of the TERM_BODY because it cannot understand
how the recursive calls are truly on subterms otherwise *)
Fixpoint Term_to_JSON (t : Term) : JSON :=
  match t with
  | asp a => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "asp"); 
      ("TERM_BODY", InJSON_Object (to_JSON a))
    ]
  | att p t1 => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "att");
      ("TERM_BODY", InJSON_Array [
          (InJSON_String (to_string p)); 
          (InJSON_Object (Term_to_JSON t1))
        ]
      )
    ]
  | lseq t1 t2 => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "lseq");
      ("TERM_BODY", InJSON_Array [
          (InJSON_Object (Term_to_JSON t1));
          (InJSON_Object (Term_to_JSON t2))
        ]
      )
    ]
  | bseq s t1 t2 => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "bseq");
      ("TERM_BODY", InJSON_Array [
          (InJSON_Object (to_JSON s));
          (InJSON_Object (Term_to_JSON t1));
          (InJSON_Object (Term_to_JSON t2))
        ]
      )
    ]
  | bpar s t1 t2 => 
    JSON_Object [
      ("TERM_CONSTRUCTOR", InJSON_String "bpar");
      ("TERM_BODY", InJSON_Array [
          (InJSON_Object (to_JSON s));
          (InJSON_Object (Term_to_JSON t1));
          (InJSON_Object (Term_to_JSON t2))
        ]
      )
    ]
  end.

Fixpoint Term_from_JSON (js : JSON) : ResultT Term string :=
  match (JSON_get_string "TERM_CONSTRUCTOR" js) with
  | resultC cons_name =>
      if (eqb cons_name "asp")
      then  match (JSON_get_Object "TERM_BODY" js) with
            | resultC js' => 
                match (from_JSON js') with
                | resultC a => resultC (asp a)
                | errC e => errC e
                end
            | errC e => errC e
            end
      else if (eqb cons_name "att")
      then (*! I hate this, but only viable way without going wf recursion *)
          match js with
          | JSON_Object [
              term_cons; 
              (_, InJSON_Array [InJSON_String plc; InJSON_Object js'])
            ] =>
              match (from_string plc), (Term_from_JSON js') with
              | resultC plc, resultC t => resultC (att plc t)
              | _, _ => errC "Parsing att not successful"
              end
          | _ => errC "Invalid att JSON: REMEMBER IT MUST BE IN A SPECIFIC FORMAT AND ORDER"
          end
      else if (eqb cons_name "lseq")
      then  match js with
            | JSON_Object [
                term_cons; 
                (_, InJSON_Array [InJSON_Object t1js; InJSON_Object t2js])
              ] =>
                match (Term_from_JSON t1js), (Term_from_JSON t2js) with
                | resultC t1, resultC t2 => resultC (lseq t1 t2)
                | _, _ => errC "Parsing lseq not successful"
                end
            | _ => errC "Invalid lseq JSON: REMEMBER IT MUST BE IN A SPECIFIC FORMAT AND ORDER"
            end
      else if (eqb cons_name "bseq")
      then  match js with
            | JSON_Object [
                term_cons; 
                (_, InJSON_Array [InJSON_Object spjs; InJSON_Object t1js; InJSON_Object t2js])
              ] =>
                match (from_JSON spjs), (Term_from_JSON t1js), (Term_from_JSON t2js) with
                | resultC s, resultC t1, resultC t2 => resultC (bseq s t1 t2)
                | _, _, _ => errC "Parsing bseq not successful"
                end
            | _ => errC "Invalid bseq JSON: REMEMBER IT MUST BE IN A SPECIFIC FORMAT AND ORDER"
            end
      else if (eqb cons_name "bpar")
      then  match js with
            | JSON_Object [
                term_cons; 
                (_, InJSON_Array [InJSON_Object spjs; InJSON_Object t1js; InJSON_Object t2js])
              ] =>
                match (from_JSON spjs), (Term_from_JSON t1js), (Term_from_JSON t2js) with
                | resultC s, resultC t1, resultC t2 => resultC (bpar s t1 t2)
                | _, _, _ => errC "Parsing bpar not successful"
                end
            | _ => errC "Invalid bpar JSON: REMEMBER IT MUST BE IN A SPECIFIC FORMAT AND ORDER"
            end
      else errC "Invalid TERM CONSTRUCTOR in Term_from_JSON"
  | errC e => errC e
  end.

Global Instance Jsonifiable_Term : Jsonifiable Term := {
  to_JSON := Term_to_JSON;
  from_JSON := Term_from_JSON
}.

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

(** Raw Evidence representaiton:  a list of binary (BS) values. *)
Definition RawEv := list BS.

Global Instance Jsonifiable_RawEv : Jsonifiable RawEv := {
  to_JSON := (fun ev => 
                JSON_Object [
                  ("RawEv", InJSON_Array (map (fun bs => InJSON_String (to_string bs)) ev))
                ]);
  from_JSON := (fun js => 
                  match (JSON_get_Array "RawEv" js) with
                  | resultC js' => 
                      result_map (fun js' => 
                                    match js' with
                                    | InJSON_String s => 
                                        match (from_string s) with
                                        | resultC bs => resultC bs
                                        | errC e => errC e
                                        end
                                    | _ => errC "Invalid RawEv JSON"
                                    end) js'
                  | errC e => errC e
                  end)
}.

(** AppResultC represents the result of a Copland Core_Term execution. *)

Inductive AppResultC :=
| mtc_app: AppResultC
| nnc_app: N_ID -> BS -> AppResultC
| ggc_app: Plc -> ASP_PARAMS -> RawEv -> AppResultC -> AppResultC
| hhc_app: Plc -> ASP_PARAMS -> BS -> AppResultC -> (* Evidence -> *) AppResultC
| eec_app: Plc -> ASP_PARAMS -> BS -> AppResultC ->(* Evidence -> *) AppResultC
| ssc_app: AppResultC -> AppResultC -> AppResultC.

Fixpoint AppResultC_to_Json (a : AppResultC) : JSON :=
  match a with
  | mtc_app => JSON_Object [("AppResultC_CONSTRUCTOR", InJSON_String "mtc_app")]
  | nnc_app n bs => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "nnc_app");
        ("N_ID", InJSON_String (to_string n));
        ("BS", InJSON_String (to_string bs))
      ]
  | ggc_app plc ps rawEv res => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "ggc_app");
        ("PLC", InJSON_String (to_string plc));
        ("ASP_PARAMS", InJSON_Object (to_JSON ps));
        ("RawEv", InJSON_Object (to_JSON rawEv));
        ("AppResultC", InJSON_Object (AppResultC_to_Json res))
      ]
  | hhc_app plc ps bs res => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "hhc_app");
        ("PLC", InJSON_String (to_string plc));
        ("ASP_PARAMS", InJSON_Object (to_JSON ps));
        ("BS", InJSON_String (to_string bs));
        ("AppResultC", InJSON_Object (AppResultC_to_Json res))
      ]
  | eec_app plc ps bs res => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "eec_app");
        ("PLC", InJSON_String (to_string plc));
        ("ASP_PARAMS", InJSON_Object (to_JSON ps));
        ("BS", InJSON_String (to_string bs));
        ("AppResultC", InJSON_Object (AppResultC_to_Json res))
      ]
  | ssc_app res1 res2 => 
      JSON_Object [
        ("AppResultC_CONSTRUCTOR", InJSON_String "ssc_app");
        ("AppResultC1", InJSON_Object (AppResultC_to_Json res1));
        ("AppResultC2", InJSON_Object (AppResultC_to_Json res2))
      ]
  end.

Fixpoint AppResultC_from_JSON (js : JSON) : ResultT AppResultC string :=
  match (JSON_get_string "AppResultC_CONSTRUCTOR" js) with
  | resultC cons_name =>
      if (eqb cons_name "mt_app")
      then resultC mtc_app
      else if (eqb cons_name "nnc_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_String n);
                (_, InJSON_String bs)
              ] => 
                match (from_string n), (from_string bs) with
                | resultC n, resultC bs => resultC (nnc_app n bs)
                | _, _ => errC "Parsing nnc_app not successful"
                end
            | _ => errC "Parsing nnc_app not successful"
            end
      else if (eqb cons_name "ggc_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_String plc);
                (_, InJSON_Object ps);
                (_, InJSON_Object rawEv);
                (_, InJSON_Object res)
              ] =>
                match (from_string plc), (from_JSON ps), (from_JSON rawEv), (AppResultC_from_JSON res) with
                | resultC plc, resultC ps, resultC rawEv, resultC res => resultC (ggc_app plc ps rawEv res)
                | _, _, _, _ => errC "Parsing ggc_app not successful"
                end
            | _ => errC "Parsing ggc_app not successful"
            end
      else if (eqb cons_name "hhc_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_String plc);
                (_, InJSON_Object ps);
                (_, InJSON_String bs);
                (_, InJSON_Object res)
              ] =>
                  match (from_string plc), (from_JSON ps), (from_string bs), (AppResultC_from_JSON res) with
                  | resultC plc, resultC ps, resultC bs, resultC res => resultC (hhc_app plc ps bs res)
                  | _, _, _, _ => errC "Parsing hhc_app not successful"
                  end
            | _ => errC "Parsing hhc_app not successful"
            end
      else if (eqb cons_name "eec_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_String plc);
                (_, InJSON_Object ps);
                (_, InJSON_String bs);
                (_, InJSON_Object res)
              ] =>
                match (from_string plc), (from_JSON ps), (from_string bs), (AppResultC_from_JSON res) with
                | resultC plc, resultC ps, resultC bs, resultC res => resultC (eec_app plc ps bs res)
                | _, _, _, _ => errC "Parsing eec_app not successful"
                end
            | _ => errC "Parsing eec_app not successful"
            end
      else if (eqb cons_name "ssc_app")
      then  match js with
            | JSON_Object [
                _;
                (_, InJSON_Object res1);
                (_, InJSON_Object res2)
              ] =>
                match (AppResultC_from_JSON res1), (AppResultC_from_JSON res2) with
                | resultC res1, resultC res2 => resultC (ssc_app res1 res2)
                | _, _ => errC "Parsing ssc_app not successful"
                end
            | _ => errC "Parsing ssc_app not successful"
            end
      else errC "Invalid AppResultC JSON"
  | _ => errC "Invalid AppResultC JSON"
  end.

Global Instance Jsonifiable_AppResultC : Jsonifiable AppResultC := {
  to_JSON := AppResultC_to_Json;
  from_JSON := AppResultC_from_JSON
}.

Close Scope string_scope.

Fixpoint appresultc_size (res:AppResultC) : nat :=
  match res with
  | mtc_app => 0
  | nnc_app _ _ => 1
  | ggc_app _ _ rawEv res' => Nat.add (List.length rawEv) (appresultc_size res')
  | hhc_app _ _ _ res' => Nat.add 1 (appresultc_size res')
  | eec_app _ _ _ res' => Nat.add 1 (appresultc_size res')
  | ssc_app res1 res2 => Nat.add (appresultc_size res1) (appresultc_size res2)
  end.

Definition appres_size_lt_zero (res:AppResultC) : bool :=
  Nat.ltb (appresultc_size res) 0.



(*
End Term_Defs_Core.
*)

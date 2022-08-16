(** This file contains the basic definitions for Copland terms, Core terms, 
   Evidence Types, and Copland events. *)

(*
   These definitions have been adapted from an earlier version, archived 
   here:  https://ku-sldg.github.io/copland/resources/coplandcoq.tar.gz
*)

(* LICENSE NOTICE

Copyright (c) 2018 The MITRE Corporation.
All Rights Reserved.

This proof script is free software: you can redistribute it and/or
modify it under the terms of the BSD License as published by the
University of California.  See license.txt for details. *)

(*
Require Export BS.
Require Export String. *)

Require Import List.
Import List.ListNotations.

Require Export Params_Admits.

(* sig_params, hsh_params, defs were here *)

(**  Translating a primitive Copland phrase to its Core_Term equivalent *)
Definition asp_term_to_core (a:ASP) : Core_Term :=
  match a with
  | NULL => aspc NULLC
  | CPY => aspc CPYC
  | ASPC sp fwd params =>
    match sp with
    | NONE => lseqc (aspc CLEAR) (aspc (ASPCC fwd params))
    | ALL => (aspc (ASPCC fwd params))
    end
                   
  | SIG => aspc (ASPCC EXTD sig_params)
  | HSH => aspc (ASPCC COMP hsh_params)
  | ENC q => aspc (ASPCC ENCR (enc_params q))
  end.

(**  Translating a Copland phrase to its Core_Term equivalent *)
Fixpoint copland_compile (t:Term) : Core_Term :=
  match t with
  | asp a => (asp_term_to_core a)
  | att q t' => attc q t'

  | lseq t1 t2 => lseqc (copland_compile t1) (copland_compile t2)

  | bseq (ALL,ALL) t1 t2 =>
    bseqc
      (copland_compile t1) (copland_compile t2)  
  | bseq (ALL,NONE) t1 t2 =>
    bseqc
      (copland_compile t1)
      (lseqc (aspc CLEAR) (copland_compile t2))
  | bseq (NONE,ALL) t1 t2 =>
    bseqc
      (lseqc (aspc CLEAR) (copland_compile t1))
      (copland_compile t2)
  | bseq (NONE,NONE) t1 t2 =>
    bseqc
      (lseqc (aspc CLEAR) (copland_compile t1))
      (lseqc (aspc CLEAR) (copland_compile t2))
          
  | bpar (ALL,ALL) t1 t2 =>
    bparc O (copland_compile t1) (copland_compile t2)     
  | bpar (ALL,NONE) t1 t2 =>
    bparc O
      (copland_compile t1)
      (lseqc (aspc CLEAR) (copland_compile t2))
  | bpar (NONE,ALL) t1 t2 =>
    bparc O
      (lseqc (aspc CLEAR) (copland_compile t1))
      (copland_compile t2)
  | bpar (NONE,NONE) t1 t2 =>
    bparc O
      (lseqc (aspc CLEAR) (copland_compile t1))
      (lseqc (aspc CLEAR) (copland_compile t2))
  end.


(** Propositional encapsulation of copland_compile.  
    Useful to avoid spurious rewriting during proofs *)
Inductive term_to_coreP: Term -> Core_Term -> Prop :=
| toCoreP: forall t t',
    copland_compile t = t' ->
    term_to_coreP t t'.


(**  Calculate the size of an Evidence type *)
Fixpoint et_size (e:Evidence): nat :=
  match e with
  | mt => O
           (*
  | gg _ _ e' => 1 + (et_size e')
  | hh _ _ _ => 1
            *)
  | uu _ fwd _ e' =>
    match fwd with
    | COMP => 1
    | ENCR => 1(* et_size e' *)
    | EXTD => 1 + et_size e'
    end
    
    
  | nn _ => 1
  | ss e1 e2 => (et_size e1) + (et_size e2)
  end.


(*
Fixpoint thread_count (t:Term) : nat :=
  match t with
  | asp _ => O
  | att _ _ => O
  | lseq t1 t2 => max (thread_count t1) (thread_count t2)
  | bseq _ t1 t2 => max (thread_count t1) (thread_count t2)
  | bpar _ t1 t2 => 1 + (thread_count t1) + (thread_count t2)
  end.

Fixpoint top_level_thread_count (t:Term) : nat :=
  match t with
  | asp _ => O
  | att _ _ => O
  | lseq t1 t2 => (top_level_thread_count t1) + (top_level_thread_count t2)
  | bseq _ t1 t2 => (top_level_thread_count t1) + (top_level_thread_count t2)
  | bpar _ t1 t2 => 1 + (top_level_thread_count t1) (* + (thread_count t2) *)
  end.
*)

(*
Compute (thread_count (bpar (ALL,ALL) (asp SIG) (asp CPY))).
 *)


(** Raw Evidence representaiton:  a list of binary (BS) values. *)
Definition RawEv := list BS.

(**  Type-Tagged Raw Evidence representation.  Used as the internal evidence
     type managed by the CVM to track evidence contents and its structure. *)
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

(** A "well-formed" EvC value is where the length of its raw evidence portion
    has the proper size (calculated over the Evidence Type portion). *)
Inductive wf_ec : EvC -> Prop :=
| wf_ec_c: forall (ls:RawEv) et,
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

Definition sp_ev (sp:SP) (e:Evidence) : Evidence :=
  match sp with
  | ALL => e
  | NONE => mt
  end.

(** Helper function for evidence type reference semantics *)
Definition eval_asp t p e :=
  match t with
  | NULL => mt
  | CPY => e 
  | ASPC sp fwd params => uu p fwd params (sp_ev sp e)
                            (*
    match fwd with
    | ENCR => 
    | COMP => hh p params (sp_ev sp e)
    | EXTD => gg p params (sp_ev sp e)
    end *)
                            (*
  | SIG => gg p sig_params e
  | HSH => hh p hsh_params e *)
  | SIG => uu p EXTD sig_params e
  | HSH => uu p COMP hsh_params e
  | ENC q => uu p ENCR (enc_params q) e
  end.

(** Evidence Type denotational reference semantics.
    The evidence associated with a term, a place, and some initial evidence. *)

Fixpoint eval (t:Term) (p:Plc) (e:Evidence) : Evidence :=
  match t with
  | asp a => eval_asp a p e
  | att q t1 => eval t1 q e
  | lseq t1 t2 => eval t2 p (eval t1 p e)
  | bseq s t1 t2 => ss (eval t1 p (splitEv_T_l s e))
                      (eval t2 p (splitEv_T_r s e))
  | bpar s t1 t2 => ss (eval t1 p (splitEv_T_l s e))
                      (eval t2 p (splitEv_T_r s e))
  end.

(** * Events

    There are events for each kind of action. This includes ASP
    actions such as measurement or data processing. It also includes
    control flow actions: a [split] occurs when a thread of control
    splits, and a [join] occurs when two threads join.  [req] and [rpy] 
    are communication events.  [cvm_thread_start] and [cvm_thread_end] are 
    parallel thread synchonization events, unique to CVM execution (not in 
    the reference semantics).  Each event is distinguished using a unique 
    natural number.
 *)

Inductive Ev: Set :=
| null: nat -> Plc -> Ev
| copy:  nat -> Plc -> Ev 
| umeas: nat -> Plc -> ASP_PARAMS -> Evidence -> Ev
| req: nat -> Plc -> Plc -> Term -> Evidence -> Ev
| rpy: nat -> Plc -> Plc -> Evidence -> Ev 
| split: nat -> Plc -> Ev
| join:  nat -> Plc -> Ev
| cvm_thread_start: Loc -> Plc -> Core_Term -> Evidence -> Ev
| cvm_thread_end: Loc -> Ev.

(** The natural number used to distinguish events. *)

Definition ev x : nat :=
  match x with
  | null i _ => i
  | copy i _ => i
  | umeas i _ _ _ => i
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
  | ASPC sp _ ps => umeas i p ps (sp_ev sp e)
  | SIG => umeas i p sig_params e
  | HSH => umeas i p hsh_params e
  | ENC q => umeas i p (enc_params q) e
  end.




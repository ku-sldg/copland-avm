(** Basic definitions for Copland Terms, Core Terms, 
   EvidenceT, Remote Request/Response structures, Copland events (Ev). *)

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

Require Import Maps EqClass List ID_Type Defs.
Import ListNotations ResultNotation.

Require Export Params_Admits.

Require Export Term_Defs_Core.

Definition splitEv_T_l (sp:Split) (e:EvidenceT) : EvidenceT :=
  match sp with
  | (ALL,_) => e
  |  _ => mt_evt
  end.

Definition splitEv_T_r (sp:Split) (e:EvidenceT) : EvidenceT :=
  match sp with
  | (_,ALL) => e
  |  _ => mt_evt
  end.

Definition sp_ev (sp:SP) (e:EvidenceT) : EvidenceT :=
  match sp with
  | ALL => e
  | NONE => mt_evt
  end.

Fixpoint appr_procedure (G : GlobalContext) (p : Plc) (e:EvidenceT) 
    : ResultT EvidenceT string :=
  match e with
  | mt_evt => resultC mt_evt
  | nonce_evt n => resultC (asp_evt p check_nonce_params (nonce_evt n))
  | asp_evt asp_top_plc ps e' => 
    let '(asp_paramsC asp_id args targ_plc targ) := ps in
    match (map_get (asp_comps G) asp_id) with
    | None => errC "Compatible Appraisal ASP not found in ASP Compat Map"%string
    | Some appr_id => 
      resultC (asp_evt p (asp_paramsC appr_id args targ_plc targ) e)
    end
  | split_evt e1 e2 => 
      e1' <- appr_procedure G p e1 ;;
      e2' <- appr_procedure G p e2 ;;
      resultC (split_evt e1' e2')
  end.

(** Helper function for EvidenceT type reference semantics *)
Definition eval_asp (G : GlobalContext) (a : ASP) 
    (p : Plc) (e : EvidenceT) : ResultT EvidenceT string :=
  match a with
  | NULL => resultC mt_evt
  | CPY => resultC e
  | ASPC sp params =>
    let '(asp_paramsC asp_id args targ_plc targ) := params in
    match map_get (asp_types G) asp_id with
    | None => errC "ASP Type Signature not found in Environment"%string
    | Some fwd =>
      match fwd with
      | KEEP => resultC (sp_ev sp e)
      | KILL => resultC mt_evt
      | _ => resultC (asp_evt p params (sp_ev sp e))
      end
    end
  | APPR => appr_procedure G p e
  | SIG => resultC (asp_evt p sig_params e)
  | HSH => resultC (asp_evt p hsh_params e)
  | ENC q => resultC (asp_evt p (enc_params q) e)
  end.

(** EvidenceT Type denotational reference semantics.
    The EvidenceT associated with a term, a place, and some initial EvidenceT. *)

Fixpoint asp_comp_map_supports_ev (G : GlobalContext) (e : EvidenceT) :=
  match e with
  | mt_evt => True
  | nonce_evt n => True
  | asp_evt asp_top_plc ps e' => 
    let '(asp_paramsC asp_id args targ_plc targ) := ps in
    map_get (asp_comps G) asp_id <> None
  | split_evt e1 e2 => 
      asp_comp_map_supports_ev G e1 /\ 
      asp_comp_map_supports_ev G e2
  end.

Theorem asp_comp_map_supports_ev_iff_appr_procedure: 
  forall e p G,
  asp_comp_map_supports_ev G e <->
  exists e', appr_procedure G p e = resultC e'.
Proof.
  induction e; simpl in *; intros; try (intuition; eauto; ffa; fail);
  ff; intuition; try congruence; break_exists; try congruence;
  result_monad_unfold; ff;
  try erewrite IHe1 in *;
  try erewrite IHe2 in *;
  break_exists; repeat find_rewrite; try congruence;
  try (eexists; repeat find_rewrite; eauto; fail).
  * rewrite Heqr in H; congruence.
  * rewrite Heqr0 in H0; congruence. 
  Unshelve. all: eauto.
Qed.

Fixpoint eval (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : Term) 
    : ResultT EvidenceT string :=
  match t with
  | asp a => eval_asp G a p e
  | att q t1 => eval G q e t1
  | lseq t1 t2 => 
      e1 <- eval G p e t1 ;;
      eval G p e1 t2
  | bseq s t1 t2 => 
      e1 <- eval G p (splitEv_T_l s e) t1 ;; 
      e2 <- eval G p (splitEv_T_r s e) t2 ;;
      resultC (split_evt e1 e2)
  | bpar s t1 t2 => 
      e1 <- eval G p (splitEv_T_l s e) t1 ;; 
      e2 <- eval G p (splitEv_T_r s e) t2 ;;
      resultC (split_evt e1 e2)
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

Inductive Ev :=
| null: nat -> Plc -> Ev
| copy:  nat -> Plc -> Ev 
| umeas: nat -> Plc -> ASP_PARAMS -> EvidenceT -> Ev
| req: nat -> Plc -> Plc -> Term -> EvidenceT -> Ev
| rpy: nat -> Plc -> Plc -> EvidenceT -> Ev 
| split: nat -> Plc -> Ev
| join:  nat -> Plc -> Ev
| cvm_thread_start: nat -> Loc -> Plc -> Term -> EvidenceT -> Ev
| cvm_thread_end: nat -> Loc -> Ev.

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
  | cvm_thread_start i _ _ _ _ => i
  | cvm_thread_end i _ => i
  end.
(* 
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
  end. *)

(** Events are used in a manner that ensures that
[[
    forall e0 e1, ev e0 = ev e1 -> e0 = e1.
]]
See Lemma [events_injective].
 *)


Fixpoint asp_event (aspCM : ASP_Compat_MapT) (i : nat) (a : ASP) 
    (p : Plc) (e : EvidenceT) : ResultT Ev string :=
  match a with
  | NULL => resultC (null i p)
  | CPY => resultC (copy i p)
  | ASPC sp ps => resultC (umeas i p ps (sp_ev sp e))
  | APPR => 
    match e with
    | mt_evt => resultC (null i p)
    | nonce_evt n => resultC (umeas i p check_nonce_params (nonce_evt n))
    | asp_evt p' ps e' => 
      let '(asp_paramsC asp_id args targ_plc targ) := ps in
      match (map_get aspCM asp_id) with
      | None => errC "Compatible Appraisal ASP not found in ASP Compat Map"%string
      | Some appr_id => 
        resultC (umeas i p (asp_paramsC appr_id args targ_plc targ) e)
      end
    | split_evt e1 e2 => 
        e1' <- asp_event aspCM i a p e1 ;;
        e2' <- asp_event aspCM i a p e2 ;;
        resultC (join i p)
    end
  | SIG => resultC (umeas i p sig_params e)
  | HSH => resultC (umeas i p hsh_params e)
  | ENC q => resultC (umeas i p (enc_params q) e)
  end.

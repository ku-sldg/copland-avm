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
Import ListNotations.

Require Export Params_Admits.

Require Export Term_Defs_Core.


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
  | SIG => aspc (ASPCC (EXTD 1) sig_params)
  | HSH => aspc (ASPCC COMP hsh_params)
  | ENC q => aspc (ASPCC ENCR (enc_params q))
  end.

(**  Translating a Copland phrase to its Core_Term equivalent *)
Fixpoint copland_compile (t:Term) : Core_Term :=
  match t with
  | asp a => (asp_term_to_core a)
  | appr => apprc
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

(**  Calculate the size of an EvidenceT type *)
Fixpoint et_size (e:EvidenceT): nat :=
  match e with
  | mt_evt=> O
  | nonce_evt _ => 1
  | asp_evt _ fwd _ e' =>
    match fwd with
    | COMP => 1
    | ENCR => 1
    | (EXTD n) => n + et_size e'
    | KILL => 0
    | KEEP => et_size e'
    end 
  | appr_evt e' e'' => (et_size e') + (et_size e'')
  | split_evt e1 e2 => (et_size e1) + (et_size e2)
  end.

(**  Type-Tagged Raw EvidenceT representation.  Used as the internal EvidenceT
     type managed by the CVM to track EvidenceT contents and its structure. *)
Inductive EvC :=
| evc: RawEv -> EvidenceT -> EvC.

Definition mt_evc: EvC := (evc [] mt_evt).

Definition get_et (e:EvC) : EvidenceT :=
  match e with
  | evc ec et => et
  end.

Definition get_bits (e:EvC): list BS :=
  match e with
  | evc ls _ => ls
  end.

(** A "well-formed" EvC value is where the length of its raw EvidenceT portion
    has the proper size (calculated over the EvidenceT Type portion). *)
Inductive wf_ec : EvC -> Prop :=
| wf_ec_c: forall (ls:RawEv) et,
    List.length ls = et_size et ->
    wf_ec (evc ls et).

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

(** Helper function for EvidenceT type reference semantics *)
Definition eval_asp t p e :=
  match t with
  | NULL => mt_evt
  | CPY => e 
  | ASPC sp fwd params =>
    match fwd with
    | KEEP => (sp_ev sp e)
    | KILL => mt_evt
    | _ => asp_evt p fwd params (sp_ev sp e)
    end
  | SIG => asp_evt p (EXTD 1) sig_params e
  | HSH => asp_evt p COMP hsh_params e
  | ENC q => asp_evt p ENCR (enc_params q) e
  end.

(** EvidenceT Type denotational reference semantics.
    The EvidenceT associated with a term, a place, and some initial EvidenceT. *)
Import ResultNotation.

Fixpoint appr_procedure (p : Plc) (e:EvidenceT) (aspCM : ASP_Compat_MapT)
    : ResultT EvidenceT string :=
  match e with
  | mt_evt => resultC mt_evt
  | nonce_evt n => resultC (nonce_evt n)
  | asp_evt asp_top_plc fwd ps e' => 
    let '(asp_paramsC asp_id args targ_plc targ) := ps in
    (* NOTE: Do we need to be able to invert FWD and ARGS? *)
    match (map_get aspCM asp_id) with
    | None => errC "ASP not found"%string
    | Some appr_id => 
      e'' <- appr_procedure p e' aspCM ;;
      resultC (asp_evt p fwd (asp_paramsC appr_id args targ_plc targ) e'')
    end
  | appr_evt e' e'' => 
      new_e <- appr_procedure p e' aspCM ;;
      resultC (appr_evt new_e e)
  | split_evt e1 e2 => 
      e1' <- appr_procedure p e1 aspCM ;;
      e2' <- appr_procedure p e2 aspCM ;;
      resultC (split_evt e1' e2')
  end.

Fixpoint asp_comp_map_supports_ev (aspCM : ASP_Compat_MapT) (e : EvidenceT) :=
  match e with
  | mt_evt => True
  | nonce_evt n => True
  | asp_evt asp_top_plc fwd ps e' => 
    let '(asp_paramsC asp_id args targ_plc targ) := ps in
    (* NOTE: Do we need to be able to invert FWD and ARGS? *)
    map_get aspCM asp_id <> None /\
    asp_comp_map_supports_ev aspCM e'
  | appr_evt e' e'' => 
    asp_comp_map_supports_ev aspCM e' /\ asp_comp_map_supports_ev aspCM e''
    (* errC "Appr not implemented... not sure how exactly"%string *)
  | split_evt e1 e2 => 
      asp_comp_map_supports_ev aspCM e1 /\ asp_comp_map_supports_ev aspCM e2
  end.

Theorem asp_comp_map_supports_ev_iff_appr_procedure: 
  forall a p aspCM e,
  asp_comp_map_supports_ev aspCM e ->
  asp_comp_map_supports_ev aspCM (eval_asp a p e).

Fixpoint eval (t:Term) (p:Plc) (e:EvidenceT) (aspCM : ASP_Compat_MapT)
    : ResultT EvidenceT string :=
  match t with
  | asp a => resultC (eval_asp a p e)
  | att q t1 => eval t1 q e aspCM
  | appr => 
      e' <- appr_procedure p e aspCM ;;
      resultC (appr_evt e' e)
  | lseq t1 t2 => 
      e1 <- eval t1 p e aspCM ;;
      eval t2 p e1 aspCM
  | bseq s t1 t2 => 
      e1 <- eval t1 p (splitEv_T_l s e) aspCM ;; 
      e2 <- eval t2 p (splitEv_T_r s e) aspCM ;;
      resultC (split_evt e1 e2)
  | bpar s t1 t2 => 
      e1 <- eval t1 p (splitEv_T_l s e) aspCM ;; 
      e2 <- eval t2 p (splitEv_T_r s e) aspCM ;;
      resultC (split_evt e1 e2)
  end.


(* Lemma asp_comp_map_supports_ev_eval_asp : 
  forall a p aspCM e,
  asp_comp_map_supports_ev aspCM e ->
  asp_comp_map_supports_ev aspCM (eval_asp a p e).
Proof.
  destruct a; simpl in *; intuition; ff; eauto;
  unfold sp_ev; ff; intuition.

Lemma asp_comp_map_supports_ev_step : 
  forall t p aspCM e e',
  eval t p e aspCM = resultC e' ->
  asp_comp_map_supports_ev aspCM e ->
  asp_comp_map_supports_ev aspCM e'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using result_monad_unfold.
  - 
  - eapply IHt1 in Heqr; intuition; eauto;
    unfold splitEv_T_l, splitEv_T_r in *;
    ff;
    eapply IHt2 in Heqr0; intuition; eauto; 
    unfold asp_comp_map_supports_ev; eauto.
  - eapply IHt1 in Heqr; intuition; eauto;
    unfold splitEv_T_l, splitEv_T_r in *;
    ff;
    eapply IHt2 in Heqr0; intuition; eauto; 
    unfold asp_comp_map_supports_ev; eauto.
  - eapply IHt1 in Heqr; intuition; eauto;
    unfold splitEv_T_l, splitEv_T_r in *;
    ff;
    eapply IHt2 in Heqr0; intuition; eauto; 
    unfold asp_comp_map_supports_ev; eauto.
  -  
    eauto.
    unfold splitEv_T_r in *.
  induction e; simpl in *; intuition.
*)
Lemma eval_res_impl_asp_comp_map_supports_ev : forall t p e aspCM e',
  asp_comp_map_supports_ev aspCM e ->
  eval t p e aspCM = resultC e' ->
  asp_comp_map_supports_ev aspCM e'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using result_monad_unfold.
  - destruct a; simpl in *; intuition; ff; unfold sp_ev; ff; intuition.

Lemma asp_comp_map_supports_ev_step : 
  forall t2 t1 aspCM e e' e'' p,
  asp_comp_map_supports_ev aspCM e ->
  eval t1 p e aspCM = resultC e' ->
  eval t2 p e aspCM = resultC e'' ->
  exists e''', eval t2 p e' aspCM = resultC e'''.
Proof.
  intros.


Lemma asp_comp_map_supports_term_eval:
  forall aspCM t p e,
    asp_comp_map_supports_eval aspCM t e ->
    exists e', eval t p e aspCM = resultC e'.
Proof.
  unfold asp_comp_map_supports_eval.
  induction t; simpl in *; intuition; eauto; ffa using result_monad_unfold.
  - admit. 
  - edestruct IHt1; intuition; eauto; ff.
    rewrite H0 in Heqr; find_injection.
    edestruct IHt2; intuition; eauto; ff.
  unfold appr_procedure in *.

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
| appr_ev : nat -> Plc -> EvidenceT -> Ev
| req: nat -> Plc -> Plc -> Term -> EvidenceT -> Ev
| rpy: nat -> Plc -> Plc -> EvidenceT -> Ev 
| split: nat -> Plc -> Ev
| join:  nat -> Plc -> Ev
| cvm_thread_start: nat -> Loc -> Plc -> Core_Term -> EvidenceT -> Ev
| cvm_thread_end: nat -> Loc -> Ev.

(** The natural number used to distinguish events. *)

Definition ev x : nat :=
  match x with
  | null i _ => i
  | copy i _ => i
  | umeas i _ _ _ => i
  | appr_ev i _ _ => i
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


Definition asp_event i x p e :=
  match x with
  | NULL => null i p
  | CPY => copy i p
  | ASPC sp _ ps => umeas i p ps (sp_ev sp e)
  | SIG => umeas i p sig_params e
  | HSH => umeas i p hsh_params e
  | ENC q => umeas i p (enc_params q) e
  end.

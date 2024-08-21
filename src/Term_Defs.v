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

Require Import Maps EqClass List ID_Type Defs ErrorStringConstants Lia More_lists.
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

Definition splitEv_l (sp:Split) (e:Evidence): Evidence :=
  match sp with
  | (ALL, _) => e
  | _ => mt_evc
  end.

Definition splitEv_r (sp:Split) (e:Evidence): Evidence :=
  match sp with
  | (_,ALL) => e
  | _ => mt_evc
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
    | None => errC err_str_asp_no_compat_appr_asp
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
    | None => errC err_str_asp_no_type_sig
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

Fixpoint appr_events_size (G : GlobalContext) (e : EvidenceT) : ResultT nat string :=
  match e with
  | mt_evt => resultC 0
  | nonce_evt _ => resultC 1 (* [umeas check_nonce nonce] *)
  | asp_evt p par e' => resultC 1 (* Single dual appr asp for 1 *)
    (* let '(asp_paramsC asp_id args targ_plc targ) := par in
    match (map_get (asp_types G) asp_id) with
    | None => errC err_str_asp_no_type_sig
    | Some asp_fwd => 
      match asp_fwd with
      | COMP => resultC 1 (* Single dual appr asp for 1 *)
      | ENCR => resultC 1 (* Single dual appr asp for 1 *)
      | (EXTD n) => resultC 1 (* Single dual appr asp for 1 *)
      | KILL => resultC 0 (* this asp returns only mt_evc, which is appr as mt_evc too *)
      | KEEP => 
        n <- et_size G e' ;; (* this asp operates on stuff of size n, and returns of size n *)
        resultC (1 + n) (* they returned n, we do +1 for appr on top *)
      end
    end *)
  | split_evt e1 e2 =>
    s1 <- appr_events_size G e1 ;;
    s2 <- appr_events_size G e2 ;;
    resultC (2 + s1 + s2) (* split (1) + s1 evs + s2 evs + join (1) *)
  end.

(* EvidenceT Type size *)
Fixpoint events_size (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : Term)
    : ResultT nat string :=
  match t with
  | asp a => 
    match a with
    | APPR => appr_events_size G e (* appraisal does # of events based on ev type *)
    | _ => resultC 1 (* all other ASPs do 1 event for meas *)
    end
  | att p' t1 => 
    e' <- events_size G p' e t1 ;; (* remotely e' events are done *)
    resultC (2 + e') (* +1 for req, +e' for rem evs, +1 for rpy *)

  | lseq t1 t2 => 
    e1 <- events_size G p e t1 ;; (* first e1 events are done *)
    e' <- eval G p e t1 ;; (* we need a new evidence type for next step *)
    e2 <- events_size G p e' t2 ;; (* next e2 events are done *)
    resultC (e1 + e2) (* +e1 for first evs, +e2 for second evs *)
  
  | bseq s t1 t2 => 
    e1 <- events_size G p (splitEv_T_l s e) t1 ;; (* left does e1 events *)
    e2 <- events_size G p (splitEv_T_r s e) t2 ;; (* right does e2 events *)
    resultC (2 + e1 + e2) (* +1 for split; +e1,+e2 for sides, +1 for join *)
  | bpar s t1 t2 => 
    e1 <- events_size G p (splitEv_T_l s e) t1 ;; (* left does e1 events *)
    e2 <- events_size G p (splitEv_T_r s e) t2 ;; (* right does e2 events *)
    (* + 1 for split, +1 for thread_start; +e1,+e2 for sides, +1 for thread_join, + 1 for join *)
    resultC (4 + e1 + e2) 
  end.


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

Fixpoint asp_events (G : GlobalContext) (p : Plc) (e : EvidenceT) (a : ASP) (i : nat) 
    : ResultT (list Ev) string :=
  match a with
  | NULL => resultC ([null i p])
  | CPY => resultC ([copy i p])
  | ASPC sp ps => resultC ([umeas i p ps (sp_ev sp e)])
  | APPR => 
    match e with
    | mt_evt => resultC ([])
    | nonce_evt n => resultC ([umeas i p check_nonce_params (nonce_evt n)])
    | asp_evt p' ps e' => 
      let '(asp_paramsC asp_id args targ_plc targ) := ps in
      match (map_get (asp_comps G) asp_id) with
      | None => errC err_str_asp_no_compat_appr_asp
      | Some appr_id => 
        resultC ([umeas i p (asp_paramsC appr_id args targ_plc targ) e])
      end
    | split_evt e1 e2 => 
        e1' <- asp_events G p e1 a (S i) ;;
        let next_i := (S i) + (List.length e1') in
        e2' <- asp_events G p e2 a next_i ;;
        let last_i := next_i + (List.length e2') in
        resultC ([split i p] ++ e1' ++ e2' ++ [join last_i p])
    end
  | SIG => resultC ([umeas i p sig_params e])
  | HSH => resultC ([umeas i p hsh_params e])
  | ENC q => resultC ([umeas i p (enc_params q) e])
  end.

Lemma asp_appr_events_size_works : forall G p e i evs,
  asp_events G p e APPR i = resultC evs ->
  appr_events_size G e = resultC (List.length evs).
Proof.
  induction e; simpl in *; intros; try find_injection; 
  ffa using result_monad_unfold;
  repeat rewrite app_length; simpl in *; 
  f_equal; lia.
Qed.

Lemma asp_events_size_works : forall G p a e i evs,
  asp_events G p e a i = resultC evs ->
  events_size G p e (asp a) = resultC (List.length evs).
Proof.
  induction a; intros; simpl in *; 
  try eapply asp_appr_events_size_works; eauto;
  simpl in *; intuition; destruct e; simpl in *;
  repeat find_injection; ff; result_monad_unfold; ff.
Qed.

Theorem asp_events_deterministic_index : forall G p a e i evs,
  asp_events G p e a i = resultC evs ->
  forall v',
    true_last evs = Some v' ->
    ev v' = i + List.length evs - 1.
Proof.
  induction e; simpl in *; intros; ff; try lia.
  result_monad_unfold; 
  break_match; try congruence;
  break_match; try congruence;
  repeat find_injection; simpl in *;
  break_match; try (find_injection; simpl in *; lia).
  find_reverse_rewrite;
  repeat (
    find_apply_lem_hyp true_last_app_spec;
    intuition; try congruence;
    simpl in *;
    repeat find_injection;
    simpl in *;
    repeat rewrite app_length;
    simpl in *;
    try lia
  );
  repeat (find_apply_lem_hyp app_eq_nil;
    intuition; try congruence
  ).
  rewrite app_assoc in Heql1.
  eapply list_length_app_cons in Heql1;
  simpl in *;
  find_reverse_rewrite;
  rewrite <- app_assoc.
  simpl in *.
  repeat rewrite app_length; simpl in *.
  try lia.
Qed.

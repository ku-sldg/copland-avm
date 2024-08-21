(*
  Definition of the CVM Monad + monadic helper functions.
  Also included:  core simplification/automation tactics for the CVM Monad.

  Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ResultT Term Evidence_Bundlers Maps Session_Config_Compiler.

Require Import Coq.Program.Tactics.

Require Import Manifest_Admits ErrorStringConstants Attestation_Session.

Require Import String List.
Import ListNotations.

Require Export Cvm_St ErrorStMonad_Coq IO_Stubs Interface JSON_Core Axioms_Io.

Import ErrNotation.


(** * CVM monadic primitive operations *)

Definition get_ev : CVM Evidence :=
  st <- err_get ;;
  err_ret (st_ev st).

Definition get_trace : CVM (list Ev) :=
  st <- err_get ;;
  err_ret (st_trace st).

Definition get_evid : CVM Event_ID :=
  st <- err_get ;;
  err_ret (st_evid st).

Definition get_config : CVM Session_Config :=
  (* TODO:  consider moving this functionality to a Reader-like monad 
        i.e. an 'ask' primitive *)
  st <- err_get ;;
  err_ret (st_config st).

Definition put_ev (e' : Evidence) : CVM unit :=
  tr <- get_trace ;;
  i <- get_evid ;;
  sc <- get_config ;;
  err_put (mk_st e' tr i sc).

Definition put_trace (tr' : list Ev) : CVM unit :=
  e <- get_ev ;;
  i <- get_evid ;;
  sc <- get_config ;;
  err_put (mk_st e tr' i sc).

Definition put_evid (i' : Event_ID) : CVM unit :=
  e <- get_ev ;;
  tr <- get_trace ;;
  sc <- get_config ;;
  err_put (mk_st e tr i' sc).

Definition get_pl : CVM Plc :=
  sc <- get_config ;;
  err_ret (session_plc sc).

Definition inc_id : CVM Event_ID :=
  tr <- get_trace ;;
  e <- get_ev ;;
  i <- get_evid ;;
  sc <- get_config ;;
  err_put (mk_st e tr (Nat.add i (S O)) sc) ;;
  err_ret i.

(* Definition add_trace (tr':list Ev) : cvm_st -> cvm_st :=
  tr <- get_trace ;;
  

  fun '{| st_ev := e; st_trace := tr; st_evid := i; st_config := sc |} =>
    mk_st e (tr ++ tr') i sc. *)

Definition add_trace (tr:list Ev) : CVM unit :=
  tr' <- get_trace ;;
  put_trace (tr' ++ tr).

(* TODO: consider removing split/join events from reference semantics.
         Would make this (no-op) helper unecessary. *)
Definition split_ev : CVM unit :=
  p <- get_pl ;;
  i <- inc_id ;;
  add_trace [Term_Defs.split i p].

(** * Partially-symbolic implementations of IO operations *)

(* Generates a new event ID and adds a measurement event with that ID to the 
   CVM internal trace.  Returns the new Event_ID (used to represent raw 
   EvidenceT, relevant for appraisal verification).  *)
Definition tag_ASP (params :ASP_PARAMS) (mpl:Plc) (e:Evidence) : CVM Event_ID :=
  x <- inc_id ;;
  add_trace [umeas x mpl params (get_et e)] ;;
  err_ret x.

Definition join_seq (e1:Evidence) (e2:Evidence): CVM unit :=
  p <- get_pl ;;
  n <- inc_id ;;
  put_ev (ss_cons e1 e2) ;;
  add_trace [join n p].

(* Helper function that builds a new internal EvidenceT bundle based on 
   the EvidenceT extension parameter of an ASP term. *)
Definition bundle_asp (p:Plc) (rwev : RawEv) (e:Evidence) 
    (ps:ASP_PARAMS) : CVM Evidence :=
  sc <- get_config ;;
  let '(asp_paramsC asp_id args targ_plc targ) := ps in
  match (map_get (asp_types (session_context sc)) asp_id) with
  | None => err_failm (dispatch_error (Runtime err_str_asp_no_type_sig))
  | Some fwd =>
    match fwd with
    | COMP => 
        match comp_bundle rwev e p ps with
        | resultC e' => err_ret e'
        | errC e => err_failm (dispatch_error (Runtime e))
        end
    | EXTD n => 
        match extd_bundle rwev e p n ps with
        | resultC e' => err_ret e'
        | errC e => err_failm (dispatch_error (Runtime e))
        end
    | ENCR => 
        match encr_bundle rwev e p ps with
        | resultC e' => err_ret e'
        | errC e => err_failm (dispatch_error (Runtime e))
        end
    | KILL => err_ret mt_evc
    | KEEP => err_ret e
    end
  end.

(** * Stub for invoking external ASP procedures.  
      Extracted code should not need to use the Plc or Event_ID parameters 
      (those can be erased upon extraction). *)
Definition do_asp (params :ASP_PARAMS) (e:RawEv) (x:Event_ID) : CVM RawEv :=
  sc <- get_config  ;;
  match (sc.(aspCb) params e) with
  | resultC r => err_ret r
  | errC e => err_failm (dispatch_error e)
  end.

(* Simulates invoking an arbitrary ASP.  Tags the event, builds and returns 
   the new EvidenceT bundle. *)
Definition invoke_ASP (sp : SP) (params:ASP_PARAMS) : CVM Evidence :=
  e <-  match sp with
        | ALL => get_ev
        | NONE => err_ret mt_evc
        end ;;
  p <- get_pl ;;
  x <- tag_ASP params p e ;;
  rawev <- do_asp params (get_bits e) x ;;
  outev <- bundle_asp p rawev e params ;;
  err_ret outev.

Fixpoint peel_n_rawev (n : nat) (ls : RawEv) : CVM (RawEv * RawEv) :=
  match n with
  | 0 => err_ret ([], ls)
  | S n' =>
    match ls with
    | [] => err_failm (dispatch_error (Runtime errStr_peel_n_am))
    | x :: ls' =>
      v <- peel_n_rawev n' ls' ;;
      match v with
      | (ls1, ls2) => err_ret (x :: ls1, ls2)
      end
    end
  end.

Definition split_evidence (r : RawEv) (et1 et2 : EvidenceT) 
    : CVM (Evidence * Evidence) :=
  sc <- get_config ;;
  let G := (session_context sc) in
  match et_size G et1 with
  | errC e => err_failm (dispatch_error (Runtime e))
  | resultC et1_size => 
    match et_size G et2 with
    | errC e => err_failm (dispatch_error (Runtime e))
    | resultC et2_size =>
      '(l_ev, rest) <- peel_n_rawev et1_size r ;;
      '(r_ev, rest') <- peel_n_rawev et2_size rest ;;
      match rest' with
      | [] => err_ret (evc l_ev et1, evc r_ev et2)
      | _ => err_failm (dispatch_error (Runtime "Evidence splitting failed!"))
      end
    end
  end.

(* Simulates invoking an arbitrary ASP.  Tags the event, builds and returns 
   the new EvidenceT bundle. *)

Fixpoint invoke_APPR (et : EvidenceT) : CVM unit :=
  match et with
  | mt_evt => put_ev mt_evc (* appraise nothing = mt *)
  | nonce_evt n' => 
      ev' <- invoke_ASP ALL check_nonce_params ;;
      put_ev ev'
  | asp_evt p' par et' =>
    sc <- get_config ;;
    let '(asp_paramsC asp_id args targ_plc targ) := par in
    match (map_get (asp_comps (session_context sc)) asp_id) with
    | None => err_failm (dispatch_error (Runtime err_str_asp_no_compat_appr_asp))
    | Some appr_asp_id =>
      ev' <- invoke_ASP ALL (asp_paramsC appr_asp_id args targ_plc targ) ;;
      put_ev ev'
    end
  | split_evt et1 et2 =>
    split_ev ;; (* register event that we are splitting evidence *)
    (* first we must get out the actual Evidence for et1 *)
    top_ev <- get_ev ;;
    '(e1, e2) <- split_evidence (get_bits top_ev) et1 et2 ;;
    (* put ev for e1 to act on *)
    put_ev e1 ;;
    invoke_APPR et1 ;;
    ev1' <- get_ev ;;
    (* put ev for e2 to act on *)
    put_ev e2 ;;
    invoke_APPR et2 ;;
    ev2' <- get_ev ;;
    join_seq ev1' ev2' 
  end.
    
Definition copyEv : CVM Evidence :=
  p <- get_pl ;;
  x <- inc_id ;;
  add_trace [copy x p] ;;
  get_ev.

Definition nullEv : CVM Evidence :=
  p <- get_pl ;;
  x <- inc_id ;;
  add_trace [null x p] ;;
  err_ret mt_evc.

Definition clearEv : unit -> CVM Evidence :=
  fun _ => err_ret mt_evc.

(* Helper that interprets primitive core terms in the CVM.  *)
Definition do_prim (a: ASP) : CVM Evidence :=
  match a with
  | NULL => nullEv
  | CPY => copyEv
  | ASPC sp params => invoke_ASP sp params
  | SIG => invoke_ASP ALL sig_params
  | HSH => invoke_ASP ALL hsh_params
  | APPR => 
    e <- get_ev ;;
    invoke_APPR (get_et e) ;;
    get_ev
  | ENC q => invoke_ASP ALL (enc_params q)
  end.

(* event_id_span functions were HERE *)


(* Monadic helper function to simulate a span of remote event IDs 
   corresponding to the size of a Term *)
Definition inc_remote_event_ids (t:Term) : CVM unit :=
  i <- get_evid ;;
  sc <- get_config ;;
  p <- get_pl ;;
  ev <- get_ev ;;
  match (events_size (session_context sc) p (get_et ev) t) with
  | errC e => err_failm (dispatch_error (Runtime e))
  | resultC n => put_evid (Nat.add i n)
  end.

(* Monadic helper function to simulate a span of parallel event IDs 
   corresponding to the size of a Term *)
Definition inc_par_event_ids (e : Evidence) (t: Term) : CVM unit :=
  i <- get_evid ;;
  sc <- get_config ;;
  p <- get_pl ;;
  match (events_size (session_context sc) p (get_et e) t) with
  | errC e => err_failm (dispatch_error (Runtime e))
  | resultC n => put_evid (Nat.add i n)
  end.
  
(* Primitive monadic communication primitives 
   (some rely on Admitted IO Stubs). *)

Definition tag_REQ (t:Term) (p:Plc) (q:Plc) (e:Evidence) : CVM unit :=
  reqi <- inc_id ;;
  add_trace [req reqi p q t (get_et e)].

Definition tag_RPY (p:Plc) (q:Plc) (e:Evidence) : CVM unit :=
  rpyi <- inc_id ;;
  add_trace [rpy rpyi p q (get_et e)].

Definition get_cvm_policy : CVM PolicyT := 
  sc <- get_config ;;
  err_ret (policy sc).

Definition policy_list_not_disclosed (t:Term) (p:Plc) (e:EvidenceT) (ls: list (Plc * ASP_ID)) : bool :=   (* true. *)
  forallb (fun pr => negb (term_discloses_aspid_to_remote_enc_bool t p e (fst pr) (snd pr))) ls.

Definition check_cvm_policy (t:Term) (pTo:Plc) (et:EvidenceT) : CVM unit := 
  pol <- get_cvm_policy ;;
    match (policy_list_not_disclosed t pTo et pol) with
    | true => err_ret tt
    | false => err_failm (dispatch_error (Runtime errStr_disclosePolicy))
    end.
    
(* Remote communication primitives *)

Definition do_remote (sc : Session_Config) (pTo: Plc) (e : Evidence) (t:Term) 
    : ResultT RawEv DispatcherErrors := 
  (* There is assuredly a better way to do it than this *)
  let '(mkAtt_Sesplit_evt my_plc plc_map pk_map) := (session_config_decompiler sc) in
  (* We need  to update the Att Session to tell the next plc how
  they should be tagging their stuff (basically who they are
  in the protocol) *)
  let new_att_sesplit_evt := (mkAtt_Sesplit_evt pTo plc_map pk_map) in
  match (map_get plc_map pTo) with 
  | Some uuid => 
      let remote_req := (mkPRReq new_att_sesplit_evt my_plc e t) in
      let js_req := to_JSON remote_req in
      let resp_res := make_JSON_Network_Request uuid js_req in
      match resp_res with
      | resultC js_resp =>
          match from_JSON js_resp with
          | resultC resp => 
              let '(mkPRResp success ev) := resp in
              if success 
              then resultC ev 
              else errC (Runtime errStr_remote_am_failure)
          | errC msg => errC (Runtime msg)
          end
      | errC msg => errC (Runtime msg)
      end
  | None => errC (Unavailable)
  end.

Definition doRemote_session' (pTo:Plc) (e:Evidence) (t:Term) : CVM Evidence := 
  check_cvm_policy t pTo (get_et e) ;;
  sc <- get_config ;;
  match (do_remote sc pTo e t) with 
  | resultC ev => 
    match (eval (session_context sc) pTo (get_et e) t) with
    | resultC e' => err_ret (evc ev e')
    | errC e => err_failm (dispatch_error (Runtime e))
    end
  | errC e => err_failm (dispatch_error e)
  end.

Definition remote_session (t:Term) (p:Plc) (q:Plc) (e:Evidence) : CVM Evidence :=
  tag_REQ t p q e ;;
  e' <- doRemote_session' q e t ;;
  add_trace (cvm_events q (get_et e) t) ;;
  inc_remote_event_ids t ;;
  err_ret e'.

Definition doRemote (t:Term) (q:Plc) (e:Evidence) : CVM Evidence :=
  p <- get_pl ;;
  e' <- remote_session t p q e ;;
  tag_RPY p q e' ;;
  err_ret e'.

(* Primitive monadic parallel CVM thread primitives 
   (some rely on Admitted IO Stubs). *)

Definition start_par_thread (t: Term) (e:Evidence) : CVM nat :=
  p <- get_pl ;;
  i <- inc_id ;;
  (* The loc always = the event id for the thread_start event *)
  do_start_par_thread i e t ;;
  add_trace [cvm_thread_start i i p t (get_et e)] ;;
  err_ret i.

Definition wait_par_thread (loc:Loc) (e:Evidence) (t: Term) : CVM Evidence :=
  p <- get_pl ;;
  e' <- do_wait_par_thread loc p e t ;;
  inc_par_event_ids e t ;;
  i <- inc_id ;;
  add_trace [cvm_thread_end i loc] ;;
  err_ret e'.
   
Ltac cvm_monad_unfold :=
  repeat unfold
  do_prim,
  doRemote,
  remote_session,
  doRemote_session',
  check_cvm_policy,
  invoke_ASP,
  bundle_asp,
  extd_bundle,
  comp_bundle,
  encr_bundle,
  do_asp,
  clearEv,
  copyEv,
  nullEv,
  inc_remote_event_ids,
  inc_par_event_ids,
  wait_par_thread,
  join_seq,
  
  get_ev,
  put_ev,
  get_pl,
  get_evid,
  put_evid,
  get_config,
  add_trace,
  put_trace in * ;
  repeat err_monad_unfold;
  simpl in * .

(* Grouping together some common hypothesis normalizations.  Inverting pairs of
   Some values, cvm_st equivalences, etc. *)
Ltac pairs :=
  simpl in *;
  vmsts;
  repeat
    match goal with
    | [H: (Some _, _) =
          (Some _, _) |- _ ] => invc H; cvm_monad_unfold
                                                          
    | [H: {| st_ev := _; st_trace := _; st_evid := _; st_config := _ |} =
          {| st_ev := _; st_trace := _; st_evid := _; st_config := _ |} |- _ ] =>
      invc H; cvm_monad_unfold
    end; destruct_conjs; cvm_monad_unfold.

(*
  Definition of the CVM Monad + monadic helper functions.
  Also included:  core simplification/automation tactics for the CVM Monad.

  Author:  Adam Petz, ampetz@ku.edu
*)
Require Import String List.

Require Import ResultT Term Maps Session_Config_Compiler.

Require Import Coq.Program.Tactics.

Require Import Manifest_Admits ErrorStringConstants Attestation_Session EqClass.

Import ListNotations.

Require Export Cvm_St ErrorStMonad_Coq IO_Stubs Interface JSON_Core.

Import ErrNotation.


(** * CVM monadic primitive operations *)

Definition get_trace : CVM (list Ev) :=
  st <- err_get_state ;;
  err_ret (st_trace st).

Definition get_evid : CVM Event_ID :=
  st <- err_get_state ;;
  err_ret (st_evid st).

Definition get_config : CVM Session_Config :=
  err_get_config.

Definition put_trace (tr' : list Ev) : CVM unit :=
  i <- get_evid ;;
  err_put_state (mk_st tr' i).

Definition put_evid (i' : Event_ID) : CVM unit :=
  tr <- get_trace ;;
  err_put_state (mk_st tr i').

Definition get_pl : CVM Plc :=
  sc <- get_config ;;
  err_ret (session_plc sc).

Definition inc_id : CVM Event_ID :=
  tr <- get_trace ;;
  i <- get_evid ;;
  err_put_state (mk_st tr (Nat.add i (S O))) ;;
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

Definition join_seq (e1:Evidence) (e2:Evidence): CVM Evidence :=
  p <- get_pl ;;
  n <- inc_id ;;
  let '(evc bits1 et1) := e1 in
  let '(evc bits2 et2) := e2 in
  add_trace [join n p] ;;
  err_ret (evc (bits1 ++ bits2) (split_evt et1 et2)).

(* Helper function that builds a new internal EvidenceT bundle based on 
   the EvidenceT extension parameter of an ASP term. *)
Definition bundle_asp (p:Plc) (rwev : RawEv) 
    (cur_ev : Evidence) (ps:ASP_PARAMS) : CVM Evidence :=
  sc <- get_config ;;
  let '(asp_paramsC asp_id args targ_plc targ) := ps in
  match (map_get asp_id (asp_types (session_context sc))) with
  | None => err_failm (dispatch_error (Runtime err_str_asp_no_type_sig))
  | Some (ev_arrow fwd in_sig (OutN n)) =>
    if (eqb (length rwev) n)
    then 
      match fwd with
(* The semantics for a "REPLACE" asp are it CONSUMES all incoming evidence,
then returns a new collection of evidence that will REPLACE the CVMs current 
Evidence *)
      | REPLACE => err_ret (evc rwev (asp_evt p ps (get_et cur_ev)))
(* The semantics for a "WRAP" asp are the exact same as "REPLACE" for the 
attestation and bundling side of the CVM. Wraps main distinction lies in the
fact that its is a GUARANTEE, that the dual appraisal ASP is actually an
inverse, thus allowing WRAPPED evidence to be recovered via appraisal *)
      | WRAP => err_ret (evc rwev (asp_evt p ps (get_et cur_ev)))
(* The semantics for an "EXTEND" asp are it APPENDS all incoming evidence to the
current CVM evidence bundle *)
      | EXTEND =>
        match cur_ev with
        | evc bits et => err_ret (evc (rwev ++ bits) (asp_evt p ps et))
        end
      end
    else err_failm (dispatch_error (Runtime errStr_raw_EvidenceT_too_long))
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
Definition invoke_ASP (e : Evidence) (params:ASP_PARAMS) : CVM Evidence :=
  p <- get_pl ;;
  x <- tag_ASP params p e ;;
  rawev <- do_asp params (get_bits e) x ;;
  outev <- bundle_asp p rawev e params ;;
  err_ret outev.

Fixpoint peel_n_rawev (n : nat) (ls : RawEv) : ResultT (RawEv * RawEv) string :=
  match n with
  | 0 => resultC ([], ls)
  | S n' =>
    match ls with
    | [] => errC errStr_peel_n_am
    | x :: ls' =>
      match peel_n_rawev n' ls' with
      | errC e => errC e
      | resultC (ls1, ls2) => resultC (x :: ls1, ls2)
      end
    end
  end.

Definition hoist_result {A : Type} (r : ResultT A string) : CVM A :=
  match r with
  | resultC a => err_ret a
  | errC e => err_failm (dispatch_error (Runtime e))
  end.

Definition split_evidence (e : Evidence) (et1 et2 : EvidenceT) 
    : CVM (Evidence * Evidence) :=
  sc <- get_config ;;
  match (get_et e) with
  | mt_evt => err_failm (dispatch_error (Runtime "Cannot split null evidence!"))
  | nonce_evt _ => err_failm (dispatch_error (Runtime "Cannot split nonce evidence!"))
  | asp_evt _ _ _ => err_failm (dispatch_error (Runtime "Cannot split ASP evidence!"))
  | split_evt et1' et2' =>
    if (eqb et1 et1')
    then 
      if (eqb et2 et2')
      then 
        let r := get_bits e in
        let G := (session_context sc) in
        match et_size G et1 with
        | errC e => err_failm (dispatch_error (Runtime e))
        | resultC et1_size => 
          match et_size G et2 with
          | errC e => err_failm (dispatch_error (Runtime e))
          | resultC et2_size =>
            '(l_ev, rest) <- (hoist_result (peel_n_rawev et1_size r)) ;;
            '(r_ev, rest') <- (hoist_result (peel_n_rawev et2_size rest)) ;;
            match rest' with
            | [] => err_ret (evc l_ev et1, evc r_ev et2)
            | _ => err_failm (dispatch_error (Runtime "Evidence splitting failed: Rest of evidence not empty"))
            end
          end
        end
      else err_failm (dispatch_error (Runtime "Evidence splitting failed: et2 does not match"))
    else err_failm (dispatch_error (Runtime "Evidence splitting failed: et1 does not match"))
  end.

(* Simulates invoking an arbitrary ASP.  Tags the event, builds and returns 
   the new EvidenceT bundle. *)

Fixpoint invoke_APPR' (r : RawEv) (et : EvidenceT) (out_evt : EvidenceT) : CVM Evidence :=
  match et with
  | mt_evt => err_ret mt_evc 
  | nonce_evt n' => invoke_ASP (evc r out_evt) check_nonce_params
  | asp_evt p' par et' =>
    sc <- get_config ;;
    let '(asp_paramsC asp_id args targ_plc targ) := par in
    match (map_get asp_id (asp_comps (session_context sc))) with
    | None => err_failm (dispatch_error (Runtime err_str_asp_no_compat_appr_asp))
    | Some appr_asp_id =>
      let dual_par := asp_paramsC appr_asp_id args targ_plc targ in
      match (map_get asp_id (asp_types (session_context sc))) with
      | None => err_failm (dispatch_error (Runtime err_str_asp_no_type_sig))
      | Some (ev_arrow fwd in_sig out_sig) =>
        match fwd with
        | REPLACE => (* Only do the dual ASP *)
          invoke_ASP (evc r out_evt) dual_par
        | WRAP =>
          (* first do the dual ASP to unwrap *)
          '(evc r'' et'') <- invoke_ASP (evc r out_evt) dual_par ;;
          (* Check that the "UNWRAP" occured properly *)
          match et_size (session_context sc) et'' with
          | errC e => err_failm (dispatch_error (Runtime e))
          | resultC n' => 
            match et_size (session_context sc) et' with
            | errC e => err_failm (dispatch_error (Runtime e))
            | resultC n'' =>
              if (eqb n' n'')
              then (* The "UNWRAP" worked *)
                (* so do the recursive call *)
                invoke_APPR' r'' et' (asp_evt (session_plc sc) dual_par out_evt)
              else err_failm (dispatch_error (Runtime "Appraisal for WRAP ASP failed. Size of input to wrap is not same as output of UNWRAP"))
            end
          end
        | EXTEND =>
          let '(OutN n) := out_sig in
          (* first we split, left for the appr of extended part, right for rest *)
          split_ev ;;
          '(_, r_ev) <- (hoist_result (peel_n_rawev n r)) ;;

          (* on left we do the dual of EXTEND *)
          ev1 <- invoke_ASP (evc r out_evt) dual_par ;;

          (* now on right, we work only on the remaining evidence *)
          (* our new evidence is e' *)
          (* now we do the recursive call *)
          ev2 <- invoke_APPR' r_ev et' et' ;;
          (* now join *)
          join_seq ev1 ev2 
        end
      end
      (* ev' <- invoke_ASP (asp_paramsC appr_asp_id args targ_plc targ) ;;
      put_ev ev' *)
    end
  | split_evt et1 et2 =>
    match out_evt with
    | split_evt et1' et2' =>
      if (eqb et1 et1')
      then 
        if (eqb et2 et2')
        then 
          split_ev ;; (* register event that we are splitting evidence *)
          (* first we must get out the actual Evidence for et1 *)
          '((evc r1' et1'), (evc r2' et2')) <- split_evidence (evc r et) et1 et2 ;;
          ev1' <- invoke_APPR' r1' et1 et1' ;;
          ev2' <- invoke_APPR' r2' et2 et2' ;;
          join_seq ev1' ev2' 
        else err_failm (dispatch_error (Runtime "Evidence splitting failed: et2 does not match"))
      else err_failm (dispatch_error (Runtime "Evidence splitting failed: et1 does not match"))
    | _ => err_failm (dispatch_error (Runtime "Evidence splitting failed: out_evt does not match"))
    end
  end.

Definition invoke_APPR (e : Evidence) : CVM Evidence :=
  invoke_APPR' (get_bits e) (get_et e) (get_et e).

Definition nullEv : CVM Evidence :=
  p <- get_pl ;;
  x <- inc_id ;;
  add_trace [null x p] ;;
  err_ret mt_evc.

Definition clearEv : unit -> CVM Evidence :=
  fun _ => err_ret mt_evc.

(* Helper that interprets primitive core terms in the CVM.  *)
Definition do_prim (e : Evidence) (a: ASP) : CVM Evidence :=
  match a with
  | NULL => nullEv
  | ASPC params => invoke_ASP e params
  | SIG => invoke_ASP e sig_params
  | HSH => invoke_ASP e hsh_params
  | APPR => invoke_APPR e 
  | ENC q => invoke_ASP e (enc_params q)
  end.

(* Monadic helper function to simulate a span of remote event IDs 
   corresponding to the size of a Term *)
Definition inc_remote_event_ids (e : Evidence) (t:Term) : CVM unit :=
  i <- get_evid ;;
  sc <- get_config ;;
  p <- get_pl ;;
  match (events_size (session_context sc) p (get_et e) t) with
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
  add_trace [req reqi p q (get_et e) t].

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
    : ResultT Evidence CVM_Error := 
  (* There is assuredly a better way to do it than this *)
  let '(mkAtt_Sess my_plc plc_map pk_map G) := (session_config_decompiler sc) in
  (* We need  to update the Att Session to tell the next plc how
  they should be tagging their stuff (basically who they are
  in the protocol) *)
  let new_att_sess := (mkAtt_Sess pTo plc_map pk_map G) in
  match (map_get pTo plc_map) with 
  | Some uuid => 
      let remote_req := (mkPRReq new_att_sess my_plc e t) in
      let js_req := to_JSON remote_req in
      let resp_res := make_JSON_Network_Request uuid js_req in
      match resp_res with
      | resultC js_resp =>
          match from_JSON js_resp with
          | resultC resp => 
              let '(mkPRResp success ev) := resp in
              if success 
              then resultC ev 
              else errC (dispatch_error (Runtime errStr_remote_am_failure))
          | errC msg => errC (dispatch_error (Runtime msg)) 
          end
      | errC msg => errC (dispatch_error (Runtime msg))
      end
  | None => errC (dispatch_error Unavailable)
  end.

Definition doRemote_session' (pTo:Plc) (e:Evidence) (t:Term) 
    : CVM Evidence := 
  check_cvm_policy t pTo (get_et e) ;;
  sc <- get_config ;;
  match (do_remote sc pTo e t) with
  | resultC e' => err_ret e'
  | errC s => err_failm s
  end.

Definition remote_session (p:Plc) (q:Plc) (e:Evidence) (t:Term) : CVM Evidence :=
  tag_REQ t p q e ;;
  e' <- doRemote_session' q e t ;;
  sc <- get_config ;;
  i <- get_evid ;;
  rem_evs <- match events_fix (session_context sc) q (get_et e) t i with
  | errC e => err_failm (dispatch_error (Runtime e))
  | resultC evs => err_ret evs
  end ;;
  add_trace rem_evs ;;
  inc_remote_event_ids e t ;;
  err_ret e'.

Definition doRemote (q:Plc) (e:Evidence) (t:Term) : CVM Evidence :=
  p <- get_pl ;;
  e' <- remote_session p q e t ;;
  tag_RPY p q e' ;;
  err_ret e'.

(* Primitive monadic parallel CVM thread primitives 
   (some rely on Admitted IO Stubs). *)

Definition start_par_thread (e:Evidence) (t: Term) : CVM nat :=
  p <- get_pl ;;
  i <- inc_id ;;
  (* The loc always = the event id for the thread_start event *)
  do_start_par_thread i e t ;;
  add_trace [cvm_thread_start i i p (get_et e) t] ;;
  err_ret i.

Definition do_wait_par_thread (loc:Loc) (p:Plc) (e:Evidence) (t: Term) : CVM Evidence :=
  match (parallel_vm_thread loc p e t) with
  | resultC e' => err_ret e'
  | errC s => err_failm s
  end.

Definition wait_par_thread (loc:Loc) (e:Evidence) (t: Term) : CVM Evidence :=
  p <- get_pl ;;
  e' <- do_wait_par_thread loc p e t ;;
  i <- get_evid ;;
  sc <- get_config ;;
  rem_evs <- match events_fix (session_context sc) p (get_et e) t i with
  | errC e => err_failm (dispatch_error (Runtime e))
  | resultC evs => err_ret evs
  end ;;
  add_trace rem_evs ;;
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
  do_asp,
  clearEv,
  nullEv,
  hoist_result,
  inc_remote_event_ids,
  inc_par_event_ids,
  wait_par_thread,
  do_wait_par_thread,
  join_seq,
  
  get_pl,
  get_evid,
  put_evid,
  get_config,
  add_trace,
  put_trace in * ;
  repeat err_monad_unfold;
  simpl in * .

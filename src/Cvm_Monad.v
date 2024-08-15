(*
  Definition of the CVM Monad + monadic helper functions.
  Also included:  core simplification/automation tactics for the CVM Monad.

  Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ResultT Term EvidenceT_Bundlers Axioms_Io Maps Session_Config_Compiler.

Require Import Coq.Program.Tactics.

Require Import Manifest_Admits ErrorStringConstants Attestation_Session.

Require Import String List.
Import ListNotations.

Require Export Cvm_St ErrorStMonad_Coq IO_Stubs Interface.

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

Definition modify_evm (f:Evidence -> Evidence) : CVM unit :=
  e <- get_ev ;;
  put_ev (f e).

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

(* Helper function that builds a new internal EvidenceT bundle based on 
   the EvidenceT extension parameter of an ASP term. *)
Definition fwd_asp (fwd:FWD) (rwev : RawEv) (e:Evidence) (p:Plc) (ps:ASP_PARAMS): CVM Evidence :=
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
Definition invoke_ASP (fwd:FWD) (params:ASP_PARAMS) (* (ac : AM_Config) *) : CVM Evidence :=
  e <- get_ev ;;
  p <- get_pl ;;
  x <- tag_ASP params p e ;;
  rawev <- do_asp params (get_bits e) x ;;
  outev <- fwd_asp fwd rawev e p params ;;
  err_ret outev.

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
Definition do_prim (a:ASP_Core) (* (ac : AM_Config) *) : CVM Evidence :=
  match a with
  | NULLC => nullEv
  | CLEAR => clearEv tt
  | CPYC => copyEv
  | ASPCC fwd params => invoke_ASP fwd params
  end.


(* event_id_span functions were HERE *)


(* Monadic helper function to simulate a span of remote event IDs 
   corresponding to the size of a Term *)
Definition inc_remote_event_ids (t:Term) : CVM unit :=
  i <- get_evid ;;
  put_evid (Nat.add i (event_id_span' t)).

(* Monadic helper function to simulate a span of parallel event IDs 
   corresponding to the size of a Core_Term *)
Definition inc_par_event_ids (t:Core_Term) : CVM unit :=
  i <- get_evid ;;
  put_evid (Nat.add i (event_id_span t)).
  
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

Definition do_remote (t:Term) (pTo:Plc) (e:Evidence) (sc : Session_Config) 
    : ResultT RawEv DispatcherErrors := 
  (* There is assuredly a better way to do it than this *)
  let '(mkAtt_Sesplit_evt my_plc plc_map pk_map) := (session_config_decompiler sc) in
  (* We need  to update the Att Session to tell the next plc how
  they should be tagging their stuff (basically who they are
  in the protocol) *)
  let new_att_sesplit_evt := (mkAtt_Sesplit_evt pTo plc_map pk_map) in
  match (map_get plc_map pTo) with 
  | Some uuid => 
      let remote_req := (mkPRReq new_att_sesplit_evt t my_plc (get_bits e)) in
      let js_req := to_JSON remote_req in
      let resp_res := make_JSON_Network_Request uuid js_req in
      match resp_res with
      | resultC js_resp =>
          match from_JSON js_resp with
          | resultC resp => 
              let '(mkPRResp succesplit_evt ev) := resp in
              if succesplit_evt 
              then resultC ev 
              else errC (Runtime errStr_remote_am_failure)
          | errC msg => errC (Runtime msg)
          end
      | errC msg => errC (Runtime msg)
      end
  | None => errC (Unavailable)
  end.

Definition doRemote_session' (t:Term) (pTo:Plc) (e:Evidence) : CVM Evidence := 
  check_cvm_policy t pTo (get_et e) ;;
  sc <- get_config ;;
  match (do_remote t pTo e sc) with 
  | resultC ev => err_ret (evc ev (eval t pTo (get_et e)))  
  | errC e => err_failm (dispatch_error e)
  end.

Definition remote_session (t:Term) (p:Plc) (q:Plc) (e:Evidence) : CVM Evidence :=
  tag_REQ t p q e ;;
  e' <- doRemote_session' t q e ;;
  add_trace (cvm_events t q (get_et e)) ;;
  inc_remote_event_ids t ;;
  err_ret e'.

Definition doRemote (t:Term) (q:Plc) (e:Evidence) : CVM Evidence :=
  p <- get_pl ;;
  e' <- remote_session t p q e ;;
  tag_RPY p q e' ;;
  err_ret e'.

Definition join_seq (e1:Evidence) (e2:Evidence): CVM unit :=
  p <- get_pl ;;
  n <- inc_id ;;
  put_ev (ss_cons e1 e2) ;;
  add_trace [join n p].

(* Primitive monadic parallel CVM thread primitives 
   (some rely on Admitted IO Stubs). *)

Definition start_par_thread (loc:Loc) (t:Core_Term) (e:Evidence) : CVM unit :=
  p <- get_pl ;;
  do_start_par_thread loc t (get_bits e) ;;
  add_trace [cvm_thread_start loc p t (get_et e)].

Definition wait_par_thread (loc:Loc) (t:Core_Term) (e:Evidence) : CVM Evidence :=
  p <- get_pl ;;
  e' <- do_wait_par_thread loc t p e ;;
  add_trace [cvm_thread_end loc] ;;
  inc_par_event_ids t ;;
  err_ret e'.
   
Ltac cvm_monad_unfold :=
  repeat unfold
  do_prim,
  doRemote,
  remote_session,
  doRemote_session',
  check_cvm_policy,
  invoke_ASP,
  fwd_asp,
  extd_bundle,
  comp_bundle,
  encr_bundle,
  do_asp,
  clearEv,
  copyEv,
  nullEv,
  
  get_ev,
  get_pl,
  get_config,
  add_trace,
  modify_evm,
  add_trace in * ;
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

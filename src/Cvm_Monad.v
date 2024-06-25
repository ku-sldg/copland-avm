(*
  Definition of the CVM Monad + monadic helper functions.
  Also included:  core simplification/automation tactics for the CVM Monad.

  Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ResultT Term_Defs Term ConcreteEvidence Evidence_Bundlers Defs Axioms_Io StructTactics.

Require Import Coq.Program.Tactics Lia.

Require Import Manifest_Admits ErrorStringConstants.

Require Import String List.
Import ListNotations.

Require Export Cvm_St ErrorStMonad_Coq IO_Stubs CvmJson_Interfaces.


(** * CVM monadic primitive operations *)

Definition put_ev (e:EvC) : CVM unit :=
  st <- get ;;
     let tr' := st_trace st in
     let i := st_evid st in
     let ac := st_AM_config st in
     put (mk_st e tr' i ac).

Definition get_ev : CVM EvC :=
  st <- get ;;
  ret (st_ev st).

Definition get_CVM_amConfig : CVM AM_Config :=
  (* TODO:  consider moving this functionality to a Reader-like monad 
        i.e. an 'ask' primitive *)
  st <- get ;;
  ret (st_AM_config st).

Definition get_pl : CVM Plc :=
  ac <- get_CVM_amConfig ;;
  ret (my_abstract_plc (absMan ac)).

Definition inc_id : CVM Event_ID :=
  st <- get ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let i := st_evid st in
    let ac := st_AM_config st in
    put (mk_st e' tr' (Nat.add i (S O)) ac) ;;
    ret i.

Definition modify_evm (f:EvC -> EvC) : CVM unit :=
  st <- get ;;
  let '{| st_ev := e; st_trace := tr; st_evid := i; st_AM_config := ac |} := st in
  put (mk_st (f e) tr i ac).

Definition add_trace (tr':list Ev) : cvm_st -> cvm_st :=
  fun '{| st_ev := e; st_trace := tr; st_evid := i; st_AM_config := ac |} =>
    mk_st e (tr ++ tr') i ac.

Definition add_tracem (tr:list Ev) : CVM unit :=
  modify (add_trace tr).

(* TODO: consider removing split/join events from reference semantics.
         Would make this (no-op) helper unecessary. *)
Definition split_ev : CVM unit :=
  p <- get_pl ;;
  i <- inc_id ;;
  add_tracem [Term_Defs.split i p].


(** * Partially-symbolic implementations of IO operations *)

(* Generates a new event ID and adds a measurement event with that ID to the 
   CVM internal trace.  Returns the new Event_ID (used to represent raw 
   evidence, relevant for appraisal verification).  *)
Definition tag_ASP (params :ASP_PARAMS) (mpl:Plc) (e:EvC) : CVM Event_ID :=
  x <- inc_id ;;
  add_tracem [umeas x mpl params (get_et e)] ;;
  ret x.

(* Helper function that builds a new internal evidence bundle based on 
   the evidence extension parameter of an ASP term. *)
Definition fwd_asp (fwd:FWD) (rwev : RawEv) (e:EvC) (p:Plc) (ps:ASP_PARAMS): CVM EvC :=
  match fwd with
  | COMP => 
      match comp_bundle rwev e p ps with
      | resultC e' => ret e'
      | errC e => failm (dispatch_error (Runtime e))
      end
  | EXTD n => 
      match extd_bundle rwev e p n ps with
      | resultC e' => ret e'
      | errC e => failm (dispatch_error (Runtime e))
      end
  | ENCR => 
      match encr_bundle rwev e p ps with
      | resultC e' => ret e'
      | errC e => failm (dispatch_error (Runtime e))
      end
  | KILL => ret mt_evc
  | KEEP => ret e
  end.

(** * Stub for invoking external ASP procedures.  
      Extracted code should not need to use the Plc or Event_ID parameters 
      (those can be erased upon extraction). *)
Definition do_asp (params :ASP_PARAMS) (e:RawEv) (x:Event_ID) : CVM RawEv :=
  ac <- get_CVM_amConfig  ;;
  match (ac.(aspCb) params e) with
  | resultC r => ret r
  | errC e => failm (dispatch_error e)
  end.

(* Simulates invoking an arbitrary ASP.  Tags the event, builds and returns 
   the new evidence bundle. *)
Definition invoke_ASP (fwd:FWD) (params:ASP_PARAMS) (* (ac : AM_Config) *) : CVM EvC :=
  e <- get_ev ;;
  p <- get_pl ;;
  x <- tag_ASP params p e ;;
  rawev <- do_asp params (get_bits e) x ;;
  outev <- fwd_asp fwd rawev e p params ;;
  ret outev.

Definition copyEv : CVM EvC :=
  p <- get_pl ;;
  x <- inc_id ;;
  add_tracem [copy x p] ;;
  get_ev.

Definition nullEv : CVM EvC :=
  p <- get_pl ;;
  x <- inc_id ;;
  add_tracem [null x p] ;;
  ret mt_evc.

Definition clearEv : unit -> CVM EvC :=
  fun _ => ret mt_evc.

(* Helper that interprets primitive core terms in the CVM.  *)
Definition do_prim (a:ASP_Core) (* (ac : AM_Config) *) : CVM EvC :=
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
  st <- get ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let i := st_evid st in
    let new_i := Nat.add i (event_id_span' t) in
    let ac := st_AM_config st in
    put (mk_st e' tr' new_i ac).

(* Monadic helper function to simulate a span of parallel event IDs 
   corresponding to the size of a Core_Term *)
Definition inc_par_event_ids (t:Core_Term) : CVM unit :=
  st <- get ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let i := st_evid st in
    let new_i := Nat.add i (event_id_span t) in
    let ac := st_AM_config st in
    put (mk_st e' tr' new_i ac).
  
(* Primitive monadic communication primitives 
   (some rely on Admitted IO Stubs). *)

Definition tag_REQ (t:Term) (p:Plc) (q:Plc) (e:EvC) : CVM unit :=
  reqi <- inc_id ;;
  add_tracem [req reqi p q t (get_et e)].

Definition tag_RPY (p:Plc) (q:Plc) (e:EvC) : CVM unit :=
  rpyi <- inc_id ;;
  add_tracem [rpy rpyi p q (get_et e)].

Definition get_cvm_policy : CVM PolicyT := 
  ac <- get_CVM_amConfig ;;
  ret (policy (absMan ac)).

Definition check_cvm_policy (t:Term) (pTo:Plc) (et:Evidence) : CVM unit := 
  pol <- get_cvm_policy ;;
    match (policy_list_not_disclosed t pTo et pol) with
    | true => ret tt
    | false => failm (dispatch_error (Runtime errStr_disclosePolicy))
    end.

Definition do_remote (t:Term) (pTo:Plc) (e:EvC) (ac: AM_Config) : ResultT RawEv DispatcherErrors := 
  let remote_uuid_res : ResultT UUID DispatcherErrors := ac.(plcCb) pTo in
    match remote_uuid_res with 
    | resultC uuid => 
        let my_plc := (my_abstract_plc (absMan ac)) in
        let remote_req := (mkPRReq t my_plc (get_bits e)) in
        let js_req := ProtocolRunRequest_to_JSON remote_req in
        let js_resp := make_JSON_Network_Request uuid js_req in
        match JSON_to_AM_Protocol_Response js_resp with
        | resultC resp => 
            match resp with
            | Protocol_Run_Response prresp => 
                let '(mkPRResp success ev) := prresp in
                if success 
                then resultC ev 
                else errC (Runtime errStr_remote_am_failure)
            | _ => errC (Runtime errStr_incorrect_resp_type)
            end
        | errC msg => errC (Runtime msg)
        end
    | errC e => errC e
    end.

Definition doRemote_session' (t:Term) (pTo:Plc) (e:EvC) : CVM EvC := 
  check_cvm_policy t pTo (get_et e) ;;
  ac <- get_CVM_amConfig ;;
  match (do_remote t pTo e ac) with 
  | resultC ev => ret (evc ev (eval t pTo (get_et e)))  
  | errC e => failm (dispatch_error e)
  end.

Definition remote_session (t:Term) (p:Plc) (q:Plc) (e:EvC) : CVM EvC :=
  tag_REQ t p q e ;;
  e' <- doRemote_session' t q e ;;
  add_tracem (cvm_events t q (get_et e)) ;;
  inc_remote_event_ids t ;;
  ret e'.

Definition doRemote (t:Term) (q:Plc) (e:EvC) : CVM EvC :=
  p <- get_pl ;;
  e' <- remote_session t p q e ;;
  tag_RPY p q e' ;;
  ret e'.

Definition join_seq (e1:EvC) (e2:EvC): CVM unit :=
  p <- get_pl ;;
  n <- inc_id ;;
  put_ev (ss_cons e1 e2) ;;
  add_tracem [join n p].

(* Primitive monadic parallel CVM thread primitives 
   (some rely on Admitted IO Stubs). *)

Definition start_par_thread (loc:Loc) (t:Core_Term) (e:EvC) : CVM unit :=
  p <- get_pl ;;
  do_start_par_thread loc t (get_bits e) ;;
  add_tracem [cvm_thread_start loc p t (get_et e)].

Definition wait_par_thread (loc:Loc) (t:Core_Term) (e:EvC) : CVM EvC :=
  p <- get_pl ;;
  e' <- do_wait_par_thread loc t p e ;;
  add_tracem [cvm_thread_end loc] ;;
  inc_par_event_ids t ;;
  ret e'.
   
Ltac monad_unfold :=
  repeat unfold
  execErr,  
  do_prim,
  invoke_ASP,
  fwd_asp,
  extd_bundle,
  comp_bundle,
  encr_bundle,
  do_asp,
  clearEv,
  copyEv,
  
  get_ev,
  get_pl,
  get_CVM_amConfig,
  add_tracem,
  modify_evm,
  add_trace,
  failm,
  get,
  when,
  put,
  nop,
  modify,
  bind,
  ret in * ;
  simpl in * .

(* Grouping together some common hypothesis normalizations.  Inverting pairs of
   Some values, cvm_st equivalences, etc. *)
Ltac pairs :=
  simpl in *;
  vmsts;
  repeat
    match goal with
    | [H: (Some _, _) =
          (Some _, _) |- _ ] => invc H; monad_unfold
                                                          
    | [H: {| st_ev := _; st_trace := _; st_evid := _; st_AM_config := _ |} =
          {| st_ev := _; st_trace := _; st_evid := _; st_AM_config := _ |} |- _ ] =>
      invc H; monad_unfold
    end; destruct_conjs; monad_unfold.

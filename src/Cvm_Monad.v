(*
Definition of the CVM Monad + monadic helper functions.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Term ConcreteEvidence Axioms_Io Evidence_Bundlers Defs.
Require Import StructTactics.

Require Import Coq.Program.Tactics Lia.

Require Import Manifest_Admits ErrorStringConstants.

Require Import List.
Import ListNotations.

Require Export Cvm_St ErrorStMonad_Coq IO_Stubs.


(** * CVM monadic primitive operations *)

Definition put_ev (e:EvC) : CVM unit :=
  st <- (@get cvm_st CVM_Error) ;;
     let tr' := st_trace st in
     let p' := st_pl st in
     let i := st_evid st in
     let ac := st_AM_config st in
     (@put cvm_st CVM_Error) (mk_st e tr' p' i ac).

Definition put_pl (p:Plc) : CVM unit :=
  st <- (@get cvm_st CVM_Error) ;;
     let tr' := st_trace st in
     let e' := st_ev st in
     let i := st_evid st in
     let ac := st_AM_config st in
     (@put cvm_st CVM_Error) (mk_st e' tr' p i ac).

Definition get_ev : CVM EvC :=
  @bind cvm_st cvm_st EvC CVM_Error (@get cvm_st CVM_Error) (fun st => (ret (st_ev st))).
  (*
  st <- (@get cvm_st CVM_Error) ;;
  ret (st_ev st).
  *)
Check get_ev.

Definition get_pl : CVM Plc :=
  st <- (@get cvm_st CVM_Error) ;;
  ret (st_pl st).



Definition get_amConfig : CVM AM_Config :=
  (* TODO:  consider moving this functionality to a Reader-like monad 
        i.e. an 'ask' primitive *)
  st <- (@get cvm_st CVM_Error) ;;
  ret (st_AM_config st).

Definition inc_id : CVM Event_ID :=
  st <- (@get cvm_st CVM_Error) ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let p' := st_pl st in
    let i := st_evid st in
    let ac := st_AM_config st in
    (@put cvm_st CVM_Error) (mk_st e' tr' p' (Nat.add i (S O)) ac) ;;
    ret i.

Definition modify_evm (f:EvC -> EvC) : CVM unit :=
  st <- (@get cvm_st CVM_Error) ;;
  let '{| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |} := st in
  (@put cvm_st CVM_Error) (mk_st (f e) tr p i ac).

Definition add_trace (tr':list Ev) : cvm_st -> cvm_st :=
  fun '{| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |} =>
    mk_st e (tr ++ tr') p i ac.

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
Definition fwd_asp (fwd:FWD) (bs:BS) (e:EvC) (p:Plc) (ps:ASP_PARAMS): EvC :=
  match fwd with
  | COMP => cons_hsh bs e p ps
  | EXTD => cons_gg bs e p ps
  | ENCR => cons_enc bs e p ps
  | KILL => mt_evc
  | KEEP => e
  end.

Definition do_asp' (params :ASP_PARAMS) (e:RawEv) (mpl:Plc) (x:Event_ID) : CVM BS :=
  ac <- get_amConfig  ;;
  (*
  st <- (@get cvm_st CVM_Error) ;;
  let ac := (st_AM_config st) in
  *)
  match (do_asp params e mpl x ac) with
  | resultC r => ret r
  | errC e => failm (dispatch_error e)
  end.

(* Simulates invoking an arbitrary ASP.  Tags the event, builds and returns 
   the new evidence bundle. *)
Definition invoke_ASP (fwd:FWD) (params:ASP_PARAMS) (* (ac : AM_Config) *) : CVM EvC :=
  e <- get_ev ;;
  p <- get_pl ;;
  x <- tag_ASP params p e ;;
  bs <- do_asp' params (get_bits e) p x ;;
  ret (fwd_asp fwd bs e p params).

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
  st <- (@get cvm_st CVM_Error) ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let p' := st_pl st in
    let i := st_evid st in
    let new_i := Nat.add i (event_id_span' t) in
    let ac := st_AM_config st in
    (@put cvm_st CVM_Error) (mk_st e' tr' p' new_i ac).

(* Monadic helper function to simulate a span of parallel event IDs 
   corresponding to the size of a Core_Term *)
Definition inc_par_event_ids (t:Core_Term) : CVM unit :=
  st <- (@get cvm_st CVM_Error) ;;
    let tr' := st_trace st in
    let e' := st_ev st in
    let p' := st_pl st in
    let i := st_evid st in
    let new_i := Nat.add i (event_id_span t) in
    let ac := st_AM_config st in
    (@put cvm_st CVM_Error) (mk_st e' tr' p' new_i ac).
  
(* Primitive monadic communication primitives 
   (some rely on Admitted IO Stubs). *)

Definition tag_REQ (t:Term) (p:Plc) (q:Plc) (e:EvC) : CVM unit :=
  reqi <- inc_id ;;
  add_tracem [req reqi p q t (get_et e)].

Definition tag_RPY (p:Plc) (q:Plc) (e:EvC) : CVM unit :=
  rpyi <- inc_id ;;
  add_tracem [rpy rpyi p q (get_et e)].

Definition get_cvm_policy : CVM PolicyT := 
  ac <- get_amConfig ;;
  (*
  st <- (@get cvm_st CVM_Error) ;;
  let ac := (st_AM_config st) in *)
  ret (policy (absMan ac)).

Definition check_cvm_policy (t:Term) (pTo:Plc) (et:Evidence) : CVM unit := 
  pol <- get_cvm_policy ;;
    match (policy_list_not_disclosed t pTo et pol) with
    | true => ret tt
    | false => failm (dispatch_error (Runtime errStr_privPolicy))
    end.

Definition doRemote_session' (t:Term) (pTo:Plc) (e:EvC) : CVM EvC := 
  check_cvm_policy t pTo (get_et e) ;;
  ac <- get_amConfig ;;
  (*
  st <- (@get cvm_st CVM_Error) ;;
  let ac := (st_AM_config st) in
  *)
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
  do_asp',
  do_asp,
  clearEv,
  copyEv,
  
  doRemote,

  get_ev,
  get_pl,
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
                                                          
    | [H: {| st_ev := _; st_trace := _; st_pl := _(*; st_store := _*); st_evid := _ |} =
          {| st_ev := _; st_trace := _; st_pl := _ (*; st_store := _*); st_evid := _ |} |- _ ] =>
      invc H; monad_unfold
    end; destruct_conjs; monad_unfold.

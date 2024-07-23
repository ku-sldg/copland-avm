(* Monadic helpers and custom automation for the AM Monad (AM) *)
Require Import List String.

Require Import ErrorStMonad_Coq BS Maps Term_Defs_Core Term_Defs Cvm_Run Cvm_St.

Require Import ErrorStringConstants Appraisal_IO_Stubs Attestation_Session.

Require Export AM_St.

Import ListNotations.

Definition am_error_to_string (err:AM_Error) : string :=
  match err with 
  | am_error s => s
  | am_dispatch_error e => errStr_dispatch_error
  | cvm_error e => errStr_cvm_error
  end.

Definition fromSome{A E:Type} (default:A) (opt:ResultT A E): A :=
  match opt with
  | resultC x => x
  | _ => default
  end.

(* Definition run_am_app_comp_with_default{A:Type} (am_comp:AM A) (default_A:A) (b:bool): A :=
  if (b) 
  then (
  let optRes := evalErr am_comp empty_amst in
  let v := 
    match optRes with 
    | resultC _ => (negb b)
    | errC e => print_am_error e b
    end in 
  if(v)
  then 
  (default_A)
  else 
  (fromSome default_A optRes)
  ) 
  else 
  (default_A). *)

Definition run_am_app_comp_init_with_default{A:Type} (am_comp:AM A) (st:AM_St) (default_A:A) (b:bool): A :=
  if (b) 
  then (
  let optRes := evalErr am_comp st in
  let v := 
    match optRes with 
    | resultC _ => (negb b)
    | errC e => print_am_error e b
    end in 
  if(v)
  then 
  (default_A)
  else 
  (fromSome default_A optRes)
  ) 
  else 
  (default_A).

Definition run_am_app_comp_init {A:Type} (am_comp:AM A) (st:AM_St) : ResultT A string :=
  match (fst (am_comp st)) with
  | resultC x => resultC x
  | errC e => errC (am_error_to_string e)
  end.

Definition get_AM_config : AM Session_Config :=
    (* TODO:  consider moving this functionality to a Reader-like monad 
          i.e. an 'ask' primitive *)
    st <- get ;;
    ret (am_config st).

Definition am_newNonce (bs:BS) : AM nat :=
  oldSt <- get ;;
  let oldMap := am_nonceMap oldSt in
  let oldId := am_nonceId oldSt in
  let oldAMConfig := am_config oldSt in
  let newMap := map_set oldMap oldId bs in
  let newId := oldId + 1 in
  put (mkAM_St newMap newId oldAMConfig) ;;
  ret oldId.

Definition am_getNonce (nid:nat) : AM BS :=
  oldSt <- get ;;
  let oldMap := am_nonceMap oldSt in
  let resopt := map_get oldMap nid in
  match resopt with
  | Some res => ret res
  | None => am_failm (am_error errStr_amNonce)
  end.


Definition am_runCvm_nonce (t:Term) (bs:BS) (ac : Session_Config) : AM (nat * RawEv) :=
  nid <- am_newNonce bs ;;
  match run_cvm_w_config t [bs] ac with
  | resultC res_st => ret (nid, (get_bits (st_ev res_st)))
  | errC e => am_failm (cvm_error e)
  end.

  Ltac am_monad_unfold :=
    repeat unfold
    get_AM_config,
    am_newNonce,
    am_getNonce,
  

    am_failm,
    get,
    when,
    put,
    nop,
    modify,
    bind,
    ret in * ;
    simpl in * .
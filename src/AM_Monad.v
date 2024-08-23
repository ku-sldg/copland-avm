(* Monadic helpers and custom automation for the AM Monad (AM) *)
Require Import List String.

Require Import ErrorStMonad_Coq Maps Term_Defs Cvm_Run Cvm_St Cvm_Monad.

Require Import ErrorStringConstants Attestation_Session.

Require Export AM_St.

Import ListNotations.

Definition am_error_to_string (err:AM_Error) : string :=
  match err with 
  | am_error s => s
  | am_dispatch_error e => errStr_dispatch_error
  | cvm_error e => errStr_cvm_error
  end.

Definition run_am_app_comp_init {A:Type} (am_comp:AM A) (st:AM_St) : ResultT A string :=
  match (fst (am_comp st)) with
  | resultC x => resultC x
  | errC e => errC (am_error_to_string e)
  end.

Import ErrNotation.

Definition get_AM_config : AM Session_Config :=
    (* TODO:  consider moving this functionality to a Reader-like monad 
          i.e. an 'ask' primitive *)
    st <- err_get ;;
    err_ret (am_config st).

Definition am_newNonce (bs:BS) : AM nat :=
  oldSt <- err_get ;;
  let oldMap := am_nonceMap oldSt in
  let oldId := am_nonceId oldSt in
  let oldAMConfig := am_config oldSt in
  let newMap := map_set oldMap oldId bs in
  let newId := oldId + 1 in
  err_put (mkAM_St newMap newId oldAMConfig) ;;
  err_ret oldId.

Definition am_getNonce (nid:nat) : AM BS :=
  oldSt <- err_get ;;
  let oldMap := am_nonceMap oldSt in
  let resopt := map_get oldMap nid in
  match resopt with
  | Some res => err_ret res
  | None => am_failm (am_error errStr_amNonce)
  end.


Ltac am_monad_unfold :=
  repeat 
    (repeat unfold
      get_AM_config,
      am_newNonce,
      am_getNonce,
      am_failm in *; 
    repeat cvm_monad_unfold;
    simpl in *).
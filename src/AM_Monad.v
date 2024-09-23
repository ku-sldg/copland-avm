(* Monadic helpers and custom automation for the AM Monad (AM) *)
Require Import List String.

Require Import ErrorStMonad_Coq Maps Term_Defs Cvm_St Cvm_Monad.

Require Import ErrorStringConstants Attestation_Session.

Require Export AM_St.

Import ListNotations.

Definition am_error_to_string (err:AM_Error) : string :=
  match err with 
  | am_error s => s
  | am_dispatch_error e => errStr_dispatch_error
  | cvm_error e => errStr_cvm_error
  end.

Definition run_am_app_comp_init {A:Type} (am_comp:AM A) (st:AM_St) 
    (sc : Session_Config) : ResultT A string :=
  match (fst (fst (am_comp st sc))) with
  | resultC x => resultC x
  | errC e => errC (am_error_to_string e)
  end.

Import ErrNotation.

Definition get_AM_config : AM Session_Config :=
  err_get_config.

Definition am_newNonce (bs:BS) : AM nat :=
  oldSt <- err_get_state ;;
  let oldMap := am_nonceMap oldSt in
  let oldId := am_nonceId oldSt in
  sc <- get_AM_config ;;
  let newMap := map_set oldId bs oldMap in
  let newId := oldId + 1 in
  err_put_state (mkAM_St newMap newId) ;;
  err_ret oldId.

Definition am_getNonce (nid:nat) : AM BS :=
  oldSt <- err_get_state ;;
  let oldMap := am_nonceMap oldSt in
  let resopt := map_get nid oldMap in
  match resopt with
  | Some res => err_ret res
  | None => am_failm (am_error err_str_am_nonce)
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
Require Import StMonad_Coq AM_St BS Maps Term_Defs_Core Term_Defs Cvm_Run.

Require Import List.
Import ListNotations.



Definition AM := St AM_St.

Definition fromSome{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.

Definition run_am_app_comp{A:Type} (am_comp:AM A) (default_A:A) : A :=
  let optRes := evalSt am_comp empty_amst in
  fromSome default_A optRes.

Definition am_newNonce (bs:BS) : AM nat :=
  oldSt <- get ;;
  let oldMap := am_nonceMap oldSt in
  let oldId := am_nonceId oldSt in
  let newMap := map_set oldMap oldId bs in
  let newId := oldId + 1 in
  put (mkAM_St newMap newId) ;;
  ret oldId.

Check map_get.

Definition am_getNonce (nid:nat) : AM BS :=
  oldSt <- get ;;
  let oldMap := am_nonceMap oldSt in
  let resopt := map_get oldMap nid in
  match resopt with
  | Some res => ret res
  | None => failm
  end.


Definition am_runCvm_nonce (t:Term) (p:Plc) (bs:BS) : AM (nat * RawEv) :=
  nid <- am_newNonce bs ;;
  ret (nid, run_cvm_rawEv t p [bs]).

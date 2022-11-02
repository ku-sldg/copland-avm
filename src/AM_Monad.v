Require Import StMonad_Coq AM_St BS Maps Term_Defs_Core Term_Defs Cvm_Run.

Require Import List.
Import ListNotations.



Definition AM := St AM_St.

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

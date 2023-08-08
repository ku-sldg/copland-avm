Require Import Term_Defs_Core Term_Defs. (* OptMonad_Coq. *)

Require Import Appraisal_IO_Stubs ErrorStMonad_Coq AM_Monad.

(*
Definition checkASP (params:ASP_PARAMS) (bs:BS) : Opt BS :=
  Some (checkASP' params bs).
*)

(*
Definition checkHH (params:ASP_PARAMS) (bs:BS) (e:Evidence) : Opt BS :=
  Some (checkHH' params bs e).
*)

(*
Definition checkEE (params:ASP_PARAMS) (bs:BS) : Opt BS := 
Some (checkEE' params bs).
*)

Definition decrypt_bs_to_rawev' (bs:BS) (params:ASP_PARAMS) : AM RawEv :=
  ret (decrypt_bs_to_rawev bs params).

Definition check_asp_EXTD' (params:ASP_PARAMS) (p:Plc) (sig:BS) (ls:RawEv) : AM BS :=
  ret (check_asp_EXTD params p sig ls).

Definition checkNonce' (nid:nat) (nonceCandidate:BS) : AM BS :=
  nonceGolden <- am_getNonce nid ;;
  ret (checkNonce nonceGolden nonceCandidate).

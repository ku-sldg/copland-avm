Require Import Term_Defs_Core Term_Defs Manifest. (* OptMonad_Coq. *)

Require Import Appraisal_IO_Stubs ErrorStMonad_Coq AM_Monad AM_St.

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

Definition check_asp_EXTD (params:ASP_PARAMS) (p:Plc) (sig:BS) (ls:RawEv) (ac : AM_Config) : ResultT BS DispatcherErrors :=
  ac.(app_aspCb) params p sig ls.

Definition check_asp_EXTD' (params:ASP_PARAMS) (p:Plc) (sig:BS) (ls:RawEv) : AM BS :=
  ac <- get_amConfig ;;
  match (check_asp_EXTD params p sig ls ac) with
  | resultC r => ret r
  | errC e => failm (dispatch_error e)
  end.

Definition checkNonce' (nid:nat) (nonceCandidate:BS) : AM BS :=
  nonceGolden <- am_getNonce nid ;;
  ret (checkNonce nonceGolden nonceCandidate).

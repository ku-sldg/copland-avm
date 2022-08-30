Require Import Term_Defs_Core Term_Defs OptMonad_Coq.

Require Import Appraisal_IO_Stubs_New.

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

Definition decrypt_bs_to_rawev (bs:BS) (params:ASP_PARAMS) : Opt RawEv :=
  Some (decrypt_bs_to_rawev' bs params).

Definition checkGG (params:ASP_PARAMS) (p:Plc) (sig:BS) (ls:RawEv) : Opt BS :=
  Some (checkGG' params p sig ls).

Definition checkNonce (nonceGolden:BS) (nonceCandidate:BS) : Opt BS :=
  Some (checkNonce' nonceGolden nonceCandidate).

Require Import AM_Monad Impl_appraisal StMonad_Coq Term_Defs_Core Term Cvm_Run IO_Stubs.

Require Import Example_Phrases_Demo Example_Phrases_Demo_Admits.

Require Import Client_AM Server_AM.

Require Import List.
Import ListNotations.


(* AM Monad "run" functions for Copland Client *)

Definition run_am_sendReq_nonce (t:Term) (pFrom:Plc) (pTo:Plc) : AppResultC :=
  let am_comp := am_sendReq_nonce t pFrom pTo in
  (run_am_app_comp am_comp mtc_app).

Definition run_am_sendReq_nonce_auth (t:Term) (pFrom:Plc) (pTo:Plc) : AppResultC :=
  let am_comp := am_sendReq_nonce_auth t pFrom pTo in
  (run_am_app_comp am_comp mtc_app).


(* AM Monad "run" functions for Copland Server *)

Definition run_am_serve_auth_tok_req (t:Term) (fromPl:Plc) (myPl:Plc) (authTok:ReqAuthTok) (init_ev:RawEv) : RawEv :=
  run_am_app_comp (am_serve_auth_tok_req t fromPl myPl authTok init_ev) [].




(* Top-level functions for Copland Client *)

(* dest_plc = 0, source_plc = 3 *)
Definition client_demo_am_comp (t:Term) : AppResultC :=
  run_am_sendReq_nonce t dest_plc source_plc.

Definition client_demo_am_comp_auth (t:Term) : AppResultC :=
  run_am_sendReq_nonce_auth t dest_plc source_plc.

Require Import AM_Monad Impl_appraisal StMonad_Coq Term_Defs_Core Term Cvm_Run IO_Stubs.

Require Import Example_Phrases_Demo Example_Phrases_Demo_Admits.

Require Import List.
Import ListNotations.


Definition am_sendReq_auth (t:Term) (pFrom:Plc) (pTo:Plc) (initEv:RawEv) (* (et:Evidence) *) : AM RawEv :=
  let auth_phrase := ssl_sig in
  let auth_rawev := run_cvm_rawEv auth_phrase pFrom [] in
  let et := eval auth_phrase pFrom mt in
  let resev := am_sendReq t pFrom pTo et (auth_rawev ++ initEv) in
  ret resev.

Definition client_demo_am_comp (t:Term) : AM bool :=
  let app_res := run_am_sendReq_nonce_auth t dest_plc source_plc in
  let bool_res :=
      match app_res with
      | (ggc_app _ _ kimcheckres _) => true
      | _ => false (* default_bs *)
      end in
        (*
  let bool_res :=
      match kimcheckres with
      | _ => true
      end in *)
      (*
      match app_res with
      | eec_app _ _ _
                (ggc_app _ _ sigcheckres
                         (ggc_app _ _ _
                                  (ggc_app _ _ kimcheckres _))) =>
        true
      | _ => false
      end in
       *)

  
      
  if bool_res then
    (* (am_sendReq_auth client_data_phrase dest_plc source_plc [kimcheckres]) ;; *)
    ret bool_res
    (*ret tt *)
  else
    ret false.

Definition run_client_demo_am_comp (t:Term) : bool :=
  run_am_app_comp (client_demo_am_comp t) false.

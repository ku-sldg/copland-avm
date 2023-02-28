Require Import AM_Monad Impl_appraisal StMonad_Coq Term_Defs_Core Term Cvm_Run IO_Stubs.

Require Import Example_Phrases_Demo Example_Phrases_Demo_Admits.

Require Import List.
Import ListNotations.


(* dest_plc = 0, source_plc = 3 *)
Definition client_demo_am_comp (t:Term) : AppResultC :=
  (*
  run_am_sendReq_nonce_auth t dest_plc source_plc. 
   *)
  run_am_sendReq_nonce t dest_plc source_plc.

Definition client_demo_am_comp_auth (t:Term) : AppResultC :=
  (*
  run_am_sendReq_nonce_auth t dest_plc source_plc. 
   *)
  run_am_sendReq_nonce_auth t dest_plc source_plc.



(*





  (*
  let app_res := run_am_sendReq_nonce_auth t dest_plc (* 0 *) source_plc (* 1 *) in
  let bool_res := appres_size_lt_zero app_res in
   *)
  

(*
  
      match app_res with
      | (ggc_app _ _ kimcheckres _) => true
      | _ => false (* default_bs *)
      end in

*)


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

*)



(* 
Definition run_client_demo_am_comp (t:Term) : AppResultC :=
  run_am_app_comp (client_demo_am_comp t) mtc_app.
*)

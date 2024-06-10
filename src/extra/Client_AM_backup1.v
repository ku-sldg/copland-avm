Require Import Term Example_Phrases_Demo Cvm_Run Manifest.

Require Import Impl_appraisal Appraisal_IO_Stubs IO_Stubs AM_Monad ErrorStMonad_Coq.

Require Import CvmJson_Interfaces.
Require Import List.
Import ListNotations.

Definition gen_nonce_if_none (initEv:option EvC) : AM EvC :=
  match initEv with
      | Some (evc ebits et) => ret (evc ebits et)
      | None =>
        let nonce_bits := gen_nonce_bits in
        nid <- am_newNonce nonce_bits ;;
        ret (evc [nonce_bits] (nn nid))
  end.

Definition gen_authEvC_if_some (ot:option Term) (myPlc:Plc) (init_evc:EvC) : AM EvC :=
  match ot with
  | Some auth_phrase =>
    let '(evc init_rawev_auth init_et_auth) := init_evc in
    let auth_rawev := am_sendReq auth_phrase myPlc mt_evc init_rawev_auth in
                        (* run_cvm_rawEv auth_phrase pFrom [] *)
    let auth_et := eval auth_phrase myPlc init_et_auth in
      ret (evc auth_rawev auth_et)
  | None => ret (evc [] mt)
  end.

Definition am_appraise (t:Term) (toPlc:Plc) (init_et:Evidence) (cvm_ev:RawEv) : AM AppResultC :=
  (* let app_res := run_appraisal_client t pTo init_et cvm_ev in *)
  let expected_et := eval t toPlc init_et in
  app_res <- gen_appraise_AM expected_et cvm_ev ;;
  ret (app_res).


Definition am_client_gen (t:Term) (myPlc:Plc) (pTo:Plc) (initEvOpt:option EvC) 
    (authPhrase:option Term) (app_bool:bool) : AM AM_Result :=
evcIn <- gen_nonce_if_none initEvOpt ;;
auth_evc <- gen_authEvC_if_some authPhrase myPlc mt_evc  ;;
let '(evc init_ev init_et) := evcIn in
let resev := am_sendReq t pTo auth_evc init_ev in 
match app_bool with
| true =>  
  app_res <- am_appraise t pTo init_et resev ;; 
  ret (am_appev app_res)
| false => ret (am_rawev resev)
end.

Definition am_client_auth (t:Term) (myPlc:Plc) (pTo:Plc) 
    (authPhrase:Term) (nonceB:bool) (appraiseB:bool) : AM AM_Result :=
    let init_evc_opt := (if(nonceB) then None else (Some mt_evc)) in
      am_client_gen t myPlc pTo init_evc_opt (Some authPhrase) appraiseB.

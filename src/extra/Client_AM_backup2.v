Require Import Term Example_Phrases_Demo Cvm_Run Manifest.

Require Import Impl_appraisal Appraisal_IO_Stubs IO_Stubs AM_Monad StMonad_Coq.

Require Import CvmJson_Interfaces.
Require Import List.
Import ListNotations.

Definition gen_nonce_if_none (initEv:option EvC) : AM EvC :=
  match initEv with
      | Some (evc ebits et) => ret (evc ebits et)
      | None =>
        let nonce_bits := gen_nonce_bits in
        nid <- am_newNonce nonce_bits ;;
        ret (evc [nonce_bits] (nonce_evt nid))
  end.

Definition gen_authEvC_if_some (ot:option Term) (pFrom:Plc) : AM EvC :=
  match ot with
  | Some auth_phrase =>
    let auth_rawev := run_cvm_rawEv auth_phrase pFrom [] in
    let auth_et := eval auth_phrase pFrom mt_evtin
    ret (evc auth_rawev auth_et)
  | None => ret (evc [] mt_evt)
  end.

Definition run_appraisal_client (t:Term) (p:Plc) (e:EvidenceT) (re:RawEv) : AppResultC :=
    let expected_et := eval t p e in 
    let comp := gen_appraise_AM expected_et re in
    run_am_app_comp comp mtc_app.

Definition am_sendReq_gen (t:Term) (pFrom:Plc) (pTo:Plc)
  (initEv:option EvC) (authPhrase:option Term) 
  (* (plcCb : CakeML_PlcCallback) *) (app_bool:bool) : AM AM_Result :=
evcIn <- gen_nonce_if_none initEv ;;
auth_evc <- gen_authEvC_if_some authPhrase pFrom  ;;
let '(evc init_ev init_et) := evcIn in
(* let targetUUID := plcCb pTo in *)
let resev := am_sendReq t pTo(*targetUUID*) auth_evc init_ev in 
(*
let resev := run_cvm_rawEv t pFrom init_ev in *)
match app_bool with
| true => 
(*
let expected_et := eval t pTo init_et in *)
let app_res := run_appraisal_client t pTo init_et resev in
(* app_res <- gen_appraise_AM expected_et resev ;; *)
 ret (am_appev app_res)
| false => ret (am_rawev resev)
end.
  




(*
Definition am_sendReq_gen (t:Term) (pFrom:Plc) (pTo:Plc)
           (initEv:option EvC) (authPhrase:option Term) 
           (plcCb : CakeML_PlcCallback) (app_bool:bool) : AM AM_Result :=
  evcIn <- gen_nonce_if_none initEv ;;
  auth_evc <- gen_authEvC_if_some authPhrase pFrom  ;;
  let '(evc init_ev init_et) := evcIn in
  let targetUUID := plcCb pTo in
  let resev := am_sendReq t targetUUID auth_evc init_ev in
    match app_bool with
    | true => 
        let expected_et := eval t pTo init_et in
        app_res <- gen_appraise_AM expected_et resev ;;
          ret (am_appev app_res)
    | false => ret (am_rawev resev)
    end.
    *)

Definition am_sendReq_dispatch (maybeAuthTerm : option Term) (nonceB:bool) (t : Term) 
                               (source : Plc) (dest : Plc) (app_bool:bool)
                               (* (plcCb : CakeML_PlcCallback) *) : AM AM_Result :=
  let nonce_param := 
    if(nonceB) 
    then None 
    else (Some (evc [] mt_evt)) in
    am_sendReq_gen t source dest nonce_param maybeAuthTerm (*plcCb*) app_bool.


Definition am_sendReq_dispatch_default_auth (t : Term) (source : Plc) (dest : Plc) 
    (* (plcCb : CakeML_PlcCallback) *) (auth : bool) (app_bool:bool) : AM AM_Result :=
    let auth_term := (ssl_sig_parameterized source) in
      let auth_param := 
       if(auth)
       then (Some auth_term)
       else None in
          am_sendReq_dispatch auth_param true t source dest app_bool (*plcCb*) .




Definition am_client_auth_tok_req (t:Term) (myPl:Plc) (init_ev:RawEv) 
                                  (app_bool:bool): AM AM_Result :=
  let auth_tok := mt_evc in 
  let att_res := am_sendReq t myPl auth_tok init_ev (* run_cvm_json_full t init_ev *) (* run_cvm_rawEv t myPl init_ev *) in
  match app_bool with
  | true => 
  let app_res := am_sendReq_app t myPl mt_evtatt_res in 
  ret (am_appev app_res)

  (*
  let att_et := eval t myPl mt_evtin
  app_res <- gen_appraise_AM att_et att_res ;;
  ret (am_appev app_res)
  *)
  | false => ret (am_rawev att_res)
  end.

(*
Definition am_client_auth_tok_req (t:Term) (myPl:Plc) (init_ev:RawEv) (app_bool:bool): AM AppResultC :=
match app_bool with
| true => 
v <- am_check_auth_tok t myPl mt_evc ;;
match (andb (requester_bound t myPl mt_evc) (appraise_auth_tok v)) with
| true =>
match (privPolicy myPl t) with
| true =>
let att_res := run_cvm_rawEv t myPl init_ev in
let att_et := eval t myPl mt_evtin
gen_appraise_AM att_et att_res
| false => failm
end

| false => failm
end
| false => ret mtc_app
end.
*)









(*
Definition am_sendReq_nonce (t:Term) (pFrom:Plc) (pTo:Plc) (plcCb : CakeML_PlcCallback) : AM AppResultC :=
  am_sendReq_gen t pFrom pTo None None plcCb.
  *)

(*
Definition am_sendReq_nonce_auth (t:Term) (pFrom:Plc) (pTo:Plc) (plcCb : CakeML_PlcCallback): AM AppResultC :=
  let auth_phrase := (* kim_meas *) ssl_sig in
  am_sendReq_gen t pFrom pTo None (Some auth_phrase) plcCb.
  *)
  

(*
Definition am_sendReq_auth (t:Term) (pFrom:Plc) (pTo:Plc) (initEv:RawEv) 
                           (plcCb : CakeML_PlcCallback) : AM AM_Result :=
  let auth_phrase := (* kim_meas *) ssl_sig in
  let initEv_et := mt_evtin (* TODO:  make this a param? *)
  am_sendReq_gen t pFrom pTo (Some (evc initEv initEv_et)) (Some auth_phrase) plcCb.
*)

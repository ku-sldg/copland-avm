Require Import List.
Import ListNotations.
Require Import BS Manifest Term_Defs CvmJson_Interfaces String IO_Stubs Manifest_Admits ErrorStMonad_Coq AM_Monad.
Require Import ErrorStringConstants AM_Helpers Impl_appraisal Cvm_Run.

Definition am_check_auth_tok (t:Term) (fromPl:Plc) (authTok:ReqAuthTok) 
    : AM AppResultC :=
  match authTok with
  | evc auth_ev auth_et => 
    appres <-
    (match (requester_bound t fromPl authTok) with
     | false => am_failm (am_error errStr_requester_bound)
     | true => gen_appraise_AM auth_et auth_ev
     end) ;;
    ret appres
  end.

Definition am_serve_auth_tok_req (t:Term) (fromPl : Plc) 
                                 (authTok:ReqAuthTok) (init_ev:RawEv) (ac : AM_Config) (al:AM_Library) : AM RawEv :=
  let test_print := print_auth_tok authTok in
  v <- am_check_auth_tok t fromPl authTok ;;
  match ((appraise_auth_tok v)) with
  | true =>

    config_AM_if_lib_supported (absMan ac) al ;; 
  
    (*
    check_disclosure_policy t myPlc init_et ;;
    (* TODO: decide how to get initial Evidence type here for server AMs...  *)
    *)
    
    ret (run_cvm_rawEv t init_ev ac)
    (*
    | false => am_failm (am_error errStr_disclosePolicy)
    end *)
      
  | false => am_failm (am_error errStr_app_auth_tok)
  end.

(* Definition run_am_server_auth_tok_req (t:Term) (fromPlc:Plc) 
            (authTok:ReqAuthTok) (init_ev:RawEv) (ac : AM_Config) (al:AM_Library) : RawEv :=
  run_am_app_comp (am_serve_auth_tok_req t fromPlc authTok init_ev ac al) [] true. *)

Definition do_appraisal_session (appreq:ProtocolAppraiseRequest) (ac:AM_Config) (nonceVal:BS): ProtocolAppraiseResponse :=
  let '(mkPAReq t p et ev) := appreq in
  let expected_et := eval t p et in 
  let comp := gen_appraise_AM expected_et ev in 
  let init_noncemap := [(O, nonceVal)] in
  let init_nonceid := (S O) in
  let my_amst := (mkAM_St init_noncemap init_nonceid ac) in
  let appres := run_am_app_comp_init comp my_amst mtc_app true in
    mkPAResp true appres.

Definition handle_AM_request_Json (js : Json) (ac : AM_Config) (al:AM_Library) (nonceVal:BS) : Json :=
  match Json_to_AM_Protocol_Request js with 
  | None => ErrorResponseJson "Invalid Request Format"
  | Some (Protocol_Run_Request r) => 
    let '(mkPRReq from_plc cop_term tok ev) := r in
    let my_plc := (my_abstract_plc (absMan ac)) in
    let test_print := print_auth_tok tok in
    (* NOTE: Skipping auth tok checking for now, not sure how it should work *)
    (* v <- am_check_auth_tok cop_term from_plc tok ;;
    match (appraise_auth_tok v) with
    | true => 
      let asdf := config_AM_if_lib_supported (absMan ac) al in
      let resev := run_cvm_rawEv cop_term ev ac in
      ProtocolRunResponse_to_Json (mkPRResp true resev)
    | false => ErrorResponseJson "Appraisal failed"
    end *)
    let cvm_resp := (run_cvm_rawEv cop_term ev ac) in
      ProtocolRunResponse_to_Json (mkPRResp true cvm_resp)

  | Some (Protocol_Appraise_Request appreq) => 
    let app_resp := (do_appraisal_session appreq ac nonceVal) in 
      ProtocolAppraiseResponse_to_Json app_resp

  | Some (Protocol_Negotiate_Request r) => 
    (* TODO: Fill this in when negotiation is implemented *)
    ErrorResponseJson "Negotiation not implemented yet"
  end.

Definition make_AM_Protocol_Run_request_json 
    (t:Term) (targ_uuid : UUID) (tok:ReqAuthTok) (ev:RawEv) (from_plc : Plc)
    : option RawEv :=
  let req := (mkPRReq from_plc t tok ev) in
  let js_req := ProtocolRunRequest_to_Json req in
  let js_resp := make_JSON_Request targ_uuid js_req in
  match Json_to_AM_Protocol_Response js_resp with
  | Some (Protocol_Run_Response prresp) => 
    let '(mkPRResp success ev) := prresp in
    if success 
    then Some ev 
    else None
  | _ => None
  end.
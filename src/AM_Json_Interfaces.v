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
(* 
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
  end. *)

Definition do_appraisal_session (appreq:ProtocolAppraiseRequest) (ac:AM_Config) (nonceVal:BS): ResultT ProtocolAppraiseResponse string :=
  let '(mkPAReq t p et ev) := appreq in
  let expected_et := eval t p et in 
  let app_am := gen_appraise_AM expected_et ev in 
  let init_noncemap := [(O, nonceVal)] in
  let init_nonceid := (S O) in
  let my_amst := (mkAM_St init_noncemap init_nonceid ac) in
  match run_am_app_comp_init app_am my_amst with
  | errC e => errC e
  | resultC appres =>
      resultC (mkPAResp true appres)
  end.

Definition handle_AM_request_JSON (js : JSON) (ac : AM_Config) (nonceVal:BS) : JSON :=
  match JSON_to_AM_Protocol_Request js with 
  | errC msg => ErrorResponseJSON msg
  | resultC (Protocol_Run_Request r) => 
    let '(mkPRReq cop_term from_plc ev) := r in
    let my_plc := (my_abstract_plc (absMan ac)) in
    (* NOTE: Skipping auth tok checking for now, not sure how it should work *)
    (* v <- am_check_auth_tok cop_term from_plc tok ;;
    match (appraise_auth_tok v) with
    | true => 
      let asdf := config_AM_if_lib_supported (absMan ac) al in
      let resev := run_cvm_rawEv cop_term ev ac in
      ProtocolRunResponse_to_JSON (mkPRResp true resev)
    | false => ErrorResponseJSON "Appraisal failed"
    end *)
    let cvm_resp := (run_cvm_rawEv cop_term ev ac) in
    match cvm_resp with
    | errC e => ErrorResponseJSON e
    | resultC res_ev => 
        ProtocolRunResponse_to_JSON (mkPRResp true res_ev)
    end

  | resultC (Protocol_Appraise_Request appreq) => 
    let app_resp := (do_appraisal_session appreq ac nonceVal) in 
    match app_resp with
    | errC e => ErrorResponseJSON e
    | resultC app_resp =>
      ProtocolAppraiseResponse_to_JSON app_resp
    end

  | resultC (Protocol_Negotiate_Request r) => 
    (* TODO: Fill this in when negotiation is implemented *)
    ErrorResponseJSON errStr_negotiation_not_implemented
  end.

Definition make_AM_Protocol_Run_request_JSON 
    (t:Term) (targ_uuid : UUID) (tok:ReqAuthTok) (ev:RawEv) (from_plc : Plc)
    : ResultT RawEv string :=
  let req := (mkPRReq t from_plc ev) in
  let js_req := ProtocolRunRequest_to_JSON req in
  let resp_res := make_JSON_Network_Request targ_uuid js_req in
  match resp_res with
  | resultC js_resp =>
      match JSON_to_AM_Protocol_Response js_resp with
      | resultC (Protocol_Run_Response prresp) => 
        let '(mkPRResp success ev) := prresp in
        if success 
        then resultC ev 
        else errC errStr_remote_am_failure
      | errC msg => errC msg
      | _ => errC errStr_invalid_request_type
      end
  | errC msg => errC msg
  end.
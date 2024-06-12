Require Import BS Manifest Term_Defs CvmJson_Interfaces String IO_Stubs Manifest_Admits.

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

Definition handle_AM_request_Json (js : Json) (ac : AM_Config) (al:AM_Library) (nonceVal:BS) : Json :=
  match Json_to_AM_Protocol_Request js with 
  | None => ErrorResponseJson "Invalid Request Format"
  | Some (Protocol_Run_Request req) => 
    let '(mkPRReq from_plc cop_term tok ev) := req in
    let my_plc := (my_abstract_plc (absMan ac)) in
    let test_print := print_auth_tok tok in
    match am_check_auth_tok cop_term from_plc tok with
    | am_res => 
      match appraise_auth_tok am_res with
      | true => 
        let asdf := config_AM_if_lib_supported (absMan ac) al in
        let resev := run_cvm_rawEv cop_term my_plc ev ac in
        ProtocolRunResponse_to_Json (mkPRResp true resev)
      | false => ErrorResponseJson "Appraisal failed"
      end
    end
    let cvm_resp := (do_cvm_session r ac al) in 
      ProtocolRunResponse_to_Json cvm_resp

  | Some (Protocol_Appraise_Request appreq) => 
    let app_resp := (do_appraisal_session appreq ac nonceVal) in 
      ProtocolAppraiseResponse_to_Json app_resp

  | Some (Protocol_Negotiate_Request r) => 
    (* TODO: Fill this in when negotiation is implemented *)
    ErrorResponseJson "Negotiation not implemented yet"
  end.

Definition make_AM_Protocol_Run_request_json 
    (t:Term) (uuid : UUID) (tok:ReqAuthTok) (ev:RawEv) : option RawEv :=
  let req := (mkPRReq t tok ev) in
  let js_req := ProtocolRunRequest_to_Json req in
  let js_resp := make_JSON_Request uuid js_req in
  match Json_to_AM_Protocol_Response js_resp with
  | Some (Protocol_Run_Response prresp) => 
    let '(mkPRResp success ev) := prresp in
    if success 
    then Some ev 
    else None
  | _ => None
  end.
  
  ProtocolRunRequest_to_Json (mkPRReq t tok ev).
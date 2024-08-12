Require Import Interface_Types Stringifiable Attestation_Session Term_Defs.
Require Export JSON List.
Import ListNotations ResultNotation.

(* Protocol Run Request *)
Global Instance Jsonifiable_ProtocolRunRequest `{Jsonifiable Term,
  Jsonifiable RawEv, Jsonifiable Attestation_Session}: Jsonifiable ProtocolRunRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_RUN));
    (STR_ATTEST_SESS, (to_JSON (prreq_att_sess req)));
    (STR_REQ_PLC, (JSON_String (to_string (prreq_req_plc req))));
    (STR_TERM, (to_JSON (prreq_term req))); 
    (STR_RAWEV, (to_JSON (prreq_rawev req)))])
(from_JSON := (fun j =>
  temp_att_sess <- JSON_get_Object STR_ATTEST_SESS j ;;
  temp_term <- JSON_get_Object STR_TERM j ;;
  temp_req_plc <- JSON_get_string STR_REQ_PLC j ;;
  temp_ev <- JSON_get_Object STR_RAWEV j ;;

  att_sess <- from_JSON temp_att_sess ;;
  term <- from_JSON temp_term ;;
  req_plc <- from_string temp_req_plc ;;
  ev <- from_JSON temp_ev ;;
  resultC (mkPRReq att_sess term req_plc ev)));
solve_json.
Defined.

(* Protocol Run Response *)
Global Instance Jsonifiable_ProtocolRunResponse `{Jsonifiable RawEv}: Jsonifiable ProtocolRunResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_RUN));
    (STR_SUCCESS, (JSON_Boolean (prresp_success resp)));
    (STR_PAYLOAD, (to_JSON (prresp_ev resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_ev <- JSON_get_Object STR_PAYLOAD resp ;;

  ev <- from_JSON temp_ev ;;
  resultC (mkPRResp temp_success ev))); solve_json.
Defined.

(* Protocol Negotiate Request *)
Global Instance Jsonifiable_ProtocolNegotiateRequest `{Jsonifiable Term}: Jsonifiable ProtocolNegotiateRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_NEGOTIATE));
    (STR_TERM, (to_JSON (pnreq_term req)))])
(from_JSON := (fun j =>
  temp_term <- JSON_get_Object STR_TERM j ;;

  term <- from_JSON temp_term ;;
  resultC (mkPNReq term))); solve_json.
Defined.

(* Protocol Negotiate Response *)
Global Instance Jsonifiable_ProtocolNegotiateResponse `{Jsonifiable Term}: Jsonifiable ProtocolNegotiateResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_NEGOTIATE));
    (STR_SUCCESS, (JSON_Boolean (pnresp_success resp)));
    (STR_PAYLOAD, (to_JSON (pnresp_term resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_term <- JSON_get_Object STR_PAYLOAD resp ;;

  term <- from_JSON temp_term ;;
  resultC (mkPNResp temp_success term))); solve_json.
Defined.

(* Protocol Appraise Request *)
Global Instance Jsonifiable_ProtocolAppraiseRequest `{Jsonifiable Term, Jsonifiable RawEv, Jsonifiable Evidence, Jsonifiable Attestation_Session}: Jsonifiable ProtocolAppraiseRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object [
    (STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_APPRAISE));
    (STR_ATTEST_SESS, (to_JSON (pareq_att_sess req)));
    (STR_TERM, (to_JSON (pareq_term req)));
    (STR_REQ_PLC, (JSON_String (to_string (pareq_plc req))));
    (STR_EVIDENCE, (to_JSON (pareq_evidence req)));
    (STR_RAWEV, (to_JSON (pareq_ev req)))])
(from_JSON := (fun j =>
  temp_att_sess <- JSON_get_Object STR_ATTEST_SESS j ;;
  temp_term <- JSON_get_Object STR_TERM j ;;
  temp_plc <- JSON_get_string STR_REQ_PLC j ;;
  temp_evidence <- JSON_get_Object STR_EVIDENCE j ;;
  temp_ev <- JSON_get_Object STR_RAWEV j ;;
  
  att_sess <- from_JSON temp_att_sess ;;
  term <- from_JSON temp_term ;;
  plc <- from_string temp_plc ;;
  evidence <- from_JSON temp_evidence ;;
  ev <- from_JSON temp_ev ;;
  resultC (mkPAReq att_sess term plc evidence ev))); solve_json.
Defined.

(* Protocol Appraise Response *)
Global Instance Jsonifiable_ProtocolAppraiseResponse `{Jsonifiable AppResultC}: Jsonifiable ProtocolAppraiseResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object [
    (STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_APPRAISE));
    (STR_SUCCESS, (JSON_Boolean (paresp_success resp)));
    (STR_PAYLOAD, (to_JSON (paresp_result resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_result <- JSON_get_Object STR_PAYLOAD resp ;;

  result <- from_JSON temp_result ;;
  resultC (mkPAResp temp_success result))); solve_json.
Defined.

(* ASP Run Request *)
Global Instance Jsonifiable_ASPRunRequest `{Jsonifiable RawEv, Jsonifiable ASP_ARGS}: Jsonifiable ASPRunRequest.
eapply Build_Jsonifiable with
(to_JSON := fun req =>
  JSON_Object [
    (STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_ASP_RUN));
    (STR_ASP_ID, (JSON_String (to_string (asprreq_asp_id req))));
    (STR_ASP_ARGS, (to_JSON (asprreq_asp_args req)));
    (STR_ASP_PLC, (JSON_String (to_string (asprreq_targ_plc req))));
    (STR_ASP_TARG_ID, (JSON_String (to_string (asprreq_targ req))));
    (STR_RAWEV, (to_JSON (asprreq_rawev req)))])
(from_JSON := (fun j =>
  temp_asp_id <- JSON_get_string STR_ASP_ID j ;;
  temp_asp_args <- JSON_get_Object STR_ASP_ARGS j ;;
  temp_targ_plc <- JSON_get_string STR_ASP_PLC j ;;
  temp_targ <- JSON_get_string STR_ASP_TARG_ID j ;;
  temp_ev <- JSON_get_Object STR_RAWEV j ;;

  asp_id <- from_string temp_asp_id ;;
  asp_args <- from_JSON temp_asp_args ;;
  targ_plc <- from_string temp_targ_plc ;;
  targ <- from_string temp_targ ;;
  ev <- from_JSON temp_ev ;;
  resultC (mkASPRReq asp_id asp_args targ_plc targ ev))); solve_json.
Defined.

(* ASP Run Response *)
Global Instance Jsonifiable_ASPRunResponse `{Jsonifiable RawEv}: Jsonifiable ASPRunResponse.
eapply Build_Jsonifiable with
(to_JSON := fun resp =>
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_ASP_RUN));
    (STR_SUCCESS, (JSON_Boolean (asprresp_success resp)));
    (STR_PAYLOAD, (to_JSON (asprresp_rawev resp)))])
(from_JSON := (fun resp =>
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_rawev <- JSON_get_Object STR_PAYLOAD resp ;;

  rawev <- from_JSON temp_rawev ;;
  resultC (mkASPRResp temp_success rawev))); solve_json.
Defined.

(* Error Response *)
Definition ErrorResponseJSON (msg: string): JSON :=
  JSON_Object 
    [(STR_SUCCESS, JSON_Boolean false);
    (STR_PAYLOAD, (JSON_String msg))].
(* Admitted definitions of JSON types and conversions to/from strings 
    and Copland datatypes at the boundary of AMs.
    
    At the moment, these are too low-level to represent faithfully in the Coq development.   *)

Require Import Term_Defs_Core Term_Defs StringT List JSON Interface_Types ResultT.
Import ListNotations ResultNotation.

(* Protocol Run Section *)
Definition ProtocolRunRequest_to_JSON (req: ProtocolRunRequest): JSON :=
  JSON__Object 
    [(STR_REQ_PLC, (JSON__String (Plc_to_stringT (prreq_req_plc req))));
    (STR_TERM, (JSON__String (Term_to_stringT (prreq_term req)))); 
    (STR_EV, (JSON__String (RawEv_to_stringT (prreq_ev req))))].

Definition JSON_to_ProtocolRunRequest (req : JSON): ResultT ProtocolRunRequest StringT :=
  temp_term <- JSON_get_stringT STR_TERM req ;;
  temp_req_plc <- JSON_get_stringT STR_REQ_PLC req ;;
  temp_ev <- JSON_get_stringT STR_EV req ;;
  term <- stringT_to_Term temp_term ;;
  req_plc <- stringT_to_Plc temp_req_plc ;;
  ev <- stringT_to_RawEv temp_ev ;;
  resultC (mkPRReq term req_plc ev).

Definition ProtocolRunResponse_to_JSON (resp: ProtocolRunResponse): JSON :=
  JSON__Object 
    [(STR_SUCCESS, (JSON__Boolean (prresp_success resp)));
    (STR_PAYLOAD, (JSON__String (RawEv_to_stringT (prresp_ev resp))))].

Definition JSON_to_ProtocolRunResponse (resp : JSON): ResultT ProtocolRunResponse StringT :=
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_ev <- JSON_get_stringT STR_PAYLOAD resp ;;
  ev <- stringT_to_RawEv temp_ev ;;
  resultC (mkPRResp temp_success ev).

(* Protocol Negotiate Section *)
Definition ProtocolNegotiateRequest_to_JSON (req: ProtocolNegotiateRequest): JSON :=
  JSON__Object 
    [(STR_TERM, (JSON__String (Term_to_stringT (pnreq_term req))))].

Definition JSON_to_ProtocolNegotiateRequest (req : JSON): 
    ResultT ProtocolNegotiateRequest StringT :=
  temp_term <- JSON_get_stringT STR_TERM req ;;
  term <- stringT_to_Term temp_term ;;
  resultC (mkPNReq term).

Definition ProtocolNegotiateResponse_to_JSON (resp: ProtocolNegotiateResponse): JSON :=
  JSON__Object 
    [(STR_SUCCESS, (JSON__Boolean (pnresp_success resp)));
    (STR_PAYLOAD, (JSON__String (Term_to_stringT (pnresp_term resp))))].

Definition JSON_to_ProtocolNegotiateResponse (resp : JSON): 
    ResultT ProtocolNegotiateResponse StringT :=
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_term <- JSON_get_stringT STR_PAYLOAD resp ;;
  term <- stringT_to_Term temp_term ;;
  resultC (mkPNResp temp_success term).

(* Protocol Appraise Section *)
Definition ProtocolAppraiseRequest_to_JSON (req: ProtocolAppraiseRequest): JSON :=
  JSON__Object 
    [(STR_TERM, (JSON__String (Term_to_stringT (pareq_term req))));
    (STR_REQ_PLC, (JSON__String (Plc_to_stringT (pareq_plc req))));
    (STR_EVIDENCE, (JSON__String (Evidence_to_stringT (pareq_evidence req))));
    (STR_EV, (JSON__String (RawEv_to_stringT (pareq_ev req))))].

Definition JSON_to_ProtocolAppraiseRequest (req : JSON): 
    ResultT ProtocolAppraiseRequest StringT :=
  temp_term <- JSON_get_stringT STR_TERM req ;;
  temp_plc <- JSON_get_stringT STR_REQ_PLC req ;;
  temp_evidence <- JSON_get_stringT STR_EVIDENCE req ;;
  temp_ev <- JSON_get_stringT STR_EV req ;;
  term <- stringT_to_Term temp_term ;;
  plc <- stringT_to_Plc temp_plc ;;
  evidence <- stringT_to_Evidence temp_evidence ;;
  ev <- stringT_to_RawEv temp_ev ;;
  resultC (mkPAReq term plc evidence ev).

Definition ProtocolAppraiseResponse_to_JSON (resp: ProtocolAppraiseResponse): JSON :=
  JSON__Object 
    [(STR_SUCCESS, (JSON__Boolean (paresp_success resp)));
    (STR_PAYLOAD, (JSON__String (AppResultC_to_stringT (paresp_result resp))))].

Definition JSON_to_ProtocolAppraiseResponse (resp : JSON): 
    ResultT ProtocolAppraiseResponse StringT :=
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_result <- JSON_get_stringT STR_PAYLOAD resp ;;
  result <- stringT_to_AppResultC temp_result ;;
  resultC (mkPAResp temp_success result).

(* TODO: These are commented because they are excessive and not too necessary

(* AM Protocol Request Section *)
Definition AM_Protocol_Request_to_JSON (req: AM_Protocol_Requests): JSON :=
  match req with
  | Protocol_Run_Request r => ProtocolRunRequest_to_JSON r
  | Protocol_Appraise_Request r => ProtocolAppraiseRequest_to_JSON r
  | Protocol_Negotiate_Request r => ProtocolNegotiateRequest_to_JSON r
  end.

Definition JSON_to_AM_Protocol_Request (req : JSON): option AM_Protocol_Requests :=
  temp_type <- JSON_get_stringT "action" req ;;
  match temp_type with
  | "RUN" => temp_req <- JSON_to_ProtocolRunRequest req ;;
    Some (Protocol_Run_Request temp_req)
  | "NEGOTIATE" => temp_req <- JSON_to_ProtocolAppraiseRequest req ;;
    Some (Protocol_Appraise_Request temp_req)
  | "APPRAISE" => temp_req <- JSON_to_ProtocolNegotiateRequest req ;;
    Some (Protocol_Negotiate_Request temp_req)
  | _ => None
  end.

(* AM Protocol Response Section *)
Definition AM_Protocol_Response_to_JSON (resp: AM_Protocol_Responses): JSON :=
  match resp with
  | Protocol_Run_Response r => ProtocolRunResponse_to_JSON r
  | Protocol_Appraise_Response r => ProtocolAppraiseResponse_to_JSON r
  | Protocol_Negotiate_Response r => ProtocolNegotiateResponse_to_JSON r
  end.

Definition JSON_to_AM_Protocol_Response (resp : JSON): option AM_Protocol_Responses :=
  temp_type <- JSON_get_stringT "action" resp ;;
  match temp_type with
  | "RUN" => temp_resp <- JSON_to_ProtocolRunResponse resp ;;
    Some (Protocol_Run_Response temp_resp)
  | "NEGOTIATE" => temp_resp <- JSON_to_ProtocolAppraiseResponse resp ;;
    Some (Protocol_Appraise_Response temp_resp)
  | "APPRAISE" => temp_resp <- JSON_to_ProtocolNegotiateResponse resp ;;
    Some (Protocol_Negotiate_Response temp_resp)
  | _ => None
  end.

(* AM Protocol Interface Section *)
Definition AM_Protocol_Interface_to_JSON (msg: AM_Protocol_Interface): JSON :=
  match msg with
  | AM_Protocol_Request_Interface r => AM_Protocol_Request_to_JSON r
  | AM_Protocol_Response_Interface r => AM_Protocol_Response_to_JSON r
  end.

Definition JSON_to_AM_Protocol_Interface (msg : JSON): option AM_Protocol_Interface :=
  temp_type <- JSON_get_stringT "type" msg ;;
  match temp_type with
  | "REQUEST" => temp_msg <- JSON_to_AM_Protocol_Request msg ;;
    Some (AM_Protocol_Request_Interface temp_msg)
  | "RESPONSE" => temp_msg <- JSON_to_AM_Protocol_Response msg ;;
    Some (AM_Protocol_Response_Interface temp_msg)
  | _ => None
  end.

*)

(* Error Response *)
Definition ErrorResponseJSON (msg: StringT): JSON :=
  JSON__Object 
    [(STR_SUCCESS, JSON__Boolean false);
    (STR_PAYLOAD, (JSON__String msg))].
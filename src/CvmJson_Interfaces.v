(* Admitted definitions of JSON types and conversions to/from strings 
    and Copland datatypes at the boundary of AMs.
    
    At the moment, these are too low-level to represent faithfully in the Coq development.   *)

Require Import Term_Defs_Core Term_Defs String List JSON Interface_Types ResultT ErrorStringConstants Term_Defs_Admits BS.
Export Interface_Types JSON.
Import ListNotations ResultNotation.

(* Protocol Run Section *)
Definition ProtocolRunRequest_to_JSON (req: ProtocolRunRequest): JSON :=
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_RUN));
    (STR_REQ_PLC, (JSON_String (Plc_to_string (prreq_req_plc req))));
    (STR_TERM, (JSON_String (Term_to_string (prreq_term req)))); 
    (STR_EV, (JSON_String (RawEv_to_string (prreq_ev req))))].

Definition JSON_to_ProtocolRunRequest (req : JSON): ResultT ProtocolRunRequest string :=
  temp_term <- JSON_get_string STR_TERM req ;;
  temp_req_plc <- JSON_get_string STR_REQ_PLC req ;;
  temp_ev <- JSON_get_string STR_EV req ;;
  term <- string_to_Term temp_term ;;
  req_plc <- string_to_Plc temp_req_plc ;;
  ev <- string_to_RawEv temp_ev ;;
  resultC (mkPRReq term req_plc ev).

Definition ProtocolRunResponse_to_JSON (resp: ProtocolRunResponse): JSON :=
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_RUN));
    (STR_SUCCESS, (JSON_Boolean (prresp_success resp)));
    (STR_PAYLOAD, (JSON_String (RawEv_to_string (prresp_ev resp))))].

Definition JSON_to_ProtocolRunResponse (resp : JSON): ResultT ProtocolRunResponse string :=
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_ev <- JSON_get_string STR_PAYLOAD resp ;;
  ev <- string_to_RawEv temp_ev ;;
  resultC (mkPRResp temp_success ev).

(* Protocol Negotiate Section *)
Definition ProtocolNegotiateRequest_to_JSON (req: ProtocolNegotiateRequest): JSON :=
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_NEGOTIATE));
      (STR_TERM, (JSON_String (Term_to_string (pnreq_term req))))].

Definition JSON_to_ProtocolNegotiateRequest (req : JSON): 
    ResultT ProtocolNegotiateRequest string :=
  temp_term <- JSON_get_string STR_TERM req ;;
  term <- string_to_Term temp_term ;;
  resultC (mkPNReq term).

Definition ProtocolNegotiateResponse_to_JSON (resp: ProtocolNegotiateResponse): JSON :=
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_NEGOTIATE));
      (STR_SUCCESS, (JSON_Boolean (pnresp_success resp)));
    (STR_PAYLOAD, (JSON_String (Term_to_string (pnresp_term resp))))].

Definition JSON_to_ProtocolNegotiateResponse (resp : JSON): 
    ResultT ProtocolNegotiateResponse string :=
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_term <- JSON_get_string STR_PAYLOAD resp ;;
  term <- string_to_Term temp_term ;;
  resultC (mkPNResp temp_success term).

(* Protocol Appraise Section *)
Definition ProtocolAppraiseRequest_to_JSON (req: ProtocolAppraiseRequest): JSON :=
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_APPRAISE));
    (STR_TERM, (JSON_String (Term_to_string (pareq_term req))));
    (STR_REQ_PLC, (JSON_String (Plc_to_string (pareq_plc req))));
    (STR_EVIDENCE, (JSON_String (Evidence_to_string (pareq_evidence req))));
    (STR_EV, (JSON_String (RawEv_to_string (pareq_ev req))))].

Definition JSON_to_ProtocolAppraiseRequest (req : JSON): 
    ResultT ProtocolAppraiseRequest string :=
  temp_term <- JSON_get_string STR_TERM req ;;
  temp_plc <- JSON_get_string STR_REQ_PLC req ;;
  temp_evidence <- JSON_get_string STR_EVIDENCE req ;;
  temp_ev <- JSON_get_string STR_EV req ;;
  term <- string_to_Term temp_term ;;
  plc <- string_to_Plc temp_plc ;;
  evidence <- string_to_Evidence temp_evidence ;;
  ev <- string_to_RawEv temp_ev ;;
  resultC (mkPAReq term plc evidence ev).

Definition ProtocolAppraiseResponse_to_JSON (resp: ProtocolAppraiseResponse): JSON :=
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_APPRAISE));
    (STR_SUCCESS, (JSON_Boolean (paresp_success resp)));
    (STR_PAYLOAD, (JSON_String (AppResultC_to_string (paresp_result resp))))].

Definition JSON_to_ProtocolAppraiseResponse (resp : JSON): 
    ResultT ProtocolAppraiseResponse string :=
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_result <- JSON_get_string STR_PAYLOAD resp ;;
  result <- string_to_AppResultC temp_result ;;
  resultC (mkPAResp temp_success result).

(* AM Protocol Request Section *)
Definition AM_Protocol_Request_to_JSON (req: AM_Protocol_Requests): JSON :=
  match req with
  | Protocol_Run_Request r => ProtocolRunRequest_to_JSON r
  | Protocol_Appraise_Request r => ProtocolAppraiseRequest_to_JSON r
  | Protocol_Negotiate_Request r => ProtocolNegotiateRequest_to_JSON r
  end.

Definition JSON_to_AM_Protocol_Request (req : JSON): 
    ResultT AM_Protocol_Requests string :=
  temp_type <- JSON_get_string STR_ACTION req ;;
  if (eqb temp_type STR_RUN)
  then (temp_req <- JSON_to_ProtocolRunRequest req ;;
        resultC (Protocol_Run_Request temp_req))
  else if (eqb temp_type STR_APPRAISE)
  then (temp_req <- JSON_to_ProtocolAppraiseRequest req ;;
        resultC (Protocol_Appraise_Request temp_req))
  else if (eqb temp_type STR_NEGOTIATE)
  then (temp_req <- JSON_to_ProtocolNegotiateRequest req ;;
        resultC (Protocol_Negotiate_Request temp_req))
  else errC errStr_invalid_request_type.

(* AM Protocol Response Section *)
Definition AM_Protocol_Response_to_JSON (resp: AM_Protocol_Responses): JSON :=
  match resp with
  | Protocol_Run_Response r => ProtocolRunResponse_to_JSON r
  | Protocol_Appraise_Response r => ProtocolAppraiseResponse_to_JSON r
  | Protocol_Negotiate_Response r => ProtocolNegotiateResponse_to_JSON r
  end.

Definition JSON_to_AM_Protocol_Response (resp : JSON): 
    ResultT AM_Protocol_Responses string :=
  temp_type <- JSON_get_string STR_ACTION resp ;;
  if (eqb temp_type STR_RUN)
  then (temp_resp <- JSON_to_ProtocolRunResponse resp ;;
        resultC (Protocol_Run_Response temp_resp))
  else if (eqb temp_type STR_APPRAISE)
  then (temp_resp <- JSON_to_ProtocolAppraiseResponse resp ;;
        resultC (Protocol_Appraise_Response temp_resp))
  else if (eqb temp_type STR_NEGOTIATE)
  then (temp_resp <- JSON_to_ProtocolNegotiateResponse resp ;;
        resultC (Protocol_Negotiate_Response temp_resp))
  else errC errStr_invalid_request_type.

(* AM Protocol Interface Section *)
Definition AM_Protocol_Interface_to_JSON (msg: AM_Protocol_Interface): JSON :=
  match msg with
  | AM_Protocol_Request_Interface r => AM_Protocol_Request_to_JSON r
  | AM_Protocol_Response_Interface r => AM_Protocol_Response_to_JSON r
  end.

Definition JSON_to_AM_Protocol_Interface (msg : JSON): 
    ResultT AM_Protocol_Interface string :=
  temp_type <- JSON_get_string STR_TYPE msg ;;
  if (eqb temp_type STR_REQUEST)
  then (temp_msg <- JSON_to_AM_Protocol_Request msg ;;
        resultC (AM_Protocol_Request_Interface temp_msg))
  else if (eqb temp_type STR_RESPONSE)
  then (temp_msg <- JSON_to_AM_Protocol_Response msg ;;
        resultC (AM_Protocol_Response_Interface temp_msg))
  else errC errStr_incorrect_resp_type.


(* ASP Run Request Section *)
Definition ASPRunRequest_to_JSON (req: ASPRunRequest): JSON :=
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_REQUEST));
    (STR_ACTION, (JSON_String STR_ASP_RUN));
    (STR_ASP_ID, (JSON_String (ASP_ID_to_string (asprreq_asp_id req))));
    (STR_ASP_ARGS, (JSON_String (ASP_ARGS_to_string (asprreq_asp_args req))));
    (STR_TARG_PLC, (JSON_String (Plc_to_string (asprreq_targ_plc req))));
    (STR_TARG, (JSON_String (TARG_ID_to_string (asprreq_targ req))));
    (STR_EV, (JSON_String (RawEv_to_string (asprreq_rawev req))))].

Definition JSON_to_ASPRunRequest (req : JSON): ResultT ASPRunRequest string :=
  temp_asp_id <- JSON_get_string STR_ASP_ID req ;;
  temp_asp_args <- JSON_get_string STR_ASP_ARGS req ;;
  temp_targ_plc <- JSON_get_string STR_TARG_PLC req ;;
  temp_targ <- JSON_get_string STR_TARG req ;;
  temp_ev <- JSON_get_string STR_EV req ;;
  asp_id <- string_to_ASP_ID temp_asp_id ;;
  asp_args <- string_to_ASP_ARGS temp_asp_args ;;
  targ_plc <- string_to_Plc temp_targ_plc ;;
  targ <- string_to_TARG_ID temp_targ ;;
  ev <- string_to_RawEv temp_ev ;;
  resultC (mkASPRReq asp_id asp_args targ_plc targ ev).

Definition ASPRunResponse_to_JSON (resp: ASPRunResponse): JSON :=
  JSON_Object 
    [(STR_TYPE, (JSON_String STR_RESPONSE));
    (STR_ACTION, (JSON_String STR_ASP_RUN));
    (STR_SUCCESS, (JSON_Boolean (asprresp_success resp)));
    (STR_PAYLOAD, (JSON_String (RawEv_to_string (asprresp_rawev resp))))].

Definition JSON_to_ASPRunResponse (resp : JSON): ResultT ASPRunResponse string :=
  temp_success <- JSON_get_bool STR_SUCCESS resp ;;
  temp_rawev <- JSON_get_string STR_PAYLOAD resp ;;
  rawev <- string_to_RawEv temp_rawev ;;
  resultC (mkASPRResp temp_success rawev).

(* AM ASP Interface Section *)

Definition AM_ASP_Interface_to_JSON (msg: AM_ASP_Interface): JSON :=
  match msg with
  | ASP_Run_Request r => ASPRunRequest_to_JSON r
  | ASP_Run_Response r => ASPRunResponse_to_JSON r
  end.

Definition JSON_to_AM_ASP_Interface (msg : JSON): 
    ResultT AM_ASP_Interface string :=
  temp_type <- JSON_get_string STR_TYPE msg ;;
  temp_action <- JSON_get_string STR_ACTION msg ;;
  if (eqb temp_type STR_REQUEST)
  then if (eqb temp_action STR_ASP_RUN)
       then (temp_msg <- JSON_to_ASPRunRequest msg ;;
             resultC (ASP_Run_Request temp_msg))
       else errC errStr_invalid_request_type
  else if (eqb temp_type STR_RESPONSE)
      then if (eqb temp_action STR_ASP_RUN)
          then (temp_msg <- JSON_to_ASPRunResponse msg ;;
                resultC (ASP_Run_Response temp_msg))
          else errC errStr_invalid_request_type
  else errC errStr_incorrect_resp_type.

(* Error Response *)
Definition ErrorResponseJSON (msg: string): JSON :=
  JSON_Object 
    [(STR_SUCCESS, JSON_Boolean false);
    (STR_PAYLOAD, (JSON_String msg))].
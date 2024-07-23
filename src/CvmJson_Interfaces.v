(* Admitted definitions of JSON types and conversions to/from strings 
    and Copland datatypes at the boundary of AMs.
    
    At the moment, these are too low-level to represent faithfully in the Coq development.   *)

Require Import Term_Defs_Core Term_Defs List JSON Interface ResultT ErrorStringConstants BS Stringifiable.
Export Interface JSON.
Import ListNotations ResultNotation.

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

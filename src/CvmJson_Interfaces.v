(* Admitted definitions of JSON types and conversions to/from strings 
    and Copland datatypes at the boundary of AMs.
    
    At the moment, these are too low-level to represent faithfully in the Coq development.   *)

Require Import Term_Defs_Core Term_Defs StringT List.
From JSON Require Import JSON Lexer Printer.
Import ListNotations.
Require Import ExtLib.Structures.Monads.

Definition strToJson (s:StringT): option json := 
  match from_string (StringT_to_string s) with
  | inl e => None
  | inr j => Some j
  end.

Definition jsonToStr (js: json): StringT := 
  string_to_StringT (to_string js).

(* Protocol Run Section *)
Definition ProtocolRunRequest_to_Json (req: ProtocolRunRequest): json :=
  JSON__Object 
    [("term", (JSON__String (Term_to_string (prreq_term req)))); 
    ("authTok", (JSON__String (EvC_to_string (prreq_authTok req)))); 
    ("ev", (JSON__String (RawEv_to_string (prreq_ev req))))].

Definition Json_to_ProtocolRunRequest (req : json): option ProtocolRunRequest :=
  temp_term <- get_string "term" req ;;
  temp_authTok <- get_string "authTok" req ;;
  temp_ev <- get_string "ev" req ;;
  term <- string_to_Term temp_term ;;
  authTok <- string_to_EvC temp_authTok ;;
  ev <- string_to_RawEv temp_ev ;;
  Some (mkPRReq term authTok ev).

Definition ProtocolRunResponse_to_Json (resp: ProtocolRunResponse): json :=
  JSON__Object 
    [("success", (if (prresp_success resp) then JSON__True else JSON__False));
    ("payload", (JSON__String (RawEv_to_string (prresp_ev resp))))].

Definition Json_to_ProtocolRunResponse (resp : json): option ProtocolRunResponse :=
  temp_success <- get_bool "success" resp ;;
  temp_ev <- get_string "payload" resp ;;
  ev <- string_to_RawEv temp_ev ;;
  Some (mkPRResp temp_success ev).

(* Protocol Negotiate Section *)
Definition ProtocolNegotiateRequest_to_Json (req: ProtocolNegotiateRequest): json :=
  JSON__Object 
    [("term", (JSON__String (Term_to_string (pnreq_term req))))].

Definition Json_to_ProtocolNegotiateRequest (req : json): option ProtocolNegotiateRequest :=
  temp_term <- get_string "term" req ;;
  term <- string_to_Term temp_term ;;
  Some (mkPNReq term).

Definition ProtocolNegotiateResponse_to_Json (resp: ProtocolNegotiateResponse): json :=
  JSON__Object 
    [("success", (if (pnresp_success resp) then JSON__True else JSON__False));
    ("payload", (JSON__String (Term_to_string (pnresp_term resp))))].

Definition Json_to_ProtocolNegotiateResponse (resp : json): option ProtocolNegotiateResponse :=
  temp_success <- get_bool "success" resp ;;
  temp_term <- get_string "payload" resp ;;
  term <- string_to_Term temp_term ;;
  Some (mkPNResp temp_success term).

(* Protocol Appraise Section *)
Definition ProtocolAppraiseRequest_to_Json (req: ProtocolAppraiseRequest): json :=
  JSON__Object 
    [("term", (JSON__String (Term_to_string (pareq_term req))));
    ("plc", (JSON__String (Plc_to_string (pareq_plc req))));
    ("evidence", (JSON__String (Evidence_to_string (pareq_evidence req))));
    ("ev", (JSON__String (RawEv_to_string (pareq_ev req))))].

Definition Json_to_ProtocolAppraiseRequest (req : json): option ProtocolAppraiseRequest :=
  temp_term <- get_string "term" req ;;
  temp_plc <- get_string "plc" req ;;
  temp_evidence <- get_string "ev" req ;;
  temp_ev <- get_string "ev" req ;;
  term <- string_to_Term temp_term ;;
  plc <- string_to_Plc temp_plc ;;
  evidence <- string_to_Evidence temp_evidence ;;
  ev <- string_to_RawEv temp_ev ;;
  Some (mkPAReq term plc evidence ev).

Definition ProtocolAppraiseResponse_to_Json (resp: ProtocolAppraiseResponse): json :=
  JSON__Object 
    [("success", (if (paresp_success resp) then JSON__True else JSON__False));
    ("payload", (JSON__String (AppResultC_to_string (paresp_result resp))))].

Definition Json_to_ProtocolAppraiseResponse (resp : json): option ProtocolAppraiseResponse :=
  temp_success <- get_bool "success" resp ;;
  temp_result <- get_string "payload" resp ;;
  result <- string_to_AppResultC temp_result ;;
  Some (mkPAResp temp_success result).

(* AM Protocol Request Section *)
Definition AM_Protocol_Request_to_Json (req: AM_Protocol_Requests): json :=
  match req with
  | Protocol_Run_Request r => ProtocolRunRequest_to_Json r
  | Protocol_Appraise_Request r => ProtocolAppraiseRequest_to_Json r
  | Protocol_Negotiate_Request r => ProtocolNegotiateRequest_to_Json r
  end.

Definition Json_to_AM_Protocol_Request (req : json): option AM_Protocol_Requests :=
  temp_type <- get_string "action" req ;;
  match temp_type with
  | "RUN" => temp_req <- Json_to_ProtocolRunRequest req ;;
    Some (Protocol_Run_Request temp_req)
  | "NEGOTIATE" => temp_req <- Json_to_ProtocolAppraiseRequest req ;;
    Some (Protocol_Appraise_Request temp_req)
  | "APPRAISE" => temp_req <- Json_to_ProtocolNegotiateRequest req ;;
    Some (Protocol_Negotiate_Request temp_req)
  | _ => None
  end.

(* AM Protocol Response Section *)
Definition AM_Protocol_Response_to_Json (resp: AM_Protocol_Responses): json :=
  match resp with
  | Protocol_Run_Response r => ProtocolRunResponse_to_Json r
  | Protocol_Appraise_Response r => ProtocolAppraiseResponse_to_Json r
  | Protocol_Negotiate_Response r => ProtocolNegotiateResponse_to_Json r
  end.

Definition Json_to_AM_Protocol_Response (resp : json): option AM_Protocol_Responses :=
  temp_type <- get_string "action" resp ;;
  match temp_type with
  | "RUN" => temp_resp <- Json_to_ProtocolRunResponse resp ;;
    Some (Protocol_Run_Response temp_resp)
  | "NEGOTIATE" => temp_resp <- Json_to_ProtocolAppraiseResponse resp ;;
    Some (Protocol_Appraise_Response temp_resp)
  | "APPRAISE" => temp_resp <- Json_to_ProtocolNegotiateResponse resp ;;
    Some (Protocol_Negotiate_Response temp_resp)
  | _ => None
  end.

(* AM Protocol Interface Section *)
Definition AM_Protocol_Interface_to_Json (msg: AM_Protocol_Interface): json :=
  match msg with
  | AM_Protocol_Request_Interface r => AM_Protocol_Request_to_Json r
  | AM_Protocol_Response_Interface r => AM_Protocol_Response_to_Json r
  end.

Definition Json_to_AM_Protocol_Interface (msg : json): option AM_Protocol_Interface :=
  temp_type <- get_string "type" msg ;;
  match temp_type with
  | "REQUEST" => temp_msg <- Json_to_AM_Protocol_Request msg ;;
    Some (AM_Protocol_Request_Interface temp_msg)
  | "RESPONSE" => temp_msg <- Json_to_AM_Protocol_Response msg ;;
    Some (AM_Protocol_Response_Interface temp_msg)
  | _ => None
  end.

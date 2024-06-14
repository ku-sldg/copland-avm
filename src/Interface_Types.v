Require Import JSON Term_Defs StringT.

(* Interface StringT Values *)
Definition STR_REQ_PLC : StringT. Admitted.
Definition STR_TERM : StringT. Admitted.
Definition STR_EV : StringT. Admitted.
Definition STR_SUCCESS : StringT. Admitted.
Definition STR_PAYLOAD : StringT. Admitted.
Definition STR_EVIDENCE : StringT. Admitted.

Definition STR_ACTION : StringT. Admitted.
Definition STR_TYPE : StringT. Admitted.

Definition STR_RUN : StringT. Admitted.
Definition STR_NEGOTIATE : StringT. Admitted.
Definition STR_APPRAISE : StringT. Admitted.
Definition STR_REQUEST : StringT. Admitted.
Definition STR_RESPONSE : StringT. Admitted.

(* Interface Types *)
Record ProtocolRunRequest := 
  mkPRReq {
    prreq_term: Term;
    prreq_req_plc: Plc;
    prreq_ev: RawEv;
  }.

Record ProtocolRunResponse := 
  mkPRResp {
    prresp_success: bool;
    prresp_ev: RawEv;
  }.

Record ProtocolNegotiateRequest := 
  mkPNReq {
    pnreq_term: Term;
  }.

Record ProtocolNegotiateResponse := 
  mkPNResp {
    pnresp_success: bool;
    pnresp_term: Term;
  }.

Record ProtocolAppraiseRequest :=
  mkPAReq {
    pareq_term: Term;
    pareq_plc: Plc;
    pareq_evidence: Evidence;
    pareq_ev: RawEv;
  }.

Record ProtocolAppraiseResponse :=
  mkPAResp {
    paresp_success: bool;
    paresp_result: AppResultC;
  }.

Record ASPRunRequest := 
  mkASPRReq {
    asprreq_asp_id : ASP_ID;
    asprreq_asp_args: ASP_ARGS;
  }.

Record ASPRunResponse := 
  mkASPRResp {
    asprresp_success: bool;
    asprresp_ev: RawEv;
  }.

Record ASPInfoRequest := 
  mkASPIReq {
    aspireq_asp_id : ASP_ID;
  }.

Record ASPInfoResponse :=
  mkASPIResp {
    aspiresp_success: bool;
    aspiresp_info: ASP_Info;
  }.

Inductive AM_Protocol_Requests :=
| Protocol_Run_Request: ProtocolRunRequest -> AM_Protocol_Requests
| Protocol_Negotiate_Request: ProtocolNegotiateRequest -> AM_Protocol_Requests
| Protocol_Appraise_Request: ProtocolAppraiseRequest -> AM_Protocol_Requests.

Inductive AM_Protocol_Responses :=
| Protocol_Run_Response : ProtocolRunResponse -> AM_Protocol_Responses
| Protocol_Negotiate_Response: ProtocolNegotiateResponse -> AM_Protocol_Responses
| Protocol_Appraise_Response: ProtocolAppraiseResponse -> AM_Protocol_Responses.

Inductive AM_Protocol_Interface :=
| AM_Protocol_Request_Interface: AM_Protocol_Requests -> AM_Protocol_Interface
| AM_Protocol_Response_Interface: AM_Protocol_Responses -> AM_Protocol_Interface.

Inductive AM_ASP_Interface :=
| ASP_Run_Request: ASPRunRequest -> AM_ASP_Interface
| ASP_Run_Response : ASPRunResponse -> AM_ASP_Interface
| ASP_Info_Request: ASPInfoRequest -> AM_ASP_Interface
| ASP_Info_Response: ASPInfoResponse -> AM_ASP_Interface.

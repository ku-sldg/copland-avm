Require Import JSON Term_Defs StringT.

(* Interface StringT Values *)
Definition STR_REQ_PLC : StringT. Admitted.
Definition STR_TERM : StringT. Admitted.
Definition STR_EV : StringT. Admitted.
Definition STR_SUCCESS : StringT. Admitted.
Definition STR_PAYLOAD : StringT. Admitted.
Definition STR_EVIDENCE : StringT. Admitted.

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
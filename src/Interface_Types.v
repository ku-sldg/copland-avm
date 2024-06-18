Require Import JSON Term_Defs StringT.
Require Export Interface_Strings_Admits.


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
    asprreq_targ_plc : Plc ;
    asprreq_targ : TARG_ID ;
    asprreq_rawev : RawEv;
  }.

Record ASPRunResponse := 
  mkASPRResp {
    asprresp_success: bool;
    asprresp_bs: BS;
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
| ASP_Run_Response : ASPRunResponse -> AM_ASP_Interface.
(* NOTE: Eventually we will add these
| ASP_Info_Request: ASPInfoRequest -> AM_ASP_Interface
| ASP_Info_Response: ASPInfoResponse -> AM_ASP_Interface. *)

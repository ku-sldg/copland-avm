Require Import JSON Term_Defs Attestation_Session.
Require Export Interface_Strings_Vars.


(* Interface Types *)
Record ProtocolRunRequest := 
  mkPRReq {
    prreq_att_sesplit_evt : Attestation_Session;
    prreq_term: Term;
    prreq_req_plc: Plc;
    prreq_rawev: RawEv;
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
    pareq_att_sess: Attestation_Session;
    pareq_term: Term;
    pareq_plc: Plc;
    pareq_EvidenceT: EvidenceT;
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
    asprresp_rawev: RawEv;
  }.

(* Record ASPInfoRequest := 
  mkASPIReq {
    aspireq_asp_id : ASP_ID;
  }.

Record ASPInfoResponse :=
  mkASPIResp {
    aspiresp_success: bool;
    aspiresp_info: ASP_Info;
  }. *)

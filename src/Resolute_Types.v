Require Import Term_Defs Resolute_Logic JSON. (* Attestation_Session AppraisalSummary. *)
(* Require Export Interface_Strings_Vars. *)

Record Resolute_Client_Request := 
  mkResoluteClientReq {
    resclientreq_attest_id: string;
    resclientreq_args: JSON;
    resclientreq_resultpath: string;
  }.

Record Resolute_Client_Response := 
  mkResoluteClientResp {
    resclientresp_success: bool
  }.

Record Resolute_Client_Result := 
  mkResoluteClientResult {
    resclientres_term: Term;
    resclientres_evidence: Evidence;
    resclientres_success: bool;
    resclientres_error_str: string;
  }.


Record ResoluteResponse := 
    mkResoluteResp {
      resoluteresp_judgement: Resolute_Judgement;
      resoluteresp_formula: Resolute_Formula;
      resoluteresp_term: Resolute_Term;
  }.

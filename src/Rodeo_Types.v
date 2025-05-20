Require Import Term_Defs String JSON.

Record RODEO_Client_Request := 
  mkRODEOClientReq {
    resclientreq_attest_id: string;
    resclientreq_args: JSON;
    resclientreq_resultpath: string;
  }.

Record RODEO_Client_Response := 
mkRODEOClientResp {
  resclientres_term: Term;
  resclientres_evidence: Evidence;
  resclientres_success: bool;
  resclientres_error_str: string;
}.

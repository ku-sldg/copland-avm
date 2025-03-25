Require Import Term_Defs String JSON.

Record Resolute_Client_Request := 
  mkResoluteClientReq {
    resclientreq_attest_id: string;
    resclientreq_args: JSON;
    resclientreq_resultpath: string;
  }.

Record Resolute_Client_Response := 
mkResoluteClientResp {
  resclientres_term: Term;
  resclientres_evidence: Evidence;
  resclientres_success: bool;
  resclientres_error_str: string;
}.

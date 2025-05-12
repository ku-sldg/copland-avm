Require Import List.
Import ListNotations.
Require Import BS Term_Defs Attestation_Session Interface String IO_Stubs Manifest_Admits ErrorStMonad_Coq AM_Monad Session_Config_Compiler Cvm_St Cvm_Impl.
Require Import ErrorStringConstants AM_Manager.
Require Import AppraisalSummary.
Import ErrNotation.

Definition handle_AM_request_JSON (conf : AM_Manager_Config) (js : JSON) (nonceVal:BS) : JSON :=
  match (JSON_get_string STR_ACTION js) with
  | errC msg => ErrorResponseJSON msg
  | resultC req_type =>
    if (eqb req_type STR_RUN)
    then (
      match (from_JSON js) with
      | errC msg => ErrorResponseJSON msg
      | resultC r =>
        let '(mkPRReq att_sess from_plc to_plc ev cop_term) := r in
        let sc := (session_config_compiler conf att_sess) in
        let init_st := (mk_st [] 0) in
        let '(cvm_resp, _, _) := (build_cvm ev cop_term init_st sc) in
        match cvm_resp with
        | errC e => ErrorResponseJSON (CVM_Error_to_string e)
        | resultC res_ev => to_JSON (mkPRResp true res_ev)
        end
      end
    )
    else if (eqb req_type STR_NEGOTIATE)
    then     (
      (* TODO: Fill this in when negotiation is implemented *)
      ErrorResponseJSON errStr_negotiation_not_implemented
    )
    else if (eqb req_type STR_APPSUMM)
    then (
      match (from_JSON js) with
      | errC msg => ErrorResponseJSON msg
      | resultC r =>
        let '(mkAppSummReq att_sess e) := r in
        let '(evc rawEv et) := e in 
        let glob_ctx := (ats_context att_sess) in 
        let appsumm_result : ResultT AppraisalSummary string := do_AppraisalSummary et rawEv glob_ctx in 
        match appsumm_result with 
        | errC s => ErrorResponseJSON s
        | resultC appsumm => 
          let appsumm_success_bool := (fold_appsumm appsumm) in 
            to_JSON (mkAppSummResp appsumm_success_bool appsumm)   
        end
      end
    )
    else if (eqb req_type STR_EVSLICE)
    then (
      match (from_JSON js) with
      | errC msg => ErrorResponseJSON msg
      | resultC r =>
        let '(mkEvSliceReq e glob_ctxt params) := r in
        let '(evc rawEv et) := e in 
        let rawev_result := get_Evidence_Rawev et rawEv glob_ctxt params in 
        match rawev_result with 
        | errC s => ErrorResponseJSON s
        | resultC v => 
          let success_bool := true in 
            to_JSON (mkEvSliceResp success_bool v)   
        end
      end
    )
    else ErrorResponseJSON err_str_01
  end.
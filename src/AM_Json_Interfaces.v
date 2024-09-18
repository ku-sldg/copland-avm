Require Import List.
Import ListNotations.
Require Import BS Term_Defs Attestation_Session Interface String IO_Stubs Manifest_Admits ErrorStMonad_Coq AM_Monad Session_Config_Compiler.
Require Import ErrorStringConstants Cvm_Run AM_Manager.
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
        let '(mkPRReq att_sess from_plc ev cop_term) := r in
        let sc := (session_config_compiler conf att_sess) in
        let cvm_resp := (run_cvm_init_ev sc ev cop_term) in
        match cvm_resp with
        | errC e => ErrorResponseJSON e
        | resultC res_ev => to_JSON (mkPRResp true res_ev)
        end
      end
    )
    else if (eqb req_type STR_NEGOTIATE)
    then (
      (* TODO: Fill this in when negotiation is implemented *)
      ErrorResponseJSON errStr_negotiation_not_implemented
    )
    else ErrorResponseJSON err_str_01
  end.

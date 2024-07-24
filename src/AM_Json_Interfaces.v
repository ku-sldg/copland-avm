Require Import List.
Import ListNotations.
Require Import BS Term_Defs Attestation_Session Interface String IO_Stubs Manifest_Admits ErrorStMonad_Coq AM_Monad Session_Config_Compiler Manifest.
Require Import ErrorStringConstants AM_Helpers Impl_appraisal Cvm_Run AM_Manager.

Definition am_check_auth_tok (t:Term) (fromPl:Plc) (authTok:ReqAuthTok) 
    : AM AppResultC :=
  match authTok with
  | evc auth_ev auth_et => 
    appres <-
    (match (requester_bound t fromPl authTok) with
     | false => am_failm (am_error errStr_requester_bound)
     | true => gen_appraise_AM auth_et auth_ev
     end) ;;
    ret appres
  end.
(* 
Definition am_serve_auth_tok_req (t:Term) (fromPl : Plc) 
                                 (authTok:ReqAuthTok) (init_ev:RawEv) (ac : AM_Config) (al:AM_Library) : AM RawEv :=
  let test_print := print_auth_tok authTok in
  v <- am_check_auth_tok t fromPl authTok ;;
  match ((appraise_auth_tok v)) with
  | true =>

    config_AM_if_lib_supported (absMan ac) al ;; 
  
    (*
    check_disclosure_policy t myPlc init_et ;;
    (* TODO: decide how to get initial Evidence type here for server AMs...  *)
    *)
    
    ret (run_cvm_rawEv t init_ev ac)
    (*
    | false => am_failm (am_error errStr_disclosePolicy)
    end *)
      
  | false => am_failm (am_error errStr_app_auth_tok)
  end. *)

Definition do_appraisal_session (conf : AM_Manager_Config) (appreq:ProtocolAppraiseRequest) (nonceVal:BS)
    : ResultT ProtocolAppraiseResponse string :=
  let '(mkPAReq att_sess t p et ev) := appreq in
  let expected_et := eval t p et in 
  let app_am := gen_appraise_AM expected_et ev in 
  let init_noncemap := [(O, nonceVal)] in
  let init_nonceid := (S O) in
  let sess_config := (session_config_compiler conf att_sess) in
  let my_amst := (mkAM_St init_noncemap init_nonceid sess_config) in
  match run_am_app_comp_init app_am my_amst with
  | errC e => errC e
  | resultC appres =>
      resultC (mkPAResp true appres)
  end.

Definition handle_AM_request_JSON (conf : AM_Manager_Config) (js : JSON) (nonceVal:BS) : JSON :=
  match (JSON_get_string STR_ACTION js) with
  | errC msg => ErrorResponseJSON msg
  | resultC req_type =>
    if (eqb req_type STR_RUN)
    then (
      match (from_JSON js) with
      | errC msg => ErrorResponseJSON msg
      | resultC r =>
        let '(mkPRReq att_sess cop_term from_plc ev) := r in
        let sc := (session_config_compiler conf att_sess) in
        let cvm_resp := (run_cvm_rawEv cop_term ev sc) in
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
    else if (eqb req_type STR_APPRAISE)
    then (
      match (from_JSON js) with
      | errC msg => ErrorResponseJSON msg
      | resultC appreq =>
        let app_resp := (do_appraisal_session conf appreq nonceVal) in 
        match app_resp with
        | errC e => ErrorResponseJSON e
        | resultC app_resp => to_JSON app_resp
        end
      end
    )
    else ErrorResponseJSON "Invalid request type"
  end.

Definition make_AM_Protocol_Run_request_JSON (att_sess : Attestation_Session)
    (t:Term) (targ_uuid : UUID) (tok:ReqAuthTok) (ev:RawEv) (from_plc : Plc)
    : ResultT RawEv string :=
  let req := (mkPRReq att_sess t from_plc ev) in
  let js_req := to_JSON req in
  let resp_res := make_JSON_Network_Request targ_uuid js_req in
  match resp_res with
  | resultC js_resp =>
      match from_JSON js_resp with
      | resultC prresp =>
        let '(mkPRResp success ev) := prresp in
        if success 
        then resultC ev 
        else errC errStr_remote_am_failure
      | errC msg => errC msg
      end
  | errC msg => errC msg
  end.
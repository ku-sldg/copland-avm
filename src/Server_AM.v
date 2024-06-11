(*  Implementation of a top-level Server (listener) thread for Server AMs in
      end-to-end Copland Attestation + Appraisal protocols.  *)

Require Import Term IO_Stubs Cvm_Run CvmJson_Interfaces Example_Phrases_Admits.

Require Import AM_Monad ErrorStMonad_Coq Impl_appraisal Manifest Manifest_Admits Cvm_St.

Require Import StringT ErrorStringConstants AM_Helpers.

Require Import List String.
Import ListNotations.


Definition am_check_auth_tok (t:Term) (fromPl:Plc) (authTok:ReqAuthTok) : AM AppResultC :=
  match authTok with
  | evc auth_ev auth_et => 
    appres <-
    (match (requester_bound t fromPl authTok) with
     | false => am_failm (am_error errStr_requester_bound)
     | true => gen_appraise_AM auth_et auth_ev
     end) ;;
    ret appres
  end.

Definition am_serve_auth_tok_req (t:Term) (fromPl : Plc) (myPl:Plc) 
                                 (authTok:ReqAuthTok) (init_ev:RawEv) (ac : AM_Config) (al:AM_Library) : AM RawEv :=
  let asdf := print_auth_tok authTok in
  v <- am_check_auth_tok t fromPl authTok ;;
  match ((appraise_auth_tok v)) with
  | true =>

    config_AM_if_lib_supported (absMan ac) al ;; 
  
    (*
    check_disclosure_policy t myPlc init_et ;;
    (* TODO: decide how to get initial Evidence type here for server AMs...  *)
    *)
    
    ret (run_cvm_rawEv t myPl init_ev ac)
    (*
    | false => am_failm (am_error errStr_disclosePolicy)
    end *)
      
  | false => am_failm (am_error errStr_app_auth_tok)
  end.

Definition run_am_server_auth_tok_req (t:Term) (fromPlc:Plc) (myPl:Plc) 
            (authTok:ReqAuthTok) (init_ev:RawEv) (ac : AM_Config) (al:AM_Library) : RawEv :=
              run_am_app_comp (am_serve_auth_tok_req t fromPlc myPl authTok init_ev ac al) [] true.
                            

Definition do_cvm_session (req:ProtocolRunRequest) (ac : AM_Config) (al:AM_Library): ProtocolRunResponse := 
  let fromPlc := default_place in 
  let myPlc := default_place in
  let '(mkPRReq t tok ev) := req in
  let asdf := print_auth_tok tok in 
  let resev := run_am_server_auth_tok_req t fromPlc myPlc tok ev ac al in 
    mkPRResp true resev.

Definition do_appraisal_session (appreq:ProtocolAppraiseRequest) (ac:AM_Config) (nonceVal:BS): ProtocolAppraiseResponse :=
  let '(mkPAReq t p et ev) := appreq in
  let expected_et := eval t p et in 
  let comp := gen_appraise_AM expected_et ev in 
  let init_noncemap := [(O, nonceVal)] in
  let init_nonceid := (S O) in
  let my_amst := (mkAM_St init_noncemap init_nonceid ac) in
  let appres := run_am_app_comp_init comp my_amst mtc_app true in
    mkPAResp true appres.

Open Scope string_scope.

Definition handle_AM_request (s:StringT) (ac : AM_Config) (al:AM_Library) (nonceVal:BS) : StringT :=
  match strToJson s with
  | None => (jsonToStr (ErrorResponseJson "Invalid JSON"))
  | Some js =>
    match Json_to_AM_Protocol_Request js with 
    | None => (jsonToStr (ErrorResponseJson "Invalid Request Format"))
    | Some (Protocol_Run_Request r) => 
      let cvm_resp := (do_cvm_session r ac al) in 
        jsonToStr (ProtocolRunResponse_to_Json cvm_resp)
    | Some (Protocol_Appraise_Request appreq) => 
      let app_resp := (do_appraisal_session appreq ac nonceVal) in 
        jsonToStr (ProtocolAppraiseResponse_to_Json app_resp)
    | Some (Protocol_Negotiate_Request r) => 
      (* TODO: Fill this in when negotiation is implemented *)
      jsonToStr (ErrorResponseJson "Negotiation not implemented yet")
    end
  end.

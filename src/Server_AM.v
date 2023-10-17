Require Import Term IO_Stubs Cvm_Run CvmJson_Admits Example_Phrases_Admits.

Require Import AM_Monad ErrorStMonad_Coq Impl_appraisal Manifest Manifest_Admits Cvm_St.

Require Import ErrorStringConstants.

Require Import AM_Helpers.

Require Import List.
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

  (*
    match (privPolicy fromPl t) with
    | true => 

  *)

    config_AM_if_lib_supported t myPl al ;; 
  
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
                            

Definition do_cvm_session (req:CvmRequestMessage) (ac : AM_Config) (al:AM_Library): CvmResponseMessage := 
  let fromPlc := default_place in 
  let myPlc := default_place in
  match req with 
  | REQ t tok ev => 
    let asdf := print_auth_tok tok in 
      let resev := run_am_server_auth_tok_req t fromPlc myPlc tok ev ac al in 
        (RES resev)
  end.

Definition do_appraisal_session (appreq:AppraisalRequestMessage): 
                                AppraisalResponseMessage :=
  let appres := 
    match appreq with
    | REQ_APP t p et ev => 
        let expected_et := eval t p et in 
        let comp := gen_appraise_AM expected_et ev in 
          run_am_app_comp comp mtc_app true
    end in 
      (RES_APP appres).

Definition handle_AM_request (s:StringT) (ac : AM_Config) (al:AM_Library) : StringT :=
  let js := strToJson s in 
  let am_req := jsonToAmRequest js in 
  let json_resp := 
    match am_req with 
    | CVM_REQ r => 
      let cvm_resp := (do_cvm_session r ac al) in 
        responseToJson cvm_resp
    | APP_REQ appreq => 
      let app_resp := (do_appraisal_session appreq) in 
        appResponseToJson app_resp
    end in 
    jsonToStr json_resp.

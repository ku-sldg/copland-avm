Require Import Term IO_Stubs Cvm_Run CvmJson CvmJson_Admits Example_Phrases_Admits.

Require Import AM_Monad StMonad_Coq Impl_appraisal privPolicy Manifest Manifest_Admits.


Require Import List.
Import ListNotations.



Definition am_check_auth_tok (t:Term) (fromPl:Plc) (authTok:ReqAuthTok) : AM AppResultC :=
  match authTok with
  | evc auth_ev auth_et => 
    appres <-
    (match (requester_bound t fromPl authTok) with
     | false => failm
     | true => gen_appraise_AM auth_et auth_ev
     end) ;;
    ret appres
  end.

Definition am_serve_auth_tok_req (t:Term) (fromPl : Plc) (myPl:Plc) 
                                 (authTok:ReqAuthTok) (init_ev:RawEv): AM RawEv :=
  let asdf := print_auth_tok authTok in
  v <- am_check_auth_tok t fromPl authTok ;;
  match (andb (requester_bound t fromPl authTok) (appraise_auth_tok v)) with
  | true =>
    match (privPolicy fromPl t) with
    | true => ret (* (run_cvm_json_full t init_ev *) (run_cvm_rawEv t myPl init_ev)
    | false => failm
    end
      
  | false => failm
  end.

Definition run_am_server_auth_tok_req (t:Term) (fromPlc:Plc) (myPl:Plc) 
            (authTok:ReqAuthTok) (init_ev:RawEv) : RawEv :=
              run_am_app_comp (am_serve_auth_tok_req t fromPlc myPl authTok init_ev) [].
                            

Definition do_cvm_session (req:CvmRequestMessage): CvmResponseMessage := 
  let fromPlc := default_place in 
  let myPlc := default_place in
  match req with 
  | REQ t tok ev => 
    let asdf := print_auth_tok tok in 
      let resev := run_am_server_auth_tok_req t fromPlc myPlc tok ev in 
        (RES resev)
  end.


Definition do_appraisal_session (appreq:AppraisalRequestMessage): 
                                AppraisalResponseMessage :=
  let appres := 
    match appreq with
    | REQ_APP t p et ev => 
        let expected_et := eval t p et in 
        let comp := gen_appraise_AM expected_et ev in 
          run_am_app_comp comp mtc_app
    end in 
      (RES_APP appres).




Definition evalJson (s:StringT) : JsonT :=
  let js := strToJson s in 
  let am_req := jsonToAmRequest js in 
  match am_req with 
  | CVM_REQ r => 
    let cvm_resp := (do_cvm_session r) in 
      responseToJson cvm_resp
  | APP_REQ appreq => 
    let app_resp := (do_appraisal_session appreq) in 
      appResponseToJson app_resp
  end.


Definition am_client_auth_tok_req (t:Term) (myPl:Plc) (init_ev:RawEv) 
                                  (app_bool:bool): AM AM_Result :=
  let auth_tok := mt_evc in 
  let att_res := am_sendReq t myPl auth_tok init_ev (* run_cvm_json_full t init_ev *) (* run_cvm_rawEv t myPl init_ev *) in
  match app_bool with
  | true => 
    let app_res := am_sendReq_app t myPl mt att_res in 
      ret (am_appev app_res)

  (*
      let att_et := eval t myPl mt in
        app_res <- gen_appraise_AM att_et att_res ;;
        ret (am_appev app_res)
  *)
  | false => ret (am_rawev att_res)
  end.

(*
Definition am_client_auth_tok_req (t:Term) (myPl:Plc) (init_ev:RawEv) (app_bool:bool): AM AppResultC :=
  match app_bool with
  | true => 
     v <- am_check_auth_tok t myPl mt_evc ;;
     match (andb (requester_bound t myPl mt_evc) (appraise_auth_tok v)) with
      | true =>
        match (privPolicy myPl t) with
        | true =>
          let att_res := run_cvm_rawEv t myPl init_ev in
          let att_et := eval t myPl mt in
          gen_appraise_AM att_et att_res
        | false => failm
        end
      
      | false => failm
     end
| false => ret mtc_app
end.
*)

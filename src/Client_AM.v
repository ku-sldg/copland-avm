(*  Implementation of a top-level Client (initiator) thread for Client AMs in
      end-to-end Copland Attestation + Appraisal protocols.  *)
Require Import String.

Require Import Term EqClass.

Require Import IO_Stubs AM_Monad ErrorStMonad_Coq.

Require Import Maps Attestation_Session Interface.

Require Import ErrorStringConstants Manifest_Admits.

Require Import AM_Helpers AppraisalSummary.

Import ListNotations ErrNotation.

Import ResultNotation.

Definition am_sendReq (att_sess : Attestation_Session) (req_plc : Plc) 
    (e : Evidence) (t:Term) (toPlc : Plc) : ResultT RawEv string :=
  let req := (mkPRReq att_sess req_plc e t) in 
  let m :=  Plc_Mapping att_sess in 
    match (map_get toPlc m) with 
    | None => errC errStr_remote_am_failure (* TODO: better errStr here *)
    | Some uuid =>  

      let js := to_JSON req in
      let resp_res := make_JSON_Network_Request uuid js in 
      match resp_res with 
      | errC msg => errC msg
      | resultC js_res => 
          match from_JSON js_res with
          | errC msg => errC msg
          | resultC res =>
            let '(mkPRResp success (evc ev _)) := res in
            if success then resultC ev else errC errStr_remote_am_failure
          end
      end
    end.

Definition am_client_app_summary (att_sess : Attestation_Session) (req_plc : Plc) 
(e : Evidence) (t:Term) (toPlc : Plc) : ResultT (AppraisalSummary * bool) string :=
  match (am_sendReq att_sess req_plc e t toPlc) with 
  | errC msg => errC msg 
  | resultC rawev => 
      let glob_ctx := (ats_context att_sess) in 
      match e with 
      | evc _ et => 
        et' <- eval glob_ctx toPlc et t ;;
        appsumm <- do_AppraisalSummary et' rawev glob_ctx ;;
        resultC (appsumm, (fold_appsumm appsumm))
      end
  end.
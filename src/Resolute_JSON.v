Require Import Interface_Types Stringifiable Term_Defs.
(* Require Import AppraisalSummary. *)
Require Import Resolute_Types ErrorStringConstants.
Require Export JSON List Maps EqClass JSON_Core ID_Type.
Import ListNotations ResultNotation.

Definition STR_RESOLUTE_CLIENT_ATTEST_ID : string := "ResClientReq_attest_id".
Definition STR_RESOLUTE_CLIENT_ATTEST_ARGS : string := "ResClientReq_attest_args".
Definition STR_RESOLUTE_CLIENT_RESULT_PATH : string := "ResClientReq_result_path".

Definition STR_RESOLUTE_CLIENT_RESULT_TERM : string := "ResClientResult_term".
Definition STR_RESOLUTE_CLIENT_RESULT_EVIDENCE : string := "ResClientResult_evidence".
Definition STR_RESOLUTE_CLIENT_RESULT_SUCCESS : string := "ResClientResult_success".
Definition STR_RESOLUTE_CLIENT_RESULT_ERROR : string := "ResClientResult_error".

Definition Resolute_Client_Request_to_JSON (req:Resolute_Client_Request) : JSON := 

  JSON_Object 
    [(STR_RESOLUTE_CLIENT_ATTEST_ID, (JSON_String (resclientreq_attest_id req)));
    (STR_RESOLUTE_CLIENT_ATTEST_ARGS, (resclientreq_args req));
    (STR_RESOLUTE_CLIENT_RESULT_PATH, (JSON_String (resclientreq_resultpath req)))].

Definition Resolute_Client_Request_from_JSON
(req:JSON) : ResultT Resolute_Client_Request string := 
  temp_attid <- JSON_get_string STR_RESOLUTE_CLIENT_ATTEST_ID req ;;
  temp_attargs <- JSON_get_Object STR_RESOLUTE_CLIENT_ATTEST_ARGS req ;;
  temp_attrespath <- JSON_get_string STR_RESOLUTE_CLIENT_RESULT_PATH req ;;

  resultC (mkResoluteClientReq temp_attid temp_attargs temp_attrespath).

Global Instance Jsonifiable_Resolute_Client_Request: Jsonifiable Resolute_Client_Request.
eapply Build_Jsonifiable with
(to_JSON := Resolute_Client_Request_to_JSON)
(from_JSON := Resolute_Client_Request_from_JSON); unfold Resolute_Client_Request_to_JSON; unfold Resolute_Client_Request_from_JSON; solve_json.
Defined.

Definition Resolute_Client_Response_to_JSON `{Jsonifiable Term, Jsonifiable Evidence, Jsonifiable bool} (res:Resolute_Client_Response) : JSON := 

  JSON_Object 
    [(STR_RESOLUTE_CLIENT_RESULT_TERM, (to_JSON (resclientres_term res)));
    (STR_RESOLUTE_CLIENT_RESULT_EVIDENCE, (to_JSON (resclientres_evidence res)));
    (STR_RESOLUTE_CLIENT_RESULT_SUCCESS, (JSON_Boolean (resclientres_success res)));
    (STR_RESOLUTE_CLIENT_RESULT_ERROR, (JSON_String (resclientres_error_str res)))].

Definition Resolute_Client_Response_from_JSON  `{Jsonifiable Term, Jsonifiable Evidence, Jsonifiable bool}
(res:JSON) : ResultT Resolute_Client_Response string := 
  temp_term <- JSON_get_Object STR_RESOLUTE_CLIENT_RESULT_TERM res ;;
  temp_evid <- JSON_get_Object STR_RESOLUTE_CLIENT_RESULT_EVIDENCE res ;;
  temp_succ <- JSON_get_bool STR_RESOLUTE_CLIENT_RESULT_SUCCESS res ;;
  temp_err  <- JSON_get_string STR_RESOLUTE_CLIENT_RESULT_ERROR res ;;

  term <- from_JSON temp_term ;;
  evid <- from_JSON temp_evid ;;

  resultC (mkResoluteClientResp term evid temp_succ temp_err).

Global Instance Jsonifiable_Resolute_Client_Response `{Jsonifiable Term, Jsonifiable Evidence, Jsonifiable bool} : Jsonifiable Resolute_Client_Response.
eapply Build_Jsonifiable with
(to_JSON := Resolute_Client_Response_to_JSON)
(from_JSON := Resolute_Client_Response_from_JSON); unfold Resolute_Client_Response_to_JSON; unfold Resolute_Client_Response_from_JSON; solve_json.
Defined.
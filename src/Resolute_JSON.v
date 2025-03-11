Require Import Interface_Types Stringifiable (* Attestation_Session *) Term_Defs.
(* Require Import AppraisalSummary. *)
Require Import Resolute_Logic Resolute_Types ErrorStringConstants.
Require Export JSON List Maps EqClass JSON_Core ID_Type.
Import ListNotations ResultNotation.

Definition STR_RESOLUTE_SUCCESS  : string := "RESOLUTE_POLICY_CHECK".
Definition STR_RESOLUTE_FORMULA  : string := "RESOLUTE_FORMULA".
Definition STR_RESOLUTE_EVIDENCE : string := "RESOLUTE_EVIDENCE".
Definition STR_RESOLUTE_JUDGEMENT : string := "RESOLUTE_JUDGEMENT".
Definition STR_RESOLUTE_TERM     : string := "RESOLUTE_TERM".

Definition STR_RESOLUTE : string := "RESOLUTE".
Definition r_false_name_constant : string := "R_False".
Definition r_true_name_constant : string := "R_True".
Definition r_goal_name_constant : string := "R_Goal".
Definition r_and_name_constant : string := "R_And".
Definition r_or_name_constant : string := "R_Or".
Definition r_imp_name_constant : string := "R_Imp".

Definition r_goal_e_name_constant : string := "R_Goal_E".
Definition r_and_e_name_constant : string := "R_And_E".
Definition r_or_e_name_constant : string := "R_Or_E".

Definition r_goal_t_name_constant : string := "R_Goal_T".
Definition r_and_t_name_constant : string := "R_And_T".
Definition r_or_t_name_constant : string := "R_Or_T".

Definition r_goal_j_name_constant : string := "R_Goal_J".
Definition r_and_j_name_constant : string := "R_And_J".
Definition r_or_j_name_constant : string := "R_Or_J".

Definition STR_RESOLUTE_CLIENT_ATTEST_ID : string := "ResClientReq_attest_id".
Definition STR_RESOLUTE_CLIENT_ATTEST_ARGS : string := "ResClientReq_attest_args".
Definition STR_RESOLUTE_CLIENT_RESULT_PATH : string := "ResClientReq_result_path".

Definition STR_RESOLUTE_CLIENT_RESPONSE_SUCCESS : string := "ResClientRespSuccess".

Definition STR_RESOLUTE_CLIENT_RESULT_TERM : string := "ResClientResult_term".
Definition STR_RESOLUTE_CLIENT_RESULT_EVIDENCE : string := "ResClientResult_evidence".
Definition STR_RESOLUTE_CLIENT_RESULT_SUCCESS : string := "ResClientResult_success".
Definition STR_RESOLUTE_CLIENT_RESULT_ERROR : string := "ResClientResult_error".

Fixpoint Resolute_to_JSON (t : Resolute_Formula)  : JSON := 
  match t with
  | R_Goal tid args => constructor_to_JSON STR_RESOLUTE_FORMULA r_goal_name_constant [JSON_String (to_string tid); (to_JSON args)]
  | R_And t1 t2 => constructor_to_JSON STR_RESOLUTE_FORMULA r_and_name_constant
  [(Resolute_to_JSON t1); (Resolute_to_JSON t2)]
  | R_Or t1 t2 => constructor_to_JSON STR_RESOLUTE_FORMULA r_or_name_constant
  [(Resolute_to_JSON t1); (Resolute_to_JSON t2)]
  end.

Open Scope string_scope.

Fixpoint Resolute_from_JSON (js : JSON) : ResultT Resolute_Formula string :=
    let type_name := STR_RESOLUTE_FORMULA in
    let type_str := type_name ++ type_sep ++ type_string_constant in
    let body_str := type_name ++ type_sep ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | resultC (JSON_String cons_name) =>

      if (eqb cons_name r_goal_name_constant) 
      then 
      match (JSON_get_Object body_str js) with 
      | resultC (JSON_Array
                  [(JSON_String n_js); args_js]) =>
          n <- from_string n_js ;;
          args <- from_JSON args_js ;;
          resultC (R_Goal n args)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else if (eqb cons_name r_and_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
          ] =>
            term1_val <- (Resolute_from_JSON term1) ;;
            term2_val <- (Resolute_from_JSON term2) ;;
            resultC (R_And term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else if (eqb cons_name r_or_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
          ] =>
            term1_val <- (Resolute_from_JSON term1) ;;
            term2_val <- (Resolute_from_JSON term2) ;;
            resultC (R_Or term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else errC err_str_json_invalid_constructor_name
    | resultC _ => errC err_str_json_invalid_constructor_name
    | errC e => errC e
    end.

Fixpoint Resolute_Evidence_to_JSON `{Jsonifiable Evidence} (t : Resolute_Evidence)  : JSON := 
  match t with
  | R_Goal_E tid args e => constructor_to_JSON STR_RESOLUTE_EVIDENCE r_goal_e_name_constant [JSON_String (to_string tid); (to_JSON args); (to_JSON e)]
  | R_And_E t1 t2 => constructor_to_JSON STR_RESOLUTE_EVIDENCE r_and_e_name_constant
  [(Resolute_Evidence_to_JSON t1); (Resolute_Evidence_to_JSON t2)]
  | R_Or_E t1 t2 => constructor_to_JSON STR_RESOLUTE_EVIDENCE r_or_e_name_constant
  [(Resolute_Evidence_to_JSON t1); (Resolute_Evidence_to_JSON t2)]
  end.
    
Fixpoint Resolute_Evidence_from_JSON `{Jsonifiable Evidence} (js : JSON) : ResultT Resolute_Evidence string :=
    let type_name := STR_RESOLUTE_EVIDENCE in
    let type_str := type_name ++ type_sep ++ type_string_constant in
    let body_str := type_name ++ type_sep ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | resultC (JSON_String cons_name) =>

      if (eqb cons_name r_goal_e_name_constant) 
      then 
      match (JSON_get_Object body_str js) with 
      | resultC (JSON_Array
                  [(JSON_String n_js); args_js; e_js]) =>
          n <- from_string n_js ;;
          args <- from_JSON args_js ;;
          e <- from_JSON e_js ;;
          resultC (R_Goal_E n args e)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else if (eqb cons_name r_and_e_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
          ] =>
            term1_val <- (Resolute_Evidence_from_JSON term1) ;;
            term2_val <- (Resolute_Evidence_from_JSON term2) ;;
            resultC (R_And_E term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else if (eqb cons_name r_or_e_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
          ] =>
            term1_val <- (Resolute_Evidence_from_JSON term1) ;;
            term2_val <- (Resolute_Evidence_from_JSON term2) ;;
            resultC (R_Or_E term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else errC err_str_json_invalid_constructor_name
    | resultC _ => errC err_str_json_invalid_constructor_name
    | errC e => errC e
    end.

Fixpoint Resolute_Term_to_JSON `{Jsonifiable Term} (t : Resolute_Term)  : JSON := 
  match t with
  | R_Goal_T tid args t => constructor_to_JSON STR_RESOLUTE_TERM r_goal_t_name_constant [JSON_String (to_string tid); (to_JSON args); (to_JSON t)]
  | R_And_T t1 t2 => constructor_to_JSON STR_RESOLUTE_TERM r_and_t_name_constant
  [(Resolute_Term_to_JSON t1); (Resolute_Term_to_JSON t2)]
  | R_Or_T t1 t2 => constructor_to_JSON STR_RESOLUTE_TERM r_or_t_name_constant
  [(Resolute_Term_to_JSON t1); (Resolute_Term_to_JSON t2)]
  end.
    
Fixpoint Resolute_Term_from_JSON `{Jsonifiable Term} (js : JSON) : ResultT Resolute_Term string :=
    let type_name := STR_RESOLUTE_TERM in
    let type_str := type_name ++ type_sep ++ type_string_constant in
    let body_str := type_name ++ type_sep ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | resultC (JSON_String cons_name) =>

      if (eqb cons_name r_goal_t_name_constant) 
      then 
      match (JSON_get_Object body_str js) with 
      | resultC (JSON_Array
                  [(JSON_String n_js); args_js; t_js]) =>
          n <- from_string n_js ;;
          args <- from_JSON args_js ;;
          t <- from_JSON t_js ;;
          resultC (R_Goal_T n args t)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else if (eqb cons_name r_and_t_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
          ] =>
            term1_val <- (Resolute_Term_from_JSON term1) ;;
            term2_val <- (Resolute_Term_from_JSON term2) ;;
            resultC (R_And_T term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else if (eqb cons_name r_or_t_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
          ] =>
            term1_val <- (Resolute_Term_from_JSON term1) ;;
            term2_val <- (Resolute_Term_from_JSON term2) ;;
            resultC (R_Or_T term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else errC err_str_json_invalid_constructor_name
    | resultC _ => errC err_str_json_invalid_constructor_name
    | errC e => errC e
    end.

Fixpoint Resolute_Judgement_to_JSON `{Jsonifiable bool} (t : Resolute_Judgement)  : JSON := 
  match t with
  | R_Goal_J tid args e => constructor_to_JSON STR_RESOLUTE_JUDGEMENT r_goal_j_name_constant [JSON_String (to_string tid); (to_JSON args); (to_JSON e)]
  | R_And_J t1 t2 => constructor_to_JSON STR_RESOLUTE_JUDGEMENT r_and_j_name_constant
  [(Resolute_Judgement_to_JSON t1); (Resolute_Judgement_to_JSON t2)]
  | R_Or_J t1 t2 => constructor_to_JSON STR_RESOLUTE_JUDGEMENT r_or_j_name_constant
  [(Resolute_Judgement_to_JSON t1); (Resolute_Judgement_to_JSON t2)]
  end.
        
Fixpoint Resolute_Judgement_from_JSON `{Jsonifiable bool} (js : JSON) : ResultT Resolute_Judgement string :=
    let type_name := STR_RESOLUTE_JUDGEMENT in
    let type_str := type_name ++ type_sep ++ type_string_constant in
    let body_str := type_name ++ type_sep ++ body_string_constant in
    match (JSON_get_Object type_str js) with
    | resultC (JSON_String cons_name) =>

      if (eqb cons_name r_goal_j_name_constant) 
      then 
      match (JSON_get_Object body_str js) with 
      | resultC (JSON_Array
                  [(JSON_String n_js); args_js; jt_js]) =>
          n <- from_string n_js ;;
          args <- from_JSON args_js ;;
          jt <- from_JSON jt_js ;;
          resultC (R_Goal_J n args jt)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else if (eqb cons_name r_and_j_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
          ] =>
            term1_val <- (Resolute_Judgement_from_JSON term1) ;;
            term2_val <- (Resolute_Judgement_from_JSON term2) ;;
            resultC (R_And_J term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else if (eqb cons_name r_or_j_name_constant) 
      then match js with
        | JSON_Object [
            _;
            (_, JSON_Array [ term1; term2 ])
          ] =>
            term1_val <- (Resolute_Judgement_from_JSON term1) ;;
            term2_val <- (Resolute_Judgement_from_JSON term2) ;;
            resultC (R_Or_J term1_val term2_val)
        | _ => errC err_str_json_parsing_failure_wrong_number_args
        end

      else errC err_str_json_invalid_constructor_name
    | resultC _ => errC err_str_json_invalid_constructor_name
    | errC e => errC e
    end.

Close Scope string_scope.

Global Instance Jsonifiable_Resolute : Jsonifiable Resolute_Formula. 
eapply Build_Jsonifiable with (to_JSON := Resolute_to_JSON) (from_JSON := Resolute_from_JSON).
induction a; 
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *; eauto).
Defined.

Global Instance Jsonifiable_Resolute_Evidence `{Jsonifiable Evidence} : Jsonifiable Resolute_Evidence. 
eapply Build_Jsonifiable with (to_JSON := Resolute_Evidence_to_JSON) (from_JSON := Resolute_Evidence_from_JSON).
induction a; 
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *; eauto).
Defined.

Global Instance Jsonifiable_Resolute_Term `{Jsonifiable Term} : Jsonifiable Resolute_Term. 
eapply Build_Jsonifiable with (to_JSON := Resolute_Term_to_JSON) (from_JSON := Resolute_Term_from_JSON).
induction a; 
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *; eauto).
Defined.

Global Instance Jsonifiable_Resolute_Judgement `{Jsonifiable bool} : Jsonifiable Resolute_Judgement. 
eapply Build_Jsonifiable with (to_JSON := Resolute_Judgement_to_JSON) (from_JSON := Resolute_Judgement_from_JSON).
induction a; 
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *; eauto).
Defined.

(*
Definition STR_RESOLUTE_CLIENT_ATTEST_ID : string := "ResClientReq_attest_id".
Definition STR_RESOLUTE_CLIENT_ATTEST_ARGS : string := "ResClientReq_attest_args".
Definition STR_RESOLUTE_CLIENT_RESULT_PATH : string := "ResClientReq_result_path".
*)

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

Definition Resolute_Client_Response_to_JSON (resp:Resolute_Client_Response) : JSON := 

  JSON_Object 
    [(STR_RESOLUTE_CLIENT_RESPONSE_SUCCESS, (JSON_Boolean (resclientresp_success resp)))
    ].

Definition Resolute_Client_Response_from_JSON
(resp:JSON) : ResultT Resolute_Client_Response string := 
  temp_attid <- JSON_get_bool STR_RESOLUTE_CLIENT_RESPONSE_SUCCESS resp ;;
  
  resultC ( mkResoluteClientResp temp_attid).

Global Instance Jsonifiable_Resolute_Client_Response : Jsonifiable Resolute_Client_Response.
eapply Build_Jsonifiable with
(to_JSON := Resolute_Client_Response_to_JSON)
(from_JSON := Resolute_Client_Response_from_JSON); unfold Resolute_Client_Response_to_JSON; unfold Resolute_Client_Response_from_JSON; solve_json.
Defined.

(*
Definition STR_RESOLUTE_CLIENT_RESULT_TERM : string := "ResClientResult_term".
Definition STR_RESOLUTE_CLIENT_RESULT_EVIDENCE : string := "ResClientResult_evidence".
Definition STR_RESOLUTE_CLIENT_RESULT_SUCCESS : string := "ResClientResult_success".
Definition STR_RESOLUTE_CLIENT_RESULT_ERROR : string := "ResClientResult_error".
*)

Definition Resolute_Client_Result_to_JSON `{Jsonifiable Term, Jsonifiable Evidence, Jsonifiable bool} (res:Resolute_Client_Result) : JSON := 

  JSON_Object 
    [(STR_RESOLUTE_CLIENT_RESULT_TERM, (to_JSON (resclientres_term res)));
    (STR_RESOLUTE_CLIENT_RESULT_EVIDENCE, (to_JSON (resclientres_evidence res)));
    (STR_RESOLUTE_CLIENT_RESULT_SUCCESS, (JSON_Boolean (resclientres_success res)));
    (STR_RESOLUTE_CLIENT_RESULT_ERROR, (JSON_String (resclientres_error_str res)))].

Definition Resolute_Client_Result_from_JSON  `{Jsonifiable Term, Jsonifiable Evidence, Jsonifiable bool}
(res:JSON) : ResultT Resolute_Client_Result string := 
  temp_term <- JSON_get_Object STR_RESOLUTE_CLIENT_RESULT_TERM res ;;
  temp_evid <- JSON_get_Object STR_RESOLUTE_CLIENT_RESULT_EVIDENCE res ;;
  temp_succ <- JSON_get_bool STR_RESOLUTE_CLIENT_RESULT_SUCCESS res ;;
  temp_err  <- JSON_get_string STR_RESOLUTE_CLIENT_RESULT_ERROR res ;;

  term <- from_JSON temp_term ;;
  evid <- from_JSON temp_evid ;;

  resultC (mkResoluteClientResult term evid temp_succ temp_err).

Global Instance Jsonifiable_Resolute_Client_Result  `{Jsonifiable Term, Jsonifiable Evidence, Jsonifiable bool} : Jsonifiable Resolute_Client_Result.
eapply Build_Jsonifiable with
(to_JSON := Resolute_Client_Result_to_JSON)
(from_JSON := Resolute_Client_Result_from_JSON); unfold Resolute_Client_Result_to_JSON; unfold Resolute_Client_Result_from_JSON; solve_json.
Defined.














Definition ResoluteResponse_to_JSON `{Jsonifiable Resolute_Term, Jsonifiable Resolute_Formula, Jsonifiable Resolute_Judgement} (resp:ResoluteResponse) : JSON := 

  JSON_Object 
    [(STR_RESOLUTE_JUDGEMENT, (to_JSON (resoluteresp_judgement resp)));
    (STR_RESOLUTE_FORMULA, (to_JSON (resoluteresp_formula resp)));
    (STR_RESOLUTE_TERM, (to_JSON (resoluteresp_term resp)))].

Definition ResoluteResponse_from_JSON `{Jsonifiable Resolute_Term, Jsonifiable Resolute_Formula, Jsonifiable Resolute_Judgement}
(resp:JSON) : ResultT ResoluteResponse string := 
  temp_success <- JSON_get_Object STR_RESOLUTE_JUDGEMENT resp ;;
  temp_formula <- JSON_get_Object STR_RESOLUTE_FORMULA resp ;;
  temp_term <- JSON_get_Object STR_RESOLUTE_TERM resp ;;

  judgement <- from_JSON temp_success ;;
  formula <- from_JSON temp_formula ;;
  term <- from_JSON temp_term ;;
  resultC (mkResoluteResp judgement formula term).

Global Instance Jsonifiable_ResoluteResponse `{Jsonifiable Resolute_Judgement, Jsonifiable Resolute_Term, Jsonifiable Resolute_Formula}: Jsonifiable ResoluteResponse.
eapply Build_Jsonifiable with
(to_JSON := ResoluteResponse_to_JSON)
(from_JSON := ResoluteResponse_from_JSON); unfold ResoluteResponse_to_JSON; unfold ResoluteResponse_from_JSON; solve_json.
Defined.

(*
Definition test_resolute_resp_compute_json `{Jsonifiable ResoluteResponse} (x:ResoluteResponse) : JSON := to_JSON x.
*)


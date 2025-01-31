Require Import Interface_Types Stringifiable (* Attestation_Session *) Term_Defs.
(* Require Import AppraisalSummary. *)
Require Import Resolute_Logic Resolute_Types ErrorStringConstants.
Require Export JSON List Maps EqClass JSON_Core ID_Type.
Import ListNotations ResultNotation.

Definition STR_RESOLUTE_SUCCESS : string := "RESOLUTE_POLICY_CHECK".
Definition STR_RESOLUTE_FORMULA : string := "RESOLUTE_FORMULA".
Definition STR_RESOLUTE_EVIDENCE : string := "RESOLUTE_EVIDENCE".

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

Close Scope string_scope.

Global Instance Jsonifiable_Resolute : Jsonifiable Resolute_Formula. 
eapply Build_Jsonifiable with (to_JSON := Resolute_to_JSON) (from_JSON := Resolute_from_JSON).
induction a; 
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *; eauto).
Defined.

Global Instance Jsonifiable_Resolute_Evidence : Jsonifiable Resolute_Evidence. 
eapply Build_Jsonifiable with (to_JSON := Resolute_Evidence_to_JSON) (from_JSON := Resolute_Evidence_from_JSON).
induction a; 
repeat (result_monad_unfold;
jsonifiable_hammer; repeat rewrite canonical_jsonification in *; eauto).
Defined.

Definition ResoluteResponse_to_JSON `{Jsonifiable Term, Jsonifiable Resolute_Formula} (resp:ResoluteResponse) : JSON := 

  JSON_Object 
    [(STR_RESOLUTE_SUCCESS, (JSON_Boolean (resoluteresp_success resp)));
    (STR_RESOLUTE_FORMULA, (to_JSON (resoluteresp_formula resp)));
    (STR_TERM, (to_JSON (resoluteresp_term resp)))].

Definition ResoluteResponse_from_JSON `{Jsonifiable Term, Jsonifiable Resolute_Formula}
(resp:JSON) : ResultT ResoluteResponse string := 
  temp_success <- JSON_get_bool STR_RESOLUTE_SUCCESS resp ;;
  temp_formula <- JSON_get_Object STR_RESOLUTE_FORMULA resp ;;
  temp_term <- JSON_get_Object STR_TERM resp ;;

  formula <- from_JSON temp_formula ;;
  term <- from_JSON temp_term ;;
  resultC (mkResoluteResp temp_success formula term).


Global Instance Jsonifiable_ResoluteResponse `{Jsonifiable Term, Jsonifiable Resolute_Formula}: Jsonifiable ResoluteResponse.
eapply Build_Jsonifiable with
(to_JSON := ResoluteResponse_to_JSON)
(from_JSON := ResoluteResponse_from_JSON); unfold ResoluteResponse_to_JSON; unfold ResoluteResponse_from_JSON; solve_json.
Defined.

Definition test_resolute_resp_compute_json (x:ResoluteResponse) : JSON := to_JSON x.


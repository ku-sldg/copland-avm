(* Abstract place-holders for error string constant definitions.
    Once instantiated, these should provide descriptive error messages for 
    dynamic error cases in Coq-extracted code. *)

Require Import String.

Definition empty_string : string := "empty_string".

Definition errStr_amNonce : string := "errStr_amNonce".

Definition errStr_peel_bs_am : string := "errStr_peel_bs_am".

Definition errStr_peel_n_am : string := "errStr_peel_n_am".

Definition errStr_requester_bound : string := "errStr_requester_bound".

Definition errStr_disclosePolicy : string := "errStr_disclosePolicy".

Definition errStr_app_auth_tok : string := "errStr_app_auth_tok".

Definition errStr_dispatch_error : string := "errStr_dispatch_error".

Definition errStr_cvm_error : string := "errStr_cvm_error".

Definition errStr_decryption_prim : string := "errStr_decryption_prim".

Definition errStr_et_size : string := "errStr_et_size".

Definition errStr_lib_supports_man_check : string := "errStr_lib_supports_man_check".

Definition errStr_lib_supports_man_app_check : string := "errStr_lib_supports_man_app_check".

(* Evidence Bundling Errors *)
Definition errStr_empty_raw_ev : string := "errStr_empty_raw_ev".

Definition errStr_raw_evidence_too_long : string := "errStr_raw_evidence_too_long".

Definition errStr_raw_evidence_wrong_length_comp : string := "errStr_raw_evidence_wrong_length_comp".

(* JSON Interface Error String *)
Definition errStr_remote_am_failure : string := "errStr_remote_am_failure".

Definition errStr_incorrect_resp_type : string := "errStr_incorrect_resp_type".

Definition errStr_json_parsing : string := "errStr_json_parsing".

Definition errStr_invalid_request_type : string := "errStr_invalid_request_type".

Definition errStr_negotiation_not_implemented : string := "errStr_negotiation_not_implemented".

(* Run CVM Error Strings *)
Definition errStr_run_cvm_at_error_dynamic : string := "errStr_run_cvm_at_error_dynamic".

Definition errStr_run_cvm_at_error_static : string := "errStr_run_cvm_at_error_static".

Definition errStr_run_cvm_dispatch_unavailable : string := "errStr_run_cvm_dispatch_unavailable".

(* JSON Converter Strings *)
Definition errStr_json_to_manifest_set : string := "errStr_json_to_manifest_set".

Definition errStr_json_to_map : string := "errStr_json_to_map".

Definition errStr_json_to_id_type : string := "errStr_json_to_id_type".

Definition errStr_json_to_manifest : string := "errStr_json_to_manifest".

Definition errStr_json_to_ASP_Locator : string := "errStr_json_to_ASP_Locator".

Definition errStr_json_to_am_lib : string := "errStr_json_to_am_lib".

Definition errStr_json_to_pair : string := "errStr_json_to_pair".

Definition errStr_JSON_get_Object_key_not_found : string := "errStr_JSON_get_Object_key_not_found".
Definition errStr_JSON_get_Object_not_a_json : string := "errStr_JSON_get_Object_not_a_json".

Definition errStr_json_get_array_key_not_found : string := "errStr_json_get_array_key_not_found".
Definition errStr_json_get_array_not_an_array : string := "errStr_json_get_array_not_an_array".

Definition errStr_json_get_string_key_not_found : string := "errStr_json_get_string_key_not_found".
Definition errStr_json_get_string_not_a_string : string := "errStr_json_get_string_not_a_string".

Definition errStr_json_get_bool_key_not_found : string := "errStr_json_get_bool_key_not_found".
Definition errStr_json_get_bool_not_a_bool : string := "errStr_json_get_bool_not_a_bool".


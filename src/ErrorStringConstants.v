(* Abstract place-holders for error string constant definitions.
    Once instantiated, these should provide descriptive error messages for 
    dynamic error cases in Coq-extracted code. *)

Require Import String.
Open Scope string_scope.

(* Global Context Errors *)
Definition err_str_asp_no_type_sig := "ASP Type signature not found in the Global Context".

Definition err_str_asp_no_compat_appr_asp := "Compatible Appraisal ASP not found in Global Context".


(* AM and CVM Errors *)
Definition empty_string := "empty_string".

Definition errStr_amNonce := "errStr_amNonce".

Definition errStr_peel_bs_am := "errStr_peel_bs_am".

Definition errStr_peel_n_am := "errStr_peel_n_am".

Definition errStr_requester_bound := "errStr_requester_bound".

Definition errStr_disclosePolicy := "errStr_disclosePolicy".

Definition errStr_app_auth_tok := "errStr_app_auth_tok".

Definition errStr_dispatch_error := "errStr_dispatch_error".

Definition errStr_cvm_error := "errStr_cvm_error".

Definition errStr_decryption_prim := "errStr_decryption_prim".

Definition errStr_et_size := "errStr_et_size".

Definition errStr_lib_supports_man_check := "errStr_lib_supports_man_check".

Definition errStr_lib_supports_man_app_check := "errStr_lib_supports_man_app_check".

(* EvidenceT Bundling Errors *)
Definition errStr_empty_raw_ev := "errStr_empty_raw_ev".

Definition errStr_raw_EvidenceT_too_long := "errStr_raw_EvidenceT_too_long".

Definition errStr_raw_EvidenceT_wrong_length_comp := "errStr_raw_EvidenceT_wrong_length_comp".

(* JSON Interface Error String *)
Definition errStr_remote_am_failure := "errStr_remote_am_failure".

Definition errStr_incorrect_resp_type := "errStr_incorrect_resp_type".

Definition errStr_json_parsing := "errStr_json_parsing".

Definition errStr_invalid_request_type := "errStr_invalid_request_type".

Definition errStr_negotiation_not_implemented := "errStr_negotiation_not_implemented".

(* Run CVM Error Strings *)
Definition errStr_run_cvm_at_error_dynamic := "errStr_run_cvm_at_error_dynamic".

Definition errStr_run_cvm_at_error_static := "errStr_run_cvm_at_error_static".

Definition errStr_run_cvm_dispatch_unavailable := "errStr_run_cvm_dispatch_unavailable".

(* JSON Converter Strings *)
Definition errStr_json_to_manifest_set := "errStr_json_to_manifest_set".

Definition errStr_json_to_map := "errStr_json_to_map".

Definition errStr_json_to_id_type := "errStr_json_to_id_type".

Definition errStr_json_to_manifest := "errStr_json_to_manifest".

Definition errStr_json_to_ASP_Locator := "errStr_json_to_ASP_Locator".

Definition errStr_json_to_am_lib := "errStr_json_to_am_lib".

Definition errStr_json_to_pair := "errStr_json_to_pair".

Definition errStr_JSON_get_Object_key_not_found := "errStr_JSON_get_Object_key_not_found".
Definition errStr_JSON_get_Object_not_a_json := "errStr_JSON_get_Object_not_a_json".

Definition errStr_json_get_array_key_not_found := "errStr_json_get_array_key_not_found".
Definition errStr_json_get_array_not_an_array := "errStr_json_get_array_not_an_array".

Definition errStr_json_get_string_key_not_found := "errStr_json_get_string_key_not_found".
Definition errStr_json_get_string_not_a_string := "errStr_json_get_string_not_a_string".

Definition errStr_json_get_bool_key_not_found := "errStr_json_get_bool_key_not_found".
Definition errStr_json_get_bool_not_a_bool := "errStr_json_get_bool_not_a_bool".

Close Scope string_scope.


(* Abstract place-holders for error string constant definitions.
    Once instantiated, these should provide descriptive error messages for 
    dynamic error cases in Coq-extracted code. *)

Require Import String.

Definition empty_string : string. Admitted.

Definition errStr_amNonce : string. Admitted.

Definition errStr_peel_bs_am : string. Admitted.

Definition errStr_peel_n_am : string. Admitted.

Definition errStr_requester_bound : string. Admitted.

Definition errStr_disclosePolicy : string. Admitted.

Definition errStr_app_auth_tok : string. Admitted.

Definition errStr_dispatch_error : string. Admitted.

Definition errStr_cvm_error : string. Admitted.

Definition errStr_decryption_prim : string. Admitted.

Definition errStr_et_size : string. Admitted.

Definition errStr_lib_supports_man_check : string. Admitted.

Definition errStr_lib_supports_man_app_check : string. Admitted.

(* Evidence Bundling Errors *)
Definition errStr_empty_raw_ev : string. Admitted.

Definition errStr_raw_evidence_too_long : string. Admitted.

Definition errStr_raw_evidence_wrong_length_comp : string. Admitted.

(* JSON Interface Error String *)
Definition errStr_remote_am_failure : string. Admitted.

Definition errStr_incorrect_resp_type : string. Admitted.

Definition errStr_json_parsing : string. Admitted.

Definition errStr_invalid_request_type : string. Admitted.

Definition errStr_negotiation_not_implemented : string. Admitted.

(* Run CVM Error Strings *)
Definition errStr_run_cvm_at_error_dynamic : string. Admitted.

Definition errStr_run_cvm_at_error_static : string. Admitted.

Definition errStr_run_cvm_dispatch_unavailable : string. Admitted.

(* JSON Converter Strings *)
Definition errStr_json_to_manifest_set : string. Admitted.

Definition errStr_json_to_map : string. Admitted.

Definition errStr_json_to_id_type : string. Admitted.

Definition errStr_json_to_manifest : string. Admitted.

Definition errStr_json_to_ASP_Locator : string. Admitted.

Definition errStr_json_to_am_lib : string. Admitted.

Definition errStr_json_to_pair : string. Admitted.
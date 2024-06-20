(* Abstract place-holders for error string constant definitions.
    Once instantiated, these should provide descriptive error messages for 
    dynamic error cases in Coq-extracted code. *)

Require Import StringT.

Definition empty_string : StringT. Admitted.

Definition errStr_amNonce : StringT. Admitted.

Definition errStr_peel_bs_am : StringT. Admitted.

Definition errStr_peel_n_am : StringT. Admitted.

Definition errStr_requester_bound : StringT. Admitted.

Definition errStr_disclosePolicy : StringT. Admitted.

Definition errStr_app_auth_tok : StringT. Admitted.

Definition errStr_dispatch_error : StringT. Admitted.

Definition errStr_cvm_error : StringT. Admitted.

Definition errStr_decryption_prim : StringT. Admitted.

Definition errStr_et_size : StringT. Admitted.

Definition errStr_lib_supports_man_check : StringT. Admitted.

Definition errStr_lib_supports_man_app_check : StringT. Admitted.

(* Evidence Bundling Errors *)
Definition errStr_empty_raw_ev : StringT. Admitted.

Definition errStr_raw_evidence_too_long : StringT. Admitted.

Definition errStr_raw_evidence_wrong_length_comp : StringT. Admitted.

(* JSON Interface Error String *)
Definition errStr_remote_am_failure : StringT. Admitted.

Definition errStr_incorrect_resp_type : StringT. Admitted.

Definition errStr_json_parsing : StringT. Admitted.

Definition errStr_invalid_request_type : StringT. Admitted.

Definition errStr_negotiation_not_implemented : StringT. Admitted.

(* Run CVM Error Strings *)
Definition errStr_run_cvm_at_error_dynamic : StringT. Admitted.

Definition errStr_run_cvm_at_error_static : StringT. Admitted.

Definition errStr_run_cvm_dispatch_unavailable : StringT. Admitted.
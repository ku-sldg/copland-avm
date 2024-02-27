(* Abstract place-holders for error string constant definitions.
    Once instantiated, these should provide descriptive error messages for 
    dynamic error cases in Coq-extracted code. *)

Require Import StringT.

Definition empty_string : StringT. Admitted.

Definition errStr_amNonce : StringT. Admitted.

Definition errStr_peel_bs_am : StringT. Admitted.

Definition errStr_requester_bound : StringT. Admitted.

Definition errStr_disclosePolicy : StringT. Admitted.

Definition errStr_app_auth_tok : StringT. Admitted.

Definition errStr_dispatch_error : StringT. Admitted.

Definition errStr_cvm_error : StringT. Admitted.

Definition errStr_decryption_prim : StringT. Admitted.

Definition errStr_et_size : StringT. Admitted.

Definition errStr_lib_supports_man_check : StringT. Admitted.

Definition errStr_lib_supports_man_app_check : StringT. Admitted.
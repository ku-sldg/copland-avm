
(** Abstract definitions for cryptographic ASP parameters.
        These act as default parameters to cryptographic functions (e.g. signing, hashing)
        that should be instantiated on a per-AM/per-platform basis. *)

Require Import Term_Defs_Core.
Require Import String.

Definition sig_aspid : ASP_ID. Admitted.
Definition sig_aspargs : ASP_ARGS. Admitted.
Definition sig_params : ASP_PARAMS := asp_paramsC sig_aspid sig_aspargs.

Definition check_nonce_aspid : ASP_ID. Admitted.
Definition check_nonce_aspargs : ASP_ARGS. Admitted.
Definition check_nonce_params : ASP_PARAMS :=
    asp_paramsC check_nonce_aspid check_nonce_aspargs.

Definition hsh_aspid : ASP_ID. Admitted.
Definition hsh_aspargs : ASP_ARGS. Admitted.
Definition hsh_params : ASP_PARAMS := asp_paramsC hsh_aspid hsh_aspargs.

Definition enc_aspid : ASP_ID. Admitted.
Definition enc_aspargs : ASP_ARGS. Admitted.
Definition enc_params : Plc -> ASP_PARAMS :=
  fun enc_targplc => asp_paramsC enc_aspid (cons ("TARG_PLC"%string, enc_targplc) enc_aspargs).


(* This is an (for now, somewhat ad-hoc) ASP EvidenceT disclosure predicate.
    TODO:  move this somewhere more logical??  *)
Definition term_discloses_aspid_to_remote_enc_bool (t:Term) (p:Plc) (e:EvidenceT) (i:ASP_ID) (r:Plc) : bool.
Admitted.
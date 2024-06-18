
(** Abstract definitions for cryptographic ASP parameters.
        These act as default parameters to cryptographic functions (e.g. signing, hashing)
        that should be instantiated on a per-AM/per-platform basis. *)

Require Import Term_Defs_Core.

Definition sig_aspid : ASP_ID. Admitted.

Definition sig_aspargs : ASP_ARGS. Admitted.

Definition sig_targid : ASP_ID. Admitted.

Definition sig_targplc : Plc. Admitted.

Definition sig_params : ASP_PARAMS :=
    asp_paramsC sig_aspid sig_aspargs sig_targplc sig_targid.


Definition hsh_aspid : ASP_ID. Admitted.

Definition hsh_aspargs : ASP_ARGS. Admitted.

Definition hsh_targid : ASP_ID. Admitted.

Definition hsh_targplc : Plc. Admitted.
    
Definition hsh_params : ASP_PARAMS :=
    asp_paramsC hsh_aspid hsh_aspargs hsh_targplc hsh_targid.


Definition enc_aspid : ASP_ID. Admitted.

Definition enc_aspargs : ASP_ARGS. Admitted.

Definition enc_targid : ASP_ID. Admitted.

Definition enc_params : Plc -> ASP_PARAMS :=
  fun enc_targplc => asp_paramsC enc_aspid enc_aspargs enc_targplc enc_targid.


(* This is an (for now, somewhat ad-hoc) ASP evidence disclosure predicate.
    TODO:  move this somewhere more logical??  *)
Definition term_discloses_aspid_to_remote_enc_bool (t:Term) (p:Plc) (e:Evidence) (i:ASP_ID) (r:Plc) : bool.
Admitted.
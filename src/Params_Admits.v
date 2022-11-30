Require Import Term_Defs_Core.


(** Abstract definitions for signing and hashing parameters.  
    May instantiate these during compilation in the future. *)
Definition sig_params : ASP_PARAMS.
Admitted.
Definition hsh_params : ASP_PARAMS.
Admitted.

Definition enc_params : Plc -> ASP_PARAMS.
Admitted.

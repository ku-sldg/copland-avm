Require Import Term_Defs_Core.


(** Abstract definitions for signing and hashing parameters.  
    May instantiate these during compilation in the future. *)

Definition sig_aspid : ASP_ID.
Admitted.

Definition sig_aspargs : list Arg.
Admitted.

Definition sig_targid : ASP_ID.
Admitted.

Definition sig_targplc : Plc.
Admitted.

Definition sig_params : ASP_PARAMS :=
    asp_paramsC sig_aspid sig_aspargs sig_targplc sig_targid.



Definition hsh_params : ASP_PARAMS.
Admitted.

Definition enc_params : Plc -> ASP_PARAMS.
Admitted.

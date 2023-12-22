Require Import Term_Defs_Core.

Require Import List.
Import ListNotations.


(** Abstract definitions for signing and hashing parameters.  
    May instantiate these during compilation in the future. *)

Definition default_place : Plc := O. 

Definition sig_aspid : ASP_ID := O.

Definition sig_aspargs : list Arg := [].

Definition sig_targid : ASP_ID := O.

Definition sig_targplc : Plc := O.

Definition sig_params : ASP_PARAMS :=
    asp_paramsC sig_aspid sig_aspargs sig_targplc sig_targid.


Definition hsh_aspid : ASP_ID := O.

Definition hsh_aspargs : list Arg := [].

Definition hsh_targid : ASP_ID := O.

Definition hsh_targplc : Plc := O.
    
Definition hsh_params : ASP_PARAMS :=
    asp_paramsC hsh_aspid hsh_aspargs hsh_targplc hsh_targid.


Definition enc_aspid : ASP_ID := O.

Definition enc_aspargs : list Arg := [].

Definition enc_targid : ASP_ID := O.

Definition enc_params : Plc -> ASP_PARAMS :=
  fun enc_targplc => asp_paramsC enc_aspid enc_aspargs enc_targplc enc_targid.


(* TODO:  move this somewhere more logical??  *)
Definition term_discloses_aspid_to_remote_enc_bool (t:Term) (p:Plc) (e:Evidence) (i:ASP_ID) (r:Plc) : bool := false.
(*
Record representing the AM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Maps EqClass ConcreteEvidence.

Require Import List.
Import ListNotations.

Definition asp_map := MapC (Plc * ASP_ID) ASP_ID.
Definition sig_map := MapC Plc ASP_ID.

(* Specific AM monad state *)
Record AM_St : Type := mkAM_St
                         { am_nonceMap : MapC nat BS;
                           am_nonceId : nat;
                           st_aspmap : asp_map;
                           st_sigmap : sig_map;
                           (*am_pl : Plc ; *)
                           checked : list nat }.

Definition empty_amst :=
  mkAM_St [] 0 [] [] [].

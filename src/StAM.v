(*
Record representing the AM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Maps.
Require Import Coq.Arith.EqNat.

Definition BS := nat.

(* Specific AM monad state *)
Record AM_St : Type := mkAM_St
                         { am_nonceMap : MapC nat BS;
                           am_nonceId : nat;
                           checked : list nat }.
                                         

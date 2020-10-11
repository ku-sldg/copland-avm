(*
Record representing the AM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Maps_Class.
Require Import Coq.Arith.EqNat.

(*Definition BS := nat. *)

Instance nat_EqClass : EqClass nat :=
  { eqb:= PeanoNat.Nat.eqb;
    eqb_leibniz := beq_nat_true }.

(* Specific AM monad state *)
Record AM_St : Type := mkAM_St
                         { am_nonceMap : MapC nat nat;
                           am_nonceId : nat;
                           checked : list nat }.
                                         

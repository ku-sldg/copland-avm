Require Import Maps BS Cvm_St ErrorStMonad_Coq.


Require Import List.
Import ListNotations.


(* Specific AM monad state *)
Record AM_St : Type := mkAM_St
                         { am_nonceMap : MapC nat BS;
                           am_nonceId : nat (* ;
                           st_aspmap : asp_map;
                           st_sigmap : sig_map;
                           (*am_pl : Plc *)(*;
                           checked : list nat*) *) }.

Definition empty_amst :=
  mkAM_St map_empty 0 (* [] [] *) .

Inductive AM_Error : Type := 
| cvm_error : CVM_Error -> AM_Error
| am_error : StringT -> AM_Error.
  (*
  | term_disclosure_error : Term -> AM_Error
  | manifest_asp_unavailable : ASP_ID ->   *)
  
Definition AM A := Err AM_St A AM_Error.

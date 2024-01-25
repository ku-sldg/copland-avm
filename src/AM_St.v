(* Definitions for AM Monad State (AM_St) and AM Monad (AM).  *)

Require Import Maps BS Term_Defs_Core Cvm_St ErrorStMonad_Coq StringT.


Require Import List.
Import ListNotations.


(* Specific AM monad state *)
Record AM_St : Type := mkAM_St
                         { am_nonceMap : MapC N_ID BS;
                           am_nonceId : N_ID; 
                           amConfig : AM_Config }.

Definition empty_amst :=
  mkAM_St map_empty 0 empty_am_config.


Inductive AM_Error : Type := 
| cvm_error : CVM_Error -> AM_Error
| am_error : StringT -> AM_Error
| am_dispatch_error : DispatcherErrors -> AM_Error.
  (*
  | term_disclosure_error : Term -> AM_Error
  | manifest_asp_unavailable : ASP_ID ->   *)

Definition am_failm {A: Type} (e:AM_Error) : Err AM_St A AM_Error := fun s => (errC e, s).
  
Definition AM A := Err AM_St A AM_Error.

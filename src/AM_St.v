(* Definitions for AM Monad State (AM_St) and AM Monad (AM).  *)

Require Import Maps ResultT BS Term_Defs_Core Cvm_St ErrorStMonad_Coq String Attestation_Session.


Require Import List.
Import ListNotations.


(* Specific AM monad state *)
Record AM_St : Type := mkAM_St
                         { am_nonceMap : MapC N_ID BS;
                           am_nonceId : N_ID; 
                           am_config : Session_Config }.

Inductive AM_Error : Type := 
| cvm_error : CVM_Error -> AM_Error
| am_error : string -> AM_Error
| am_dispatch_error : DispatcherErrors -> AM_Error.
  (*
  | term_disclosure_error : Term -> AM_Error
  | manifest_asp_unavailable : ASP_ID ->   *)

Definition am_failm {A: Type} (e:AM_Error) : Err AM_St A AM_Error := fun s => (errC e, s).
  
Definition AM A := Err AM_St A AM_Error.

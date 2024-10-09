(* Definitions for AM Monad State (AM_St) and AM Monad (AM).  *)

Require Import Maps Term_Defs_Core Cvm_St ErrorStMonad_Coq String Attestation_Session.


Require Import List.
Import ListNotations.


(* Specific AM monad state *)
Record AM_St : Type := mkAM_St { 
  am_nonceMap : Map N_ID BS;
  am_nonceId : N_ID; 
}.

Inductive AM_Error : Type := 
| cvm_error : CVM_Error -> AM_Error
| am_error : string -> AM_Error
| am_dispatch_error : DispatcherErrors -> AM_Error.

Definition am_failm {A: Type} (e:AM_Error) : Err AM_St Session_Config A AM_Error := 
  fun s c => (errC e, s, c).
  
Definition AM A := Err AM_St Session_Config A AM_Error.

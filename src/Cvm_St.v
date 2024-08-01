(*
Record representing the CVM Monad state structure:  cvm_st 

CVM Monad definition.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidence ErrorStMonad_Coq Attestation_Session.
Require Import List.
Import ListNotations.
Require Import Manifest_Admits.

(** CVM monad state structure.

    st_ev - Evidence bundle.  Holds raw evidence sequence along with its 
            Evidence Type.
    st_trace - Event trace accumulated by the CVM (relevant only during 
               verification)
    st_pl - Current "executing place".
    st_evid - Monotonic event ID counter.  Incremented after each 
              attestation-relevant event/invocation.
    st_config - AM Configuration (typically produced by the Manifest Compiler).  
                   Provides callback functions used by the CVM to interpret Copland.
 *)


Record cvm_st : Type := mk_st
                          {st_ev:EvC ;
                           st_trace:list Ev ;
                           st_evid:Event_ID ;
                           st_config : Session_Config ;
                           }.

Inductive CVM_Error : Type := 
| at_error_static : Term -> Plc -> EvC -> CVM_Error
| at_error_dynamic : Term -> UUID -> EvC -> CVM_Error
| dispatch_error : DispatcherErrors -> CVM_Error.
(* | callback_error : CallBackErrors -> CVM_Error. *)

(** CVM monad -- instantiation of the general ResultT monad with cvm_st *)
Definition CVM A := Err cvm_st A CVM_Error.

(* Look for cvm_st hyps and destruct them *)
Ltac vmsts :=
  simpl in *;
  repeat
    match goal with
    | [H: cvm_st |- _] => destruct H
    end.

(* Same as vmsts, but without preceding simplification (simpl). *)
Ltac amsts :=
  repeat match goal with
         | H:cvm_st |- _ => destruct H
         end.

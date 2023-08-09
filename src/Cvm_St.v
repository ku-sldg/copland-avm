(*
Record representing the CVM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidence ErrorStMonad_Coq AbstractedTypes Manifest Manifest_Admits.
Require Import List.
Import ListNotations.

(** CVM monad state structure.

    st_ev - Evidence bundle.  Holds raw evidence sequence along with its 
            Evidence Type.
    st_trace - Event trace accumulated by the CVM (relevant only during 
               verification)
    st_pl - Current "executing place".
    st_evid - Monotonic event ID counter.  Incremented after each 
              attestation-relevant event/invocation.
 *)
Record AM_Config : Type := 
  mkAmConfig {
    concMan : ConcreteManifest ;
    aspCb : CakeML_ASPCallback ;
    plcCb : CakeML_PlcCallback ;
    pubKeyCb : CakeML_PubKeyCallback ;
    uuidCb : CakeML_uuidCallback ;
  }.

Definition emptyConcreteMan : ConcreteManifest := {|
  my_plc := min_id_type;
  Concrete_ASPs := nil;
  Concrete_Plcs := nil;
  Concrete_PubKeys := nil;
  Concrete_Targets := nil;
  ASP_Server := empty_ASP_Address;
  PubKey_Server := empty_ASP_Address;
  Plc_Server := empty_ASP_Address;
  UUID_Server := empty_ASP_Address;
|}.

Definition empty_am_config : AM_Config :=
  mkAmConfig 
    emptyConcreteMan 
    (fun x => errC Unavailable)
    (fun x => errC Unavailable)
    (fun x => errC Unavailable)
    (fun x => errC Unavailable).

Record cvm_st : Type := mk_st
                          {st_ev:EvC ;
                           st_trace:list Ev ;
                           st_pl:Plc;
                           st_evid:Event_ID ;
                           st_AM_config : AM_Config ;
                           }.

Definition empty_vmst : cvm_st := mk_st (evc [] mt) [] min_id_type 0 empty_am_config.



Inductive CVM_Error : Type := 
| at_error_static : Term -> Plc -> EvC -> CVM_Error
| at_error_dynamic : Term -> UUID -> EvC -> CVM_Error.

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

(*
Record representing the CVM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidence.
Require Import List.
Import ListNotations.

Definition Event_ID: Set := nat.

(* Specific VM monad state *)
Record cvm_st : Type := mk_st
                          {st_ev:EvC ;
                           st_trace:list Ev ;
                           st_pl:Plc;
                           st_evid:Event_ID}.

Definition empty_vmst := mk_st (evc [] mt) [] 0 0.

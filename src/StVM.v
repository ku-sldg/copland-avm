(*
Record representing the CVM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidence.
Require Import Maps.
Require Import List.
Import ListNotations.

Definition Event_ID := nat.

(* Specific VM monad state *)
(*Definition ev_store := MapC nat EvidenceC. *)
Record cvm_st : Type := mk_st
                          {st_ev:EvC ;
                           st_trace:list Ev ;
                           st_pl:Plc;
                           st_evid:Event_ID
                           (*;
                           st_store:ev_store*)}.

Definition empty_vmst := mk_st (evc [] mt) [] 0 0 (* [] *) .

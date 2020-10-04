(*
Record representing the AVM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidence.
Require Import Maps.

(* Specific VM monad state *)
Definition ev_store := Map.
Record vm_st : Type := mk_st
                         {st_ev:EvidenceC ;
                          st_trace:list Ev ;
                          st_pl:Plc ;
                          st_store:ev_store}.

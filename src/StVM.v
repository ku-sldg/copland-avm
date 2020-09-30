(*
Record representing the AVM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import MyStack ConcreteEvidence.
Require Import Maps.

(* Specific VM monad state *)
Definition ev_stack := gen_stack EvidenceC.
Definition ev_store := Map.
Record vm_st : Type := mk_st
                         {st_ev:EvidenceC ;
                          st_stack:ev_stack ; 
                          st_trace:list Ev ;
                          st_pl:Plc ;
                          st_store:ev_store}.

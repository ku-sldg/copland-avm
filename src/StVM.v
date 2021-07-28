(*
Record representing the CVM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidence.
Require Import Maps.
Require Import List.
Import ListNotations.

(* Specific VM monad state *)
(*Definition ev_store := MapC nat EvidenceC. *)
Record cvm_st : Type := mk_st
                          {st_ev:EvC ;
                           (*st_evT: Evidence ; *)
                           st_trace:list Ev ;
                           st_pl:Plc (*;
                           st_store:ev_store*)}.

Definition empty_vmst := mk_st (evc [] mt) [] 0 (* [] *) .

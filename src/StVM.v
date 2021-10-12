(*
Record representing the CVM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidence.
Require Import Maps.
Require Import List.
Import ListNotations.

Inductive CVM_Event: Set :=
| cvm_copy:  nat -> Plc -> CVM_Event 
| cvm_umeas: nat -> Plc -> ASP_ID -> (list Arg) -> Plc -> TARG_ID -> CVM_Event
| cvm_sign: nat -> Plc -> Evidence -> CVM_Event
| cvm_hash: nat -> Plc -> Evidence -> CVM_Event
| cvm_req: nat -> Plc -> Plc -> Term -> Evidence -> CVM_Event
| cvm_rpy: nat -> Plc -> Plc -> Evidence -> CVM_Event 
| cvm_split: nat -> Plc -> CVM_Event
| cvm_splitp: nat -> Loc -> Plc -> AnnoTerm -> Evidence -> CVM_Event
| cvm_join:  nat -> Plc -> CVM_Event
| cvm_joinp:  nat -> Loc -> Plc -> AnnoTerm -> CVM_Event.

(* Specific VM monad state *)
(*Definition ev_store := MapC nat EvidenceC. *)
Record cvm_st : Type := mk_st
                          {st_ev:EvC ;
                           (*st_evT: Evidence ; *)
                           st_trace:list CVM_Event ;
                           st_pl:Plc (*;
                           st_store:ev_store*)}.

Definition empty_vmst := mk_st (evc [] mt) [] 0 (* [] *) .

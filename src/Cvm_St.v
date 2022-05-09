(*
Record representing the CVM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidence StMonad_Coq.
Require Import List.
Import ListNotations.

(* Specific VM monad state *)
Record cvm_st : Type := mk_st
                          {st_ev:EvC ;
                           st_trace:list Ev ;
                           st_pl:Plc;
                           st_evid:Event_ID}.

Definition empty_vmst := mk_st (evc [] mt) [] 0 0.

Definition CVM := St cvm_st.

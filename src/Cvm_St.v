(*
Record representing the CVM Monad state structure.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import ConcreteEvidence StMonad_Coq AbstractedTypes.
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
Record cvm_st : Type := mk_st
                          {st_ev:EvC ;
                           st_trace:list Ev ;
                           st_pl:Plc;
                           st_evid:Event_ID}.

Definition empty_vmst := mk_st (evc [] mt) [] min_id_type 0.

(** CVM monad -- simple instantiation of the general St monad with cvm_st *)
Definition CVM := St cvm_st.

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

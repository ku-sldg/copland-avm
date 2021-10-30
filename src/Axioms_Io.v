(*
Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term ConcreteEvidence LTS StVM.

Require Import List.
Import ListNotations.

(** IO Axioms *)

Definition toRemote (t:AnnoTerm) (pTo:Plc) (e:EvC) : EvC.
Admitted.

Definition remote_events (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Definition parallel_vm_thread (t:AnnoTerm) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition parallel_vm_events (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

Definition remote_evidence (t:AnnoTerm) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition remote_trace (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Axiom remote_LTS: forall t n et, 
    lstar (conf t n et) (remote_events t n) (stop n (aeval t n et)).


Axiom remote_Evidence_Type_Axiom: forall t n bits et,
    get_et (toRemote t n (evc bits et)) = aeval t n et.


Axiom at_evidence : forall t (p:Plc) (e:EvC),
    toRemote t p e = remote_evidence t p e.

Axiom at_events : forall t p,
  remote_events t p = remote_trace t p.


Axiom par_evidence : forall t (p:Plc) (e:EvC),
    parallel_vm_thread t p e = remote_evidence t p e.


Axiom par_events : forall t p,
    parallel_vm_events t p = remote_trace t p.

Axiom bpar_shuffle : forall x tr p t1 t2 et1 et2,
    lstar (conf t1 p et1) tr (stop p (aeval t1 p et1)) ->
    lstar (bp x (conf t1 p et1) (conf t2 p et2))
          (shuffled_events tr
                           (remote_events t2 p))
          (bp x (stop p (aeval t1 p et1)) (stop p (aeval t2 p et2))).

Axiom thread_bookend_peel: forall t p et etr n l a n0 tr,
    lstar (conf (unannoPar t) p et) tr (stop p (aeval (unannoPar t) p et)) ->
    ([cvm_thread_start n l p a etr] ++ tr ++ [cvm_thread_end (Nat.pred n0) l p a] =
     (shuffled_events tr (remote_events a p))
    ).

Axiom wf_ec_preserved_remote: forall a n e,
    wf_ec e ->
    well_formed_r_annt a ->
    wf_ec (Axioms_Io.toRemote a n e).

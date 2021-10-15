(*
Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term ConcreteEvidence LTS StVM.

(** IO Axioms *)

Definition toRemote (t:AnnoTerm) (pTo:Plc) (e:EvC) : EvC.
Admitted.
Definition remote_events (t:AnnoTerm) (p:Plc) : (list Ev).
Admitted.

(*
Definition parallel_eval_thread (t:Term) (p:Plc) (e:EvidenceC) : EvidenceC.
Admitted.
*)


Definition parallel_vm_thread (t:AnnoTerm) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition parallel_vm_events (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

(*
Definition lts_remote_events (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.
*)



(*
    Axiom remote_lts_axiom: forall a n et x,
      lstar (conf a n et) x (stop n (aeval a n et)) ->
      x = lts_remote_events a n.
*)

Axiom remote_LTS: forall t n et, 
    lstar (conf t n et) (remote_events t n) (stop n (aeval t n et)).



Definition remote_evidence (t:AnnoTerm) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition remote_trace (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.


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





(*

Axiom par_events : forall t p,
    parallel_vm_events t p = remote_trace t p.

Axiom bpar_shuffle : forall x p t1 t2 et1 et2 xi yi,
    lstar (bp x xi yi (conf t1 p et1) (conf t2 p et2))
          (shuffled_events (parallel_vm_events t1 p)
                           (parallel_vm_events t2 p))
          (bp x xi yi (stop p (aeval t1 p et1)) (stop p (aeval t2 p et2))).
*)

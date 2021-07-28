(*
Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term ConcreteEvidence LTS.

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



Definition remote_evidence (t:AnnoTerm) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition remote_trace (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.



Axiom at_evidence : forall t (p:Plc) (e:EvC),
    toRemote t p e = remote_evidence t p e.

Axiom at_events : forall t p,
  remote_events t p = remote_trace t p.

(*
Axiom par_evidence : forall t (p:Plc) (e:EvidenceC),
    parallel_vm_thread t p e = remote_evidence t p e.

Axiom par_events : forall t p,
    parallel_vm_events t p = remote_trace t p.

Axiom bpar_shuffle : forall x p t1 t2 et1 et2 xi yi,
    lstar (bp x xi yi (conf t1 p et1) (conf t2 p et2))
          (shuffled_events (parallel_vm_events t1 p)
                           (parallel_vm_events t2 p))
          (bp x xi yi (stop p (aeval t1 p et1)) (stop p (aeval t2 p et2))).
*)

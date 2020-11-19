Require Import Term ConcreteEvidence.

(** IO Axioms *)

Definition toRemote (t:AnnoTerm) (pTo:Plc) (e:EvidenceC) : EvidenceC.
Admitted.
Definition remote_events (t:AnnoTerm) (p:Plc) : (list Ev).
Admitted.

(*
Definition parallel_eval_thread (t:Term) (p:Plc) (e:EvidenceC) : EvidenceC.
Admitted.
*)


Definition parallel_vm_thread (t:AnnoTerm) (p:Plc) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.



Definition remote_evidence (t:AnnoTerm) (p:Plc) (e:EvidenceC) : EvidenceC.
Admitted.

Definition remote_trace (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.



Axiom at_evidence : forall t (p:Plc) (e:EvidenceC),
    toRemote t p e = remote_evidence t p e.

Axiom at_events : forall t p,
  remote_events t p = remote_trace t p.

Axiom par_evidence : forall t (p:Plc) (e:EvidenceC),
    parallel_vm_thread t p e = remote_evidence t p e.

Axiom par_events : forall t p,
  parallel_vm_events t p = remote_trace t p.

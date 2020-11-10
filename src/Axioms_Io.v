Require Import Term ConcreteEvidence.

(** IO Axioms *)

Definition remote_events (t:AnnoTerm) (p:Plc) : (list Ev).
Admitted.
Definition toRemote (t:Term) (*(pTo:Plc)*) (e:EvidenceC) : EvidenceC.
Admitted.
Definition parallel_eval_thread (t:Term) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_att_vm_thread (t:AnnoTerm) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

Definition remote_evidence (t:AnnoTerm) (e:EvidenceC) : EvidenceC.
Admitted.

Definition remote_trace (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Axiom at_evidence : forall t e,
    toRemote (unanno t) e = remote_evidence t e.

Axiom at_events : forall t p,
  remote_events t p = remote_trace t p.

Axiom par_evidence : forall t e,
    parallel_att_vm_thread t e = remote_evidence t e.

Axiom par_events : forall t p,
  parallel_vm_events t p = remote_trace t p.

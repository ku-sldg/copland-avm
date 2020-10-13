Require Import Term ConcreteEvidence.

(** IO Axioms *)

Definition parallel_att_vm_thread (t:AnnoTerm) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

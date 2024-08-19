(*
Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Interface IO_Stubs.

Import ListNotations.

(** IO Axioms *)

(*
Definition doRemote_session (t:Term) (pTo:Plc) (e:Evidence) : Evidence.
Admitted.

Definition parallel_vm_thread (l:Loc) (t:Term) (p:Plc) (e:Evidence) : Evidence.
Admitted.
*)

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

Definition cvm_events (p:Plc) (e:EvidenceT) (t:Term) : list Ev. Admitted.

Definition cvm_EvidenceT (p:Plc) (e:Evidence) (t:Term) : Evidence. Admitted.


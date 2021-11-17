(*
Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs LTS.

Require Import List.
Import ListNotations.

(** IO Axioms *)

Definition doRemote_session (t:Term) (pTo:Plc) (e:EvC) : EvC.
Admitted.

Definition parallel_vm_thread (l:Loc) (t:Term) (p:Plc) (e:EvC) : EvC.
Admitted.



Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

Definition cvm_events (t:Term) (p:Plc) (e:Evidence) : list Ev.
Admitted.

Definition cvm_evidence (t:Term) (p:Plc) (e:EvC) : EvC.
Admitted.


Axiom remote_LTS: forall t n et, 
    lstar (conf t n et) (cvm_events (unanno t) n et) (stop n (aeval t n et)).


Axiom remote_Evidence_Type_Axiom: forall t n bits et,
    get_et (doRemote_session t n (evc bits et)) = eval t n et.


Axiom at_evidence : forall t (p:Plc) (e:EvC),
    doRemote_session t p e = cvm_evidence t p e.


Axiom par_evidence : forall t (p:Plc) (e:EvC) loc,
    parallel_vm_thread loc t p e = cvm_evidence t p e.



Axiom bpar_shuffle : forall x tr p t1 t2 et1 et2,
    lstar (conf t1 p et1) tr (stop p (aeval t1 p et1)) ->
    lstar (bp x (conf t1 p et1) (conf t2 p et2))
          (shuffled_events tr
                           (cvm_events (unanno t2) p et2))
          (bp x (stop p (aeval t1 p et1)) (stop p (aeval t2 p et2))).

Axiom thread_bookend_peel: forall (t:AnnoTerm) p (*et*) etr l (a:Term) tr,
    (*lstar (conf t p et) tr (stop p (aeval t p et)) -> *)
    ([cvm_thread_start l p a etr] ++ tr ++ [cvm_thread_end l] =
     (shuffled_events tr (cvm_events a p etr))
    ).


Axiom wf_ec_preserved_remote: forall a n e,
    wf_ec e ->
    wf_ec (doRemote_session a n e).

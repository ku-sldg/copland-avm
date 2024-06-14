(*
Uninterpreted functions and rewrite rules that model external (remote and local parallel) components that interpret Copland phrases.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Interface_Types LTS IO_Stubs CvmJson_Interfaces ResultT Manifest Cvm_St.

Require Import List.
Import ListNotations.

(** IO Axioms *)

(*
Definition doRemote_session (t:Term) (pTo:Plc) (e:EvC) : EvC.
Admitted.

Definition parallel_vm_thread (l:Loc) (t:Term) (p:Plc) (e:EvC) : EvC.
Admitted.
*)

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

Definition cvm_events_core (t:Core_Term) (p:Plc) (e:Evidence) : list Ev. 
Admitted.

Definition cvm_evidence_core (t:Core_Term) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition cvm_events (t:Term) (p:Plc) (e:Evidence) : list Ev :=
  cvm_events_core (copland_compile t) p e.

Definition cvm_evidence (t:Term) (p:Plc) (e:EvC) : EvC :=
  cvm_evidence_core (copland_compile t) p e.


Axiom remote_LTS: forall t annt n et i i',
    annoP_indexed annt t i i' ->
    lstar (conf annt n et) (cvm_events t n et) (stop n (aeval annt n et)).

(*
Axiom remote_Evidence_Type_Axiom: forall t n bits et,
    get_et (doRemote_session t n (evc bits et)) = eval t n et.
*)

(*
Axiom at_evidence : forall t (p:Plc) (e:EvC),
    doRemote_session t p e = cvm_evidence t p e.
*)

Axiom par_evidence : forall t (p:Plc) (e:EvC) loc,
    parallel_vm_thread loc (copland_compile t) p e = cvm_evidence t p e.



Axiom bpar_shuffle : forall x annt2 i i' tr p t1 t2 et1 et2,
    annoP_indexed annt2 t2 i i' ->
    lstar (conf t1 p et1) tr (stop p (aeval t1 p et1)) ->
    lstar (bp x (conf t1 p et1) (conf annt2 p et2))
          (shuffled_events tr
                           (cvm_events t2 p et2))
          (bp x (stop p (aeval t1 p et1)) (stop p (aeval annt2 p et2))).

Axiom thread_bookend_peel: forall (t:AnnoTerm) p (*et*) etr l (a:Core_Term) tr,
    (*lstar (conf t p et) tr (stop p (aeval t p et)) -> *)
    ([cvm_thread_start l p a etr] ++ tr ++ [cvm_thread_end l] =
     (shuffled_events tr (cvm_events_core a p etr))
    ).

(*
Axiom wf_ec_preserved_remote: forall a n e,
    wf_ec e ->
    wf_ec (doRemote_session a n e).
    *)

Axiom wf_ec_preserved_remote: forall st pTarg uuid ac ev1,
    (* doRemote t u (get_bits ev1) = resultC ev1' ->  *)
    (* do_remote t p e ac = resultC ev1' -> *)
    (st_AM_config st) = ac ->
    (st_ev st) = ev1 ->
    (plcCb ac) pTarg = resultC uuid ->
    forall t rawEv,
    JSON_to_AM_Protocol_Response (
      make_JSON_Network_Request uuid (
        ProtocolRunRequest_to_JSON (
          (mkPRReq 
            t 
            (my_abstract_plc (absMan (st_AM_config st)))
            (get_bits ev1)
          )
        ))) = resultC (Protocol_Run_Response (mkPRResp true rawEv)) -> 
    wf_ec ev1 -> 
    wf_ec (evc rawEv (eval t pTarg (get_et ev1))).

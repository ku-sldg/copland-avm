(*
Axioms and derived lemmas that capture the semantics of external CVM instances.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Cvm_Impl Axioms_Io Cvm_Monad Attestation_Session.

Require Import List.
Import ListNotations.


(* TODO: This seems obscenely strong!? *)
Axiom build_cvm_external' : forall (t : Core_Term) (e : EvC) (tr:list Ev) (i:Event_ID) (ac : Session_Config),
  build_cvm t {| st_ev := e; st_trace := tr; st_evid := i; st_config := ac |} 
    = (resultC tt, {| st_ev := cvm_EvidenceT_core t (session_plc ac) e;
           st_trace := tr ++ (cvm_events_core t (session_plc ac) (get_et e));
           st_evid := (i + event_id_span t);
           st_config := ac |}).

Lemma build_cvm_external : forall (t : Core_Term) (e : EvC) i ac,
    build_cvm t
                    {| st_ev := e;
                       st_trace := [];
                       st_evid := i;
                       st_config := ac|} =
    (resultC tt,
     {| st_ev := cvm_EvidenceT_core t (session_plc ac) e;
        st_trace := cvm_events_core t (session_plc ac) (get_et e);
        st_evid := (i + event_id_span t);
        st_config := ac
     |}).
Proof.
  intros.
  eapply build_cvm_external'.
Qed.

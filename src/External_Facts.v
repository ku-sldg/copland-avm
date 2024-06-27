(*
Axioms and derived lemmas that capture the semantics of external CVM instances.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Cvm_St Cvm_Impl Axioms_Io Helpers_CvmSemantics Cvm_Monad ID_Type.

Require Import List.
Import ListNotations.


(* TODO: This seems obscenely strong!? *)
Axiom build_cvm_external' : forall (t : Core_Term) (e : EvC) (tr:list Ev) (i:Event_ID) (ac : AM_Config),
    runErr 
      (build_cvm t)
      {| st_ev := e;
         st_trace := tr;
         st_evid := i;
         st_AM_config := ac |} =
    (resultC tt,
     {| st_ev := cvm_evidence_core t (my_abstract_plc (absMan ac)) e;
        st_trace := tr ++ (cvm_events_core t (my_abstract_plc (absMan ac)) (get_et e));
        st_evid := (i + event_id_span t);
        st_AM_config := ac
     |}).

Lemma build_cvm_external : forall (t : Core_Term) (e : EvC) i ac,
    build_cvm t
                    {| st_ev := e;
                       st_trace := [];
                       st_evid := i;
                       st_AM_config := ac|} =
    (resultC tt,
     {| st_ev := cvm_evidence_core t (my_abstract_plc (absMan ac)) e;
        st_trace := cvm_events_core t (my_abstract_plc (absMan ac)) (get_et e);
        st_evid := (i + event_id_span t);
        st_AM_config := ac
     |}).
Proof.
  intros.
  assert ([] ++ (cvm_events_core t (my_abstract_plc (absMan ac)) (get_et e)) = (cvm_events_core t (my_abstract_plc (absMan ac)) (get_et e))) by eauto.
  eapply build_cvm_external'.
Defined.

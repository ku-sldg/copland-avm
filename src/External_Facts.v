(*
Axioms and lemmas that capture the semantics of external CVM instances.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Cvm_St Cvm_Impl Axioms_Io Helpers_CvmSemantics Cvm_Monad AbstractedTypes.

Require Import List.
Import ListNotations.


Axiom build_cvm_external' : forall (t : Core_Term) (e : EvC) (n : ID_Type) (tr:list Ev) (i:Event_ID) (ac : AM_Config),
    runErr 
      (build_cvm t)
      {| st_ev := e;
         st_trace := tr;
         st_pl := n;
         st_evid := i;
         st_AM_config := ac |} =
    (resultC tt,
     {| st_ev := cvm_evidence_core t n e;
        st_trace := tr ++ (cvm_events_core t n (get_et e));
        st_pl :=
          st_pl
            (
              execErr (build_cvm t)
                     {| st_ev := e;
                        st_trace := [];
                        st_pl := n;
                        st_evid := i;
                        st_AM_config := ac |});
        st_evid := (i + event_id_span t);
        st_AM_config := ac
     |}).

Lemma build_cvm_external : forall (t : Core_Term) (e : EvC) (n : ID_Type) i ac,
    build_cvm t
                    {| st_ev := e;
                       st_trace := [];
                       st_pl := n;
                       st_evid := i;
                       st_AM_config := ac|} =
    (resultC tt,
     {| st_ev := cvm_evidence_core t n e;
        st_trace := cvm_events_core t n (get_et e);
        st_pl := n;
        st_evid := (i + event_id_span t);
        st_AM_config := ac
     |}).
Proof.
  intros.
  assert ([] ++ (cvm_events_core t n (get_et e)) = (cvm_events_core t n (get_et e))) by eauto.
  assert (n = st_pl
            (
              execErr
                (build_cvm t)
                {| st_ev := e;
                     st_trace := [];
                     st_pl := n; st_evid := i; st_AM_config := ac |})) as H0'.
  {
    rewrite pl_immut;
    tauto. 
  }
  rewrite H0' at 4.
  eapply build_cvm_external'.
Defined.

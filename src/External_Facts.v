(*
Axioms and lemmas that capture the semantics of external CVM instances.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Cvm_St Cvm_Impl Axioms_Io Helpers_CvmSemantics Cvm_Monad.

Require Import List.
Import ListNotations.


Axiom copland_compile_external' : forall (t : Core_Term) (e : EvC) (n : nat) (tr:list Ev) (i:Event_ID),
    runSt 
      (copland_compile t)
      {| st_ev := e;
         st_trace := tr;
         st_pl := n;
         st_evid := i |} =
    (Some tt,
     {| st_ev := cvm_evidence_core t n e;
        st_trace := tr ++ (cvm_events_core t n (get_et e));
        st_pl :=
          st_pl
            (
              execSt (copland_compile t)
                     {| st_ev := e;
                        st_trace := [];
                        st_pl := n;
                        st_evid := i |});
        st_evid := (i + event_id_span t)
     |}).

Lemma copland_compile_external : forall (t : Core_Term) (e : EvC) (n : nat) i,
    copland_compile t
                    {| st_ev := e;
                       st_trace := [];
                       st_pl := n;
                       st_evid := i|} =
    (Some tt,
     {| st_ev := cvm_evidence_core t n e;
        st_trace := cvm_events_core t n (get_et e);
        st_pl := n;
        st_evid := (i + event_id_span t)
     |}).
Proof.
  intros.
  assert ([] ++ (cvm_events_core t n (get_et e)) = (cvm_events_core t n (get_et e))) by eauto.
  assert (n = st_pl
            (
              execSt
                (copland_compile t)
                {| st_ev := e;
                     st_trace := [];
                     st_pl := n; st_evid := i |})) as H0'.
  {
    rewrite pl_immut;
    tauto. 
  }
  rewrite H0' at 4.
  eapply copland_compile_external'.
Defined.


(*

Lemma copland_compile_at' : forall (t : Core_Term) (e : EvC) (n : nat) (tr: list Ev) i,
    copland_compile t
                    {| st_ev := e;
                       st_trace := tr;
                       st_pl := n;
                       st_evid := i |} =
    (Some tt,
     {| st_ev := doRemote_session (unannoPar t) n e;
        st_trace := tr ++ cvm_events (unannoPar t) n (get_et e);
        st_pl := n;
        st_evid := (i + event_id_span (unannoPar t))
     |}).
Proof.
  intros.
  rewrite at_evidence.
  
  assert (st_pl
            (execSt
               (copland_compile t)
               {| st_ev := e;
                  st_trace := [];
                  st_pl := n;
                  st_evid := i|}) = n) as H0.
  eapply pl_immut.
  eauto.
  rewrite <- H0 at 4.
  eapply copland_compile_external'.
Defined.
*)


(*

Lemma copland_compile_at : forall (t : Term) (e : EvC) (n : nat) i,
    copland_compile (term_to_core_term t)
                    {| st_ev := e;
                       st_trace := [];
                       st_pl := n;
                       st_evid := i|} =
    (Some tt,
     {| st_ev := (* doRemote_session t n e; *)
        st_trace := cvm_events t n (get_et e);
        st_pl := n;
        st_evid := (i + event_id_span' t)
     |}).
Proof.
  intros.
  rewrite at_evidence.
  eapply copland_compile_external; eauto.
Defined.
*)

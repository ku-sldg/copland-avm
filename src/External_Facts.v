Require Import Term ConcreteEvidence StVM Impl_vm Axioms_Io GenStMonad Helpers_VmSemantics.

Require Import List.
Import ListNotations.

Axiom build_comp_external' : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store) (tr:list Ev),
    runSt 
      (build_comp t)
      {| st_ev := e; st_trace := tr; st_pl := n; st_store := o |} =
    (Some tt,
     {| st_ev := remote_evidence t n e;
        st_trace := tr ++ (remote_trace t n);
        st_pl :=
          st_pl
            (
              execSt (build_comp t)
                     {| st_ev := e;
                        st_trace := [];
                        st_pl := n;
                        st_store := o |});
        st_store :=
          st_store
            (
              execSt (build_comp t)
                     {| st_ev := e;
                        st_trace := [];
                        st_pl := n;
                        st_store := o |});
     |}).


Lemma build_comp_external : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store),
    well_formed t ->
    build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |} =
    (Some tt,
     {| st_ev := remote_evidence t n e;
        st_trace := remote_trace t n;
        st_pl := n;
        st_store :=
          st_store
            (
              execSt
                (build_comp t)
                  {| st_ev := e;
                     st_trace := [];
                     st_pl := n;
                     st_store := o |});
     |}).
Proof.
  intros.
  assert ([] ++ (remote_trace t n) = (remote_trace t n)) by eauto.
  assert (n = st_pl
            (
              execSt
                (build_comp t)
                  {| st_ev := e;
                     st_trace := [];
                     st_pl := n;
                     st_store := o |})) as H0'.
  {
    rewrite pl_immut;
    tauto. 
  }
  rewrite H0' at 4.
  eapply build_comp_external'.
Defined.




Lemma build_comp_at' : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store) (tr: list Ev),
    well_formed t ->
    build_comp t {| st_ev := e; st_trace := tr; st_pl := n; st_store := o |} =
    (Some tt,
     {| st_ev := toRemote t n e;
        st_trace := tr ++ remote_events t n;
        st_pl := n;
        st_store :=
          st_store
            (
              execSt
                (build_comp t)
                {| st_ev := e;
                   st_trace := [];
                   st_pl := n;
                   st_store := o |});
     |}).
Proof.
  intros.
  rewrite at_evidence.
  rewrite at_events.
  
  assert (st_pl
            (execSt
               (build_comp t)
               {| st_ev := e;
                  st_trace := [];
                  st_pl := n;
                  st_store := o |}) = n) as H0.
  eapply pl_immut.
  eauto.
  rewrite <- H0 at 4.
  eapply build_comp_external'.
Defined.


Lemma build_comp_at : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store),
    well_formed t ->
    build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |} =
    (Some tt,
     {| st_ev := toRemote t n e;
        st_trace := remote_events t n;
        st_pl := n;
        st_store :=
          st_store
            (
              execSt
                (build_comp t)
                {| st_ev := e;
                              st_trace := [];
                              st_pl := n;
                              st_store := o |});
     |}).
Proof.
  intros.
  rewrite at_evidence.
  rewrite at_events.
  eapply build_comp_external; eauto.
Defined.

Lemma build_comp_par' :
  forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store) (tr:list Ev),
    well_formed t ->
    build_comp t {| st_ev := e; st_trace := tr; st_pl := n; st_store := o |} =
    (Some tt,
     {|
       st_ev := parallel_vm_thread t n e;
       st_trace := tr ++ parallel_vm_events t n;
       st_pl := n;
       st_store :=
         st_store
           (execSt
              (build_comp t)
              {| st_ev := e;
                 st_trace := [];
                 st_pl := n;
                 st_store := o |})
     |}).
Proof.
  intros.
  rewrite par_evidence.
  rewrite par_events.
  assert (st_pl
            (execSt
               (build_comp t)
               {| st_ev := e;
                  st_trace := [];
                  st_pl := n;
                  st_store := o |}) = n) as H0.
  eapply pl_immut.
  eauto.
  rewrite <- H0 at 4.
  eapply build_comp_external'.
Defined.

Lemma build_comp_par :
  forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store),
    well_formed t ->
    build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |} =
    (Some tt,
     {|
       st_ev := parallel_vm_thread t n e;
       st_trace := parallel_vm_events t n;
       st_pl := n;
       st_store :=
         st_store
           ( execSt
               (build_comp t)
                {| st_ev := e;
                   st_trace := [];
                   st_pl := n;
                   st_store := o |})
     |}).
Proof.
  intros.
  rewrite par_evidence.
  rewrite par_events.
  eapply build_comp_external; eauto.
Defined. 

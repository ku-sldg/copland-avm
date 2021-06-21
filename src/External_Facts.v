(*
Axioms and lemmas that capture the semantics of external CVM instances.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term ConcreteEvidence StVM Impl_vm Axioms_Io GenStMonad Helpers_VmSemantics.

Require Import List.
Import ListNotations.



Axiom copland_compile_external' : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (tr:list Ev),
    runSt 
      (copland_compile t)
      {| st_ev := e; st_trace := tr; st_pl := n |} =
    (Some tt,
     {| st_ev := remote_evidence t n e;
        st_trace := tr ++ (remote_trace t n);
        st_pl :=
          st_pl
            (
              execSt (copland_compile t)
                     {| st_ev := e;
                        st_trace := [];
                        st_pl := n |})
     |}).


Lemma copland_compile_external : forall (t : AnnoTerm) (e : EvidenceC) (n : nat),
    well_formed_r t ->
    copland_compile t {| st_ev := e; st_trace := []; st_pl := n |} =
    (Some tt,
     {| st_ev := remote_evidence t n e;
        st_trace := remote_trace t n;
        st_pl := n
     |}).
Proof.
  intros.
  assert ([] ++ (remote_trace t n) = (remote_trace t n)) by eauto.
  assert (n = st_pl
            (
              execSt
                (copland_compile t)
                {| st_ev := e;
                     st_trace := [];
                     st_pl := n |})) as H0'.
  {
    rewrite pl_immut;
    tauto. 
  }
  rewrite H0' at 4.
  eapply copland_compile_external'.
Defined.




Lemma copland_compile_at' : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (tr: list Ev),
    well_formed_r t ->
    copland_compile t {| st_ev := e; st_trace := tr; st_pl := n |} =
    (Some tt,
     {| st_ev := toRemote t n e;
        st_trace := tr ++ remote_events t n;
        st_pl := n;
     |}).
Proof.
  intros.
  rewrite at_evidence.
  rewrite at_events.
  
  assert (st_pl
            (execSt
               (copland_compile t)
               {| st_ev := e;
                  st_trace := [];
                  st_pl := n |}) = n) as H0.
  eapply pl_immut.
  eauto.
  rewrite <- H0 at 4.
  eapply copland_compile_external'.
Defined.


Lemma copland_compile_at : forall (t : AnnoTerm) (e : EvidenceC) (n : nat),
    well_formed_r t ->
    copland_compile t {| st_ev := e; st_trace := []; st_pl := n |} =
    (Some tt,
     {| st_ev := toRemote t n e;
        st_trace := remote_events t n;
        st_pl := n
     |}).
Proof.
  intros.
  rewrite at_evidence.
  rewrite at_events.
  eapply copland_compile_external; eauto.
Defined.

(*
Lemma copland_compile_par' :
  forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store) (tr:list Ev),
    well_formed t ->
    copland_compile t {| st_ev := e; st_trace := tr; st_pl := n; st_store := o |} =
    (Some tt,
     {|
       st_ev := parallel_vm_thread t n e;
       st_trace := tr ++ parallel_vm_events t n;
       st_pl := n;
       st_store :=
         st_store
           (execSt
              (copland_compile t)
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
               (copland_compile t)
               {| st_ev := e;
                  st_trace := [];
                  st_pl := n;
                  st_store := o |}) = n) as H0.
  eapply pl_immut.
  eauto.
  rewrite <- H0 at 4.
  eapply copland_compile_external'.
Defined.

Lemma copland_compile_par :
  forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store),
    well_formed t ->
    copland_compile t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |} =
    (Some tt,
     {|
       st_ev := parallel_vm_thread t n e;
       st_trace := parallel_vm_events t n;
       st_pl := n;
       st_store :=
         st_store
           ( execSt
               (copland_compile t)
                {| st_ev := e;
                   st_trace := [];
                   st_pl := n;
                   st_store := o |})
     |}).
Proof.
  intros.
  rewrite par_evidence.
  rewrite par_events.
  eapply copland_compile_external; eauto.
Defined. 
*)

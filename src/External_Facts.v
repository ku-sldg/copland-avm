Require Import Term ConcreteEvidence StVM Impl_vm Axioms_Io GenStMonad.

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

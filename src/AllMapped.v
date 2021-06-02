Require Import ConcreteEvidence StAM Maps.

Require Import Coq.Program.Tactics.

Inductive evMapped : EvidenceC -> AM_St -> Prop :=
| evMappedMt : forall m, evMapped mtc m
| evMappedU : forall p i args tid e' m st bs,
    m = st_aspmap st ->
    evMapped e' st -> 
    (exists j, bound_to m (p,i) j) -> 
    evMapped (uuc i args p tid bs e') st
| evMappedG : forall e' m p st bs,
    m = st_sigmap st ->
    evMapped e' st ->
    (exists j, bound_to m p j) ->
    evMapped (ggc p bs e') st
(*| evMappedH : forall e' p st,
    (*m = st_sigmap st -> *)
    evMapped e' st ->
    evMapped (hh p e') st    
*)
| evMappedN : forall e' bs nid st nm,
    nm = am_nonceMap st ->
    evMapped e' st ->
    (exists v, bound_to nm nid v) ->
    evMapped (nnc nid bs e') st

| evMappedS : forall e1 e2 st,
    evMapped e1 st ->
    evMapped e2 st ->
    evMapped (ssc e1 e2) st
| evMappedP : forall e1 e2 st,
    evMapped e1 st ->
    evMapped e2 st ->
    evMapped (ppc e1 e2) st.

Ltac debound :=
  match goal with
  | [H: bound_to _ _ _ |- _] => invc H
  end.

Ltac evMappedFacts :=
  match goal with
  | [H: evMapped (?C _) _ |- _] => invc H
  end;
  destruct_conjs;
  try debound.

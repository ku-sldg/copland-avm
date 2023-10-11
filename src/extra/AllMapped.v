Require Import ConcreteEvidence StAM Maps.

Require Import Coq.Program.Tactics.

(*
Inductive asp_hshMapped : Plc -> ASP_ID -> AM_St -> Prop :=
| is_asp_hshMapped: forall p i m st,
    m = st_hshmap st ->
    (exists j, bound_to m (p,i) j) ->
    asp_hshMapped p i st.
  
Inductive hshMapped : Evidence -> AM_St -> Prop :=
| hshMapped_mt: forall st,
    hshMapped mt st
| hshMapped_uu: forall m st et i args tpl tid,
    m = st_hshmap st ->
    hshMapped et st ->
    (exists bs, bound_to m (tpl,i) bs) ->
    hshMapped (uu i args tpl tid et) st
| hshMapped_gg: forall et st p,
    hshMapped et st ->
    hshMapped (gg p et) st
| hshMapped_hh: forall et st p,
    hshMapped et st ->
    hshMapped (hh p et) st
| hshMapped_nn: forall et st i,
    hshMapped et st ->
    hshMapped (nn i et) st
| hshMapped_ss: forall et1 et2 st,
    hshMapped et1 st ->
    hshMapped et2 st ->
    hshMapped (ss et1 et2) st
| hshMapped_pp: forall et1 et2 st,
    hshMapped et1 st ->
    hshMapped et2 st ->
    hshMapped (pp et1 et2) st. 
 *)


Inductive evMapped : Evidence -> AM_St -> Prop :=
| evMappedMt : forall m, evMapped mt m
| evMappedU : forall p i args tid e' m st,
    m = st_aspmap st ->
    evMapped e' st -> 
    (exists j, bound_to m (p,i) j) -> 
    evMapped (uu i args p tid e') st
| evMappedG : forall e' m p st,
    m = st_sigmap st ->
    evMapped e' st ->
    (exists j, bound_to m p j) ->
    evMapped (gg p e') st
| evMappedH : forall e' st p,
    (*hshMapped et st -> *)
    evMapped e' st ->
    evMapped (hh p e') st
(*| evMappedH : forall e' p st,
    (*m = st_sigmap st -> *)
    evMapped e' st ->
    evMapped (hh p e') st    
*)
| evMappedN : forall e' nid st nm,
    nm = am_nonceMap st ->
    evMapped e' st ->
    (exists v, bound_to nm nid v) ->
    evMapped (nn nid e') st

| evMappedS : forall e1 e2 st,
    evMapped e1 st ->
    evMapped e2 st ->
    evMapped (ss e1 e2) st
| evMappedP : forall e1 e2 st,
    evMapped e1 st ->
    evMapped e2 st ->
    evMapped (pp e1 e2) st.




(*
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
| evMappedH : forall et st p bs,
    (*hshMapped et st -> *)
    evMapped (hhc p bs et) st
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
*)

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

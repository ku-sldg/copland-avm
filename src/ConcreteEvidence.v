(*
Evidence structure that models concrete results of Copland phrase execution.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Export Term_Defs Term StructTactics.

Notation BS := nat (only parsing).

Require Import List.
Import ListNotations.

(*
Inductive BSV : Set :=
| bsval: BS -> BSV
| bshsh: list BSV -> BSV.
(*| bscons: BS -> BSV -> BSV. *)


Definition bs1 := bsval 42.
Definition bs2 := bshsh [(bsval 42)].
Print bs2.
*)

(** * Concrete Evidence *)

(*
Inductive EvidenceC: Set :=
| BitsV: BS -> EvidenceC
| PairBitsV: EvidenceC -> EvidenceC -> EvidenceC.


Inductive evidence_bs: AnnoTerm -> Plc -> Evidence -> EvidenceC -> Evidence -> Prop :=
| evcpy: forall r p et ec et',
    evidence_bs (aasp r CPY) p et ec et'.
*)


Inductive EvidenceC: Set :=
| mtc: EvidenceC
| uuc: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> BS -> EvidenceC -> EvidenceC
| ggc: Plc -> BS -> EvidenceC -> EvidenceC
| hhc: Plc -> BS -> Evidence -> EvidenceC
| nnc: N_ID -> BS -> (*EvidenceC ->*) EvidenceC
| ssc: EvidenceC -> EvidenceC -> EvidenceC
| ppc: EvidenceC -> EvidenceC -> EvidenceC.

Fixpoint et_fun (ec:EvidenceC) : Evidence :=
  match ec with
  | mtc => mt
  | uuc i l p tid _ ec' => uu i l p tid (et_fun ec')
  | ggc p _ ec' => gg p (et_fun ec')
  | hhc p _ et => hh p et (* TODO:  is this acceptable? *)
  | nnc ni _ => nn ni
  | ssc ec1 ec2 => ss (et_fun ec1) (et_fun ec2)
  | ppc ec1 ec2 => pp (et_fun ec1) (et_fun ec2)
  end.

Inductive EvSubT: Evidence -> Evidence -> Prop :=
| evsub_reflT : forall e : Evidence, EvSubT e e
| uuSubT: forall e e' i tid l tpl,
    EvSubT e e' ->
    EvSubT e (uu i l tpl tid e')
| ggSubT: forall e e' p,
    EvSubT e e' ->
    EvSubT e (gg p e')
| hhSubT: forall e e' p,
    EvSubT e e' ->
    EvSubT e (hh p e')
(*| nnSubT: forall e e' i,
    EvSubT e e' ->
    EvSubT e (nn i e') *)
| ssSublT: forall e e' e'',
    EvSubT e e' ->
    EvSubT e (ss e' e'')
| ssSubrT: forall e e' e'',
    EvSubT e e'' ->
    EvSubT e (ss e' e'')
| ppSublT: forall e e' e'',
    EvSubT e e' ->
    EvSubT e (pp e' e'')
| ppSubrT: forall e e' e'',
    EvSubT e e'' ->
    EvSubT e (pp e' e'').

Inductive EvSub: EvidenceC -> EvidenceC -> Prop :=

  (*
| evsub_refl : forall e : EvidenceC, EvSub e e
| evsub_pairl : forall e1 e e',
    EvSub e1 e ->
    EvSub e1 (PairBitsV e e')
| evsub_pairr : forall e2 e e',
    EvSub e2 e' ->
    EvSub e2 (PairBitsV e e').
*)

| uuSub: forall e e' i tid l tpl bs,
    EvSub e e' ->
    EvSub e (uuc i l tpl tid bs e')
| ggSub: forall e e' p bs,
    EvSub e e' ->
    EvSub e (ggc p bs e')
(*| hhSub: forall e et p bs,
    EvSubT (et_fun e) et ->
    EvSub e (hhc p bs et) *)
(*| hhSub: forall e e' p bs,
    EvSub e e' ->
    EvSub e (hhc p bs et) *)
(*| nnSub: forall e e' i bs,
    EvSub e e' ->
    EvSub e (nnc i bs e') *)
| ssSubl: forall e e' e'',
    EvSub e e' ->
    EvSub e (ssc e' e'')
| ssSubr: forall e e' e'',
    EvSub e e'' ->
    EvSub e (ssc e' e'')
| ppSubl: forall e e' e'',
    EvSub e e' ->
    EvSub e (ppc e' e'')
| ppSubr: forall e e' e'',
    EvSub e e'' ->
    EvSub e (ppc e' e'').

(*
Inductive EvBad': Evidence -> Prop :=
| ggBad: forall e e' p p',
    e = gg p' e' ->
    EvBad' (hh p e).

Inductive EvBad : Evidence -> Prop :=
| evIsBad: forall e e',
    EvSubT e e' ->
    EvBad' e ->
    EvBad e'.
*)








(*
| uuc: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> BS -> EvidenceC -> EvidenceC
 *)

Inductive Ev_Shape: EvidenceC -> Evidence -> Prop :=
| mtt: Ev_Shape mtc mt
| uut: forall id l tid tpl bs e et,
    Ev_Shape e et ->
    Ev_Shape (uuc id l tpl tid bs e ) (uu id l tpl tid et)
| ggt: forall p bs e et,
    Ev_Shape e et ->
    Ev_Shape (ggc p bs e) (gg p et)
| hht: forall bs p et,
    (*Ev_Shape e et -> *)
    Ev_Shape (hhc p bs et) (hh p et)
| nnt: forall bs i,
    Ev_Shape (nnc i bs) (nn i)
| sst: forall e1 e2 e1t e2t,
    Ev_Shape e1 e1t ->
    Ev_Shape e2 e2t ->
    Ev_Shape (ssc e1 e2) (ss e1t e2t)
| ppt: forall e1 e2 e1t e2t,
    Ev_Shape e1 e1t ->
    Ev_Shape e2 e2t ->
    Ev_Shape (ppc e1 e2) (pp e1t e2t).
Hint Constructors Ev_Shape : core.

Ltac evShapeFacts :=
  match goal with
  | [H: Ev_Shape (?C _) _ |- _] => invc H
  | [H: Ev_Shape _ (?C _) |- _] => invc H
  | [H: Ev_Shape _ mt |- _] => invc H
  | [H: Ev_Shape mtc _ |- _] => invc H
  end.
    
    (*
  | [H: Ev_Shape mtc _ |- _] => invc H
  | [H: Ev_Shape _ mt |- _] => invc H
  | [H: Ev_Shape (uuc _ _ _ _ _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (uu _ _ _ _ _) |- _] => invc H
  | [H: Ev_Shape (ggc _ _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (gg _ _) |- _] => invc H
  | [H: Ev_Shape (hhc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (hh _ _) |- _] => invc H
  | [H: Ev_Shape (nnc _ _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (nn _ _) |- _] => invc H
  | [H: Ev_Shape (ssc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (ss _ _) |- _] => invc H
  | [H: Ev_Shape (ppc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (pp _ _) |- _] => invc H
     
    
  end.
*)

Lemma ev_evshape: forall ec,
    Ev_Shape ec (et_fun ec).
Proof.
  intros.
  induction ec; intros.
  -
    eauto.
  -
    econstructor; eauto.
  -
    econstructor; eauto.
  -
    econstructor; eauto.
  -
     econstructor; eauto.
  -
    econstructor; eauto.
  -
    econstructor; eauto.
Defined.

(* TODO: perhaps an equality modulo "measuring place" *)
Lemma evshape_determ: forall ec et et',
  Ev_Shape ec et ->
  Ev_Shape ec et' ->
  et = et'.
Proof.
  induction ec; intros;
    try 
    (repeat evShapeFacts;
     tauto).
  -
    repeat evShapeFacts.
    assert (et1 = et0) by eauto.
    congruence.
  -
    repeat evShapeFacts.
    assert (et1 = et0) by eauto.
    congruence.
    (*
  -
    repeat evShapeFacts.
    assert (et1 = et0) by eauto.
    congruence.  *)
  -
    repeat evShapeFacts.
    
    assert (e1t0 = e1t) by eauto.
    assert (e2t0 = e2t) by eauto.
    congruence.
  -
    repeat evShapeFacts.
    
    assert (e1t0 = e1t) by eauto.
    assert (e2t0 = e2t) by eauto.
    congruence. 
Defined.

Lemma ev_shape_transitive : forall e e' et et',
    Ev_Shape e et ->
    Ev_Shape e' et ->
    Ev_Shape e et' ->
    Ev_Shape e' et'.
Proof.
  intros.
  generalizeEverythingElse et.
  induction et; intros;
    try
      (repeat evShapeFacts; eauto).
Defined.

(*
    
(** * Types *)
Inductive ET: Plc -> EvidenceC -> Evidence -> Prop :=
| mtt: forall p, ET p mtc mt
(* | kkt: forall id A p q bs e et,
    ET p e et -> 
    ET p (kkc id A q bs e) (kk id p q A et) *)
| uut: forall id p bs e et,
    ET p e et -> 
    ET p (uuc id bs e) (uu id p et)
| ggt: forall n p bs e et,
    ET n e et ->
    ET n (ggc p bs e) (gg p et)
| hht: forall n p bs e et,
    ET n e et ->
    ET n (hhc bs e) (hh p et)
| nnt: forall p bs e et i,
    ET p e et ->
    ET p (nnc i bs e) (nn i et)
| sst: forall p e1 e2 e1t e2t,
    ET p e1 e1t ->
    ET p e2 e2t ->
    ET p (ssc e1 e2) (ss e1t e2t)
| ppt: forall p e1 e2 e1t e2t,
    ET p e1 e1t ->
    ET p e2 e2t ->
    ET p (ppc e1 e2) (pp e1t e2t).
Hint Constructors ET.

Theorem et_et_fun : forall p ec,
    ET p ec (et_fun p ec).
Proof.
  intros.
  generalize dependent p.
  induction ec; intros; try (simpl; eauto).
Defined.
*)



Definition splitEv_l (sp:Split) (e:EvidenceC): EvidenceC :=
  match sp with
  | RIGHT => mtc
  | _ => e
  end.

Definition splitEv_r (sp:Split) (e:EvidenceC): EvidenceC :=
  match sp with
  | LEFT => mtc
  | _ => e
  end.

(*

(** * Eval function definition *)
Definition splitEv (sp:SP) (e:EvidenceC) : EvidenceC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.
*)


(*
Evidence structure that models concrete results of Copland phrase execution.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Export Term_Defs Term StructTactics.

Require Import List.
Import ListNotations.

Notation BS := nat (only parsing).

(** * Concrete Evidence *)

Inductive EvidenceC: Set :=
| mtc: EvidenceC
| nnc: N_ID -> BS -> EvidenceC
| uuc: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> BS -> EvidenceC -> EvidenceC
| ggc: Plc -> BS -> EvidenceC -> EvidenceC
| hhc: Plc -> BS -> Evidence -> EvidenceC
| ssc: EvidenceC -> EvidenceC -> EvidenceC
| ppc: EvidenceC -> EvidenceC -> EvidenceC.

Definition EvBits := list BS.

Inductive EvC: Set :=
| evc: EvBits -> Evidence -> EvC.

Definition mt_evc: EvC := (evc [] mt).

Definition get_et (e:EvC) : Evidence :=
  match e with
  | evc ec et => et
  end.

Definition get_bits (e:EvC): list BS :=
  match e with
  | evc ls _ => ls
  end.

Inductive wf_ec : EvC -> Prop :=
| wf_ec_c: forall ls et,
    length ls = et_size et ->
    wf_ec (evc ls et).

Fixpoint et_fun (ec:EvidenceC) : Evidence :=
  match ec with
  | mtc => mt
  | uuc i l p tid _ ec' => uu i l p tid (et_fun ec')
  | ggc p _ ec' => gg p (et_fun ec')
  | hhc p _ et => hh p et
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
Hint Constructors EvSubT : core.

Ltac evSubTFacts :=
  match goal with
  | [H: EvSubT (?C _) _ |- _] => invc H
  | [H: EvSubT _ (?C _) |- _] => invc H
  | [H: EvSubT _ mt |- _] => invc H
  | [H: EvSubT mt _ |- _] => invc H
  end.

Inductive EvSub: EvidenceC -> EvidenceC -> Prop :=
| evsub_refl : forall e : EvidenceC, EvSub e e
| uuSub: forall e e' i tid l tpl bs,
    EvSub e e' ->
    EvSub e (uuc i l tpl tid bs e')
| ggSub: forall e e' p bs,
    EvSub e e' ->
    EvSub e (ggc p bs e')
| hhSub: forall e et p bs,
    EvSubT (et_fun e) et ->
    EvSub e (hhc p bs et)
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
Hint Constructors EvSub : core.

Ltac evSubFacts :=
  match goal with
  | [H: EvSub (?C _) _ |- _] => invc H
  | [H: EvSub _ (?C _) |- _] => invc H
  | [H: EvSub _ mt |- _] => invc H
  | [H: EvSub mtc _ |- _] => invc H
  end.

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

Inductive Ev_Shape: EvidenceC -> Evidence -> Prop :=
| mtt: Ev_Shape mtc mt
| uut: forall id l tid tpl bs e et,
    Ev_Shape e et ->
    Ev_Shape (uuc id l tpl tid bs e ) (uu id l tpl tid et)
| ggt: forall p bs e et,
    Ev_Shape e et ->
    Ev_Shape (ggc p bs e) (gg p et)
| hht: forall bs p et,
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

Lemma ev_evshape: forall ec,
    Ev_Shape ec (et_fun ec).
Proof.
  intros.
  induction ec; intros;
    try econstructor;
    eauto.
Defined.

(* TODO: perhaps an equality modulo "measuring place" *)
Lemma evshape_determ: forall ec et et',
  Ev_Shape ec et ->
  Ev_Shape ec et' ->
  et = et'.
Proof.
  induction ec; intros;
    repeat evShapeFacts;
    try (assert (et1 = et0) by eauto);
    try (assert (e1t0 = e1t) by eauto);
    try (assert (e2t0 = e2t) by eauto);
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
    repeat evShapeFacts;
    eauto.
Defined.

Definition splitEv_l (sp:Split) (e:EvC): EvC :=
  match sp with
  | (ALL, _) => e
  | _ => mt_evc
  end.

Definition splitEv_r (sp:Split) (e:EvC): EvC :=
  match sp with
  | (_,ALL) => e
  | _ => mt_evc
  end.

(*
Definition splitEv (sp:SP) (e:EvidenceC) : EvidenceC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.
*)

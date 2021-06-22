Require Import Term_Defs Term StAM Maps ConcreteEvidence (*MonadAM*).

Require Import StructTactics.

Require Import List.
Import ListNotations.

Require Import alt_Impl_appraisal OptMonad.


Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args tpl tid, evidenceEvent (umeas n p i args tpl tid).

Definition measEvent (t:AnnoTerm) (p:Plc) (e:Evidence) (ev:Ev) : Prop :=
  events t p e ev /\ evidenceEvent ev.

Inductive appEvent_EvidenceC : Ev -> EvidenceC -> Prop :=
  aeuc: forall i args tpl tid e e' n p,
    EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e') e ->
    appEvent_EvidenceC (umeas n p i args tpl tid) e
| ahuc: forall i args tpl tid e' et n p pi bs e,
    EvSubT (uu i args tpl tid  e') et ->
    EvSub (hhc pi (checkHash et pi bs) et) e ->
    appEvent_EvidenceC (umeas n p i args tpl tid) e.

Ltac measEventFacts :=
  match goal with
  | [H: measEvent _ _ _ _ |- _] => invc H
  end.

Ltac evEventFacts :=
  match goal with
  | [H: evidenceEvent _ |- _] => invc H
  end.

Ltac invEvents :=
  match goal with
  | [H: events _ _ _ _  |- _] => invc H
  end.

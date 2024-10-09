(*
EvidenceT structure that models concrete results of Copland phrase execution.

Author:  Adam Petz, ampetz@ku.edu
*)

(*
Require Export Term_Defs Term StructTactics.
*)

Notation BS := nat (only parsing).
Notation Plc := nat (only parsing).
Notation ASP_ID := nat (only parsing).
Notation N_ID := nat (only parsing).
Notation Arg := nat (only parsing).

(** * Concrete EvidenceT *)
Inductive EvidenceTC: Set :=
| mtc: EvidenceTC
| uuc: ASP_ID -> list Arg -> Plc -> BS -> EvidenceTC -> EvidenceTC
| ggc: Plc -> BS -> EvidenceTC -> EvidenceTC
| nnc: N_ID -> BS -> EvidenceTC -> EvidenceTC.

Inductive EvSub: EvidenceTC -> EvidenceTC -> Prop :=
| evsub_refl : forall e : EvidenceTC, EvSub e e
| uuSub: forall e e' i l p bs,
    EvSub e e' ->
    EvSub e (uuc i l p bs e')
| ggSub: forall e e' p bs,
    EvSub e e' ->
    EvSub e (ggc p bs e')
| nnSub: forall e e' i bs,
    EvSub e e' ->
    EvSub e (nnc i bs e').

Lemma mt_sub_all: forall e,
    EvSub mtc e.
Proof.
  induction e; intros;
    (econstructor; eauto; tauto).
Defined.

Lemma evSub_trans: forall e e' e'',
  EvSub e e' ->
  EvSub e' e'' ->
  EvSub e e''.
Proof.
  induction e; destruct e'; intros;
    try (eapply mt_sub_all; eauto);
    try (inversion H; tauto).
  -
    inversion H; subst; clear H.
    eassumption.
    
Abort.


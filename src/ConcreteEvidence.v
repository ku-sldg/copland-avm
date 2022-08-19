(*
Evidence structure that models concrete results of Copland phrase execution.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import StructTactics Defs. (*AutoPrim. *)

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Require Export Term_Defs.

(** * Concrete Evidence 
    This datatype acts as a "Typed Concrete Evidence" structure.  It captures
    both the type of evidence (parameters associated with its collection) 
    along with concrete binary (BS) values collected during attestation.
*)

Inductive EvidenceC: Set :=
| mtc: EvidenceC
| nnc: N_ID -> BS -> EvidenceC
| ggc: Plc -> ASP_PARAMS -> BS -> EvidenceC -> EvidenceC
| hhc: Plc -> ASP_PARAMS -> BS -> Evidence -> EvidenceC
| eec: Plc -> ASP_PARAMS -> BS -> EvidenceC -> EvidenceC
| kkc: Plc -> ASP_PARAMS -> Evidence -> EvidenceC
| ssc: EvidenceC -> EvidenceC -> EvidenceC.

(** The Evidence Type associated with a Typed Concrete Evidence value *)
Fixpoint et_fun (ec:EvidenceC) : Evidence :=
  match ec with
  | mtc => mt
  | ggc p params _ ec' => uu p EXTD params (et_fun ec')
  | hhc p params _ et => uu p COMP params et
  | eec p params _ ec' => uu p ENCR params mt (* (et_fun ec') *)
  | kkc p params et' => uu p KILL params et'
  | nnc ni _ => nn ni
  | ssc ec1 ec2 => ss (et_fun ec1) (et_fun ec2)
  end.

(** Evidence Type subterm relation *)
Inductive EvSubT: Evidence -> Evidence -> Prop :=
| evsub_reflT : forall e : Evidence, EvSubT e e
                                       (*
| ggSubT: forall e e' p ps,
    EvSubT e e' ->
    EvSubT e (gg p ps e')
| hhSubT: forall e e' p ps,
    EvSubT e e' ->
    EvSubT e (hh p ps e')
                                        *)
| uuSubT: forall e e' p fwd ps,
    EvSubT e e' -> 
    EvSubT e (uu p fwd ps e')
| ssSublT: forall e e' e'',
    EvSubT e e' ->
    EvSubT e (ss e' e'')
| ssSubrT: forall e e' e'',
    EvSubT e e'' ->
    EvSubT e (ss e' e'').
#[export] Hint Constructors EvSubT : core.

Ltac evSubTFacts :=
  match goal with
  | [H: EvSubT (?C _) _ |- _] => invc H
  | [H: EvSubT _ (?C _) |- _] => invc H
  | [H: EvSubT _ mt |- _] => invc H
  | [H: EvSubT mt _ |- _] => invc H
  end.

Lemma evsubT_transitive: forall e e' e'',
    EvSubT e e' ->
    EvSubT e' e'' ->
    EvSubT e e''.
Proof.
  intros.
  generalizeEverythingElse e''.
  induction e''; intros;
    try evSubTFacts;
       eauto.
Defined.

(** Typed Concrete Evidence subterm relation *)
Inductive EvSub: EvidenceC -> EvidenceC -> Prop :=
| evsub_refl : forall e : EvidenceC, EvSub e e
| ggSub: forall e e' p ps bs,
    EvSub e e' ->
    EvSub e (ggc p ps bs e')
          (* TODO: encrypt case here? *)
| ssSubl: forall e e' e'',
    EvSub e e' ->
    EvSub e (ssc e' e'')
| ssSubr: forall e e' e'',
    EvSub e e'' ->
    EvSub e (ssc e' e'').
#[export] Hint Constructors EvSub : core.

Ltac evSubFacts :=
  match goal with
  | [H: EvSub (?C _) _ |- _] => invc H
  | [H: EvSub _ (?C _) |- _] => invc H
  | [H: EvSub _ mtc |- _] => invc H
  | [H: EvSub mtc _ |- _] => invc H
  end.

(** Subterm relation is preserved through et_fun *)
Lemma evsub_etfun: forall e e',
    EvSub e e' ->
    EvSubT (et_fun e) (et_fun e').
Proof.
  intros.
  induction H; intros;
    cbn in *; eauto.
Defined.

Lemma evsub_hh: forall e e' e0,
    EvSub e0 e' ->
    EvSubT (et_fun e') e ->
    EvSubT (et_fun e0) e.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros; ff.
  -
    invc H0.
    jkjke.
    assert (e' = mtc).
    {
      destruct e'; try solve_by_inversion.
    }
    (*
        
    assert (e' = mtc \/ exists p params, e' = (kkc p params)).
    {
      destruct e'; try solve_by_inversion.
      right. eauto.
    }
    door;
    subst;
    solve_by_inversion.
     *)
    subst.
    ff.
  -
    invc H0.
    jkjke.
    destruct e'; try solve_by_inversion.
    ff.
  -
    invc H0.

    (*
    +
      assert (exists bs ec, e' = ggc p a bs ec).
      {
        destruct e'; ff.
        repeat eexists.
      }
      destruct_conjs.
      subst.
      ff.
      invc H.
      ++
        ff.
      ++

        assert (EvSubT (et_fun e0) (et_fun H1)).
        {
          eapply IHe.
          eassumption.
          econstructor.
        }
        apply ggSubT. eassumption.
     *)
    +
      destruct f.
      ++
        destruct e'; ff.
          
      ++
        destruct e'; ff.
          
      ++
        destruct e'; ff.
        invc H; ff; eauto.

      ++
        destruct e'; ff.
          
    +
      eauto.
  -
    invc H0.
    +
      destruct e'; ff.
      invc H; ff; eauto.
    +
      eauto.
    +
      eauto.   
Qed.

Lemma evsub_transitive: forall e e' e'',
    EvSub e e' ->
    EvSub e' e'' ->
    EvSub e e''.
Proof.
  intros e e' e'' H H0.
  generalizeEverythingElse e''.
  induction e''; intros; ff; invc H0; eauto.
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

Definition splitEvl (sp:Split) (e:EvidenceC) : EvidenceC :=
  match sp with
  | (ALL,_) => e
  | _ => mtc
  end.

Definition splitEvr (sp:Split) (e:EvidenceC) : EvidenceC :=
  match sp with
  | (_,ALL) => e
  | _ => mtc
  end.

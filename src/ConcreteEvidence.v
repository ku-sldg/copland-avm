(*
  EvidenceT structure (EvidenceTC) that encapsulates and describes concrete results of 
    Copland phrase execution.  Also included: EvidenceT subterm defintions and related properties.

  Author:  Adam Petz, ampetz@ku.edu
*)

Require Import StructTactics Defs.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Require Export Term_Defs.

(** * Concrete EvidenceT 
    This datatype acts as a "Typed Concrete EvidenceT" structure.  It captures
    both the type of EvidenceT (parameters associated with its collection) 
    along with concrete binary (BS) values collected during attestation.
*)

Inductive EvidenceTC :=
| mtc: EvidenceTC
| nonce_evtc: N_ID -> BS -> EvidenceTC
| ggc: Plc -> ASP_PARAMS -> RawEv -> EvidenceTC -> EvidenceTC
| hhc: Plc -> ASP_PARAMS -> BS -> EvidenceT -> EvidenceTC
| eec: Plc -> ASP_PARAMS -> BS -> EvidenceT -> EvidenceTC
| kkc: Plc -> ASP_PARAMS -> EvidenceT -> EvidenceTC
| kpc: Plc -> ASP_PARAMS -> EvidenceTC -> EvidenceTC
| ssc: EvidenceTC -> EvidenceTC -> EvidenceTC.

(** The EvidenceT Type associated with a Typed Concrete EvidenceT value *)
Fixpoint et_fun (ec:EvidenceTC) : EvidenceT :=
  match ec with
  | mtc => mt_evt
  | ggc p params rawev ec' => asp_evt p (EXTD (length rawev)) params (et_fun ec')
  | hhc p params _ et => asp_evt p COMP params et
  | eec p params _ et => asp_evt p ENCR params et (* (et_fun ec') *)
  | kkc p params et' => asp_evt p KILL params et'
  | kpc p params ec' => asp_evt p KEEP params (et_fun ec')
                       
  | nonce_evtc ni _ => nonce_evt ni
  | ssc ec1 ec2 => split_evt (et_fun ec1) (et_fun ec2)
  end.

Definition splitEv_l (sp:Split) (e:Evidence): Evidence :=
  match sp with
  | (ALL, _) => e
  | _ => mt_evc
  end.

Definition splitEv_r (sp:Split) (e:Evidence): Evidence :=
  match sp with
  | (_,ALL) => e
  | _ => mt_evc
  end.

Definition splitEvl (sp:Split) (e:EvidenceTC) : EvidenceTC :=
  match sp with
  | (ALL,_) => e
  | _ => mtc
  end.

Definition splitEvr (sp:Split) (e:EvidenceTC) : EvidenceTC :=
  match sp with
  | (_,ALL) => e
  | _ => mtc
  end.

(** EvidenceT Type subterm relation *)
Inductive EvSubT: EvidenceT -> EvidenceT -> Prop :=
| evsub_reflT : forall e : EvidenceT, EvSubT e e
| uuSubT: forall e e' p fwd ps,
    EvSubT e e' -> 
    EvSubT e (asp_evt p fwd ps e')
| ssSublT: forall e e' e'',
    EvSubT e e' ->
    EvSubT e (split_evt e' e'')
| ssSubrT: forall e e' e'',
    EvSubT e e'' ->
    EvSubT e (split_evt e' e'').
#[export] Hint Constructors EvSubT : core.

Ltac evSubTFacts :=
  match goal with
  | [H: EvSubT (?C _) _ |- _] => invc H
  | [H: EvSubT _ (?C _) |- _] => invc H
  | [H: EvSubT _ mt_evt|- _] => invc H
  | [H: EvSubT mt_evt_ |- _] => invc H
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
Qed.

(** Typed Concrete EvidenceT subterm relation *)
Inductive EvSub: EvidenceTC -> EvidenceTC -> Prop :=
| evsub_refl : forall e : EvidenceTC, EvSub e e
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
Qed.

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
    subst.
    ff.
      
  -
    invc H0.
    jkjke.
    destruct e'; try solve_by_inversion.
    ff.
  -
    invc H0.
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
Qed.
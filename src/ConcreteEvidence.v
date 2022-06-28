(*
Evidence structure that models concrete results of Copland phrase execution.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import StructTactics Defs. (*AutoPrim. *)

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Require Export Term_Defs.

(** * Concrete Evidence *)

Inductive EvidenceC: Set :=
| mtc: EvidenceC
| nnc: N_ID -> BS -> EvidenceC
                     (*
| uuc: ASP_PARAMS -> (*ASP_ID -> (list Arg) -> Plc -> TARG_ID -> 
       Evidence -> *) Plc -> BS -> EvidenceC -> EvidenceC
*)
| ggc: Plc -> ASP_PARAMS -> BS -> EvidenceC -> EvidenceC
| hhc: Plc -> ASP_PARAMS -> BS -> Evidence -> EvidenceC
| ssc: EvidenceC -> EvidenceC -> EvidenceC.
                                 (*
| ppc: EvidenceC -> EvidenceC -> EvidenceC. *)

Fixpoint et_fun (ec:EvidenceC) : Evidence :=
  match ec with
  | mtc => mt
            (*
  | uuc (*i args tpl tid tet*) params q _ ec' =>
      uu (*i args tpl tid tet*) params q (et_fun ec') *)
  | ggc p params _ ec' => gg p params (et_fun ec')
  | hhc p params _ et => hh p params et
  | nnc ni _ => nn ni
  | ssc ec1 ec2 => ss (et_fun ec1) (et_fun ec2)
  end.
    
                     (*
  | ppc ec1 ec2 => pp (et_fun ec1) (et_fun ec2) 
  end. *)

(*
Definition encodeEvBits (e:EvC): BS :=
  match e with
  | (evc bits _) => encodeEvRaw bits
  end.
*)

Inductive EvSubT: Evidence -> Evidence -> Prop :=
| evsub_reflT : forall e : Evidence, EvSubT e e
                                       (*
| uuSubT: forall e e' params (*i args tpl tid tet *) q,
    EvSubT e e' ->
    EvSubT e (uu params (*i args tpl tid tet*) q e') *)
| ggSubT: forall e e' p ps,
    EvSubT e e' ->
    EvSubT e (gg p ps e')
| hhSubT: forall e e' p ps,
    EvSubT e e' ->
    EvSubT e (hh p ps e')
| ssSublT: forall e e' e'',
    EvSubT e e' ->
    EvSubT e (ss e' e'')
| ssSubrT: forall e e' e'',
    EvSubT e e'' ->
    EvSubT e (ss e' e'').
           (*
| ppSublT: forall e e' e'',
    EvSubT e e' ->
    EvSubT e (pp e' e'')
| ppSubrT: forall e e' e'',
    EvSubT e e'' ->
    EvSubT e (pp e' e''). *)
Hint Constructors EvSubT : core.

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

Inductive EvSub: EvidenceC -> EvidenceC -> Prop :=
| evsub_refl : forall e : EvidenceC, EvSub e e
                                      (*
| uuSub: forall e e' params (*i args tpl tid tet*) q bs,
    EvSub e e' ->
    EvSub e (uuc params (*i args tpl tid tet*) q bs e') *)
| ggSub: forall e e' p ps bs,
    EvSub e e' ->
    EvSub e (ggc p ps bs e')
(*| hhSub: forall e et p bs,
    EvSubT (et_fun e) et ->
    EvSub e (hhc p bs et) *)
| ssSubl: forall e e' e'',
    EvSub e e' ->
    EvSub e (ssc e' e'')
| ssSubr: forall e e' e'',
    EvSub e e'' ->
    EvSub e (ssc e' e'').
          (*
| ppSubl: forall e e' e'',
    EvSub e e' ->
    EvSub e (ppc e' e'')
| ppSubr: forall e e' e'',
    EvSub e e'' ->
    EvSub e (ppc e' e''). *)
Hint Constructors EvSub : core.

Ltac evSubFacts :=
  match goal with
  | [H: EvSub (?C _) _ |- _] => invc H
  | [H: EvSub _ (?C _) |- _] => invc H
  | [H: EvSub _ mtc |- _] => invc H
  | [H: EvSub mtc _ |- _] => invc H
  end.


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
  induction e; intros; fff.
  -
    invc H0.
    jkjke.
    assert (e' = mtc).
    {
      destruct e'; try solve_by_inversion.
    }
    subst.
    invc H.
    fff.
  -
    invc H0.
    jkjke.
    destruct e'; try solve_by_inversion.
    invc H.
    ff.

    (*


    
  -
    invc H0.
    +
      assert (exists bs ec, e' = uuc a p bs ec).
      {
        destruct e'; try solve_by_inversion.
        fff.
        repeat eexists.
      }
      destruct_conjs.
      subst.
      fff.
      invc H.
      ++
        fff.
      ++
        
        assert (EvSubT (et_fun e0) (et_fun H1)).
        {
          eauto.
          (*
          eapply IHe.
          eassumption.
          econstructor. *)
        }
        apply uuSubT. eassumption.
    +
      assert (EvSubT (et_fun e0) e) by eauto.
      apply uuSubT. eassumption.
*)
  -
    invc H0.
    +
      assert (exists bs ec, e' = ggc p a bs ec).
      {
        destruct e'; try solve_by_inversion.
        fff.
        repeat eexists.
      }
      destruct_conjs.
      subst.
      fff.
      invc H.
      ++
        fff.
      ++

        assert (EvSubT (et_fun e0) (et_fun H1)).
        {
          eapply IHe.
          eassumption.
          econstructor.
        }
        apply ggSubT. eassumption.
    +
      assert (EvSubT (et_fun e0) e) by eauto.
      apply ggSubT. eassumption.
  -
    invc H0.
    +
      assert (exists bs, e' = hhc p a bs e).
      {
        destruct e'; try solve_by_inversion.
        fff.
        repeat eexists.
      }
      destruct_conjs.
      subst.
      fff.
    +
      assert (EvSubT (et_fun e0) e) by eauto.
      apply hhSubT. eassumption.
      (*
  -
    invc H0.
    assert (exists bs, e' = nnc n bs).
    {
      destruct e'; try solve_by_inversion.
      fff.
      repeat eexists.
    }
    destruct_conjs.
    subst.
    fff.
*)
  -
    
    assert ((exists e1 e2, e' = ssc e1 e2) \/
            EvSubT (et_fun e') e1 \/
            EvSubT (et_fun e') e2).
    {
      invc H0.
      +
        destruct e'; try solve_by_inversion.
        fff.
        left.
        repeat eexists.
      +
        eauto.
      +
        eauto.
    }
    door.
    +
      destruct_conjs.
      subst.
      
      
      fff.
      invc H.
      
      ++
        fff.
      ++
        assert (EvSubT (ss (et_fun H1) (et_fun H2)) e1 \/
                EvSubT (ss (et_fun H1) (et_fun H2)) e2 \/
                e1 = (et_fun H1) /\ e2 = (et_fun H2)).
        {
          invc H0.
          +++
            right.
            right.
            eauto.
          +++
            left.
            eauto.
          +++
            eauto.
        }
        door.
        +++
          eauto.
        +++
          door.
          ++++
            eauto.
          ++++
            subst.
            eauto.
      ++
        assert (EvSubT (ss (et_fun H1) (et_fun H2)) e1 \/
                EvSubT (ss (et_fun H1) (et_fun H2)) e2 \/
                e1 = (et_fun H1) /\ e2 = (et_fun H2)).
        {
          invc H0.
          +++
            right.
            right.
            eauto.
          +++
            left.
            eauto.
          +++
            eauto.
        }
        door.
        +++
          eauto.
        +++
          door.
          ++++
            eauto.
          ++++
            subst.
            eauto.
    +
      door.
      eauto.
      eauto.


      (*


  - (* ppc case *)
    
    assert ((exists e1 e2, e' = ppc e1 e2) \/
            EvSubT (et_fun e') e1 \/
            EvSubT (et_fun e') e2).
    {
      invc H0.
      +
        destruct e'; try solve_by_inversion.
        fff.
        left.
        repeat eexists.
      +
        eauto.
      +
        eauto.
    }
    door.
    +
      destruct_conjs.
      subst.
      
      
      fff.
      invc H.
      
      ++
        fff.
      ++
        assert (EvSubT (pp (et_fun H1) (et_fun H2)) e1 \/
                EvSubT (pp (et_fun H1) (et_fun H2)) e2 \/
                e1 = (et_fun H1) /\ e2 = (et_fun H2)).
        {
          invc H0.
          +++
            right.
            right.
            eauto.
          +++
            left.
            eauto.
          +++
            eauto.
        }
        door.
        +++
          eauto.
        +++
          door.
          ++++
            eauto.
          ++++
            subst.
            eauto.
      ++
        assert (EvSubT (pp (et_fun H1) (et_fun H2)) e1 \/
                EvSubT (pp (et_fun H1) (et_fun H2)) e2 \/
                e1 = (et_fun H1) /\ e2 = (et_fun H2)).
        {
          invc H0.
          +++
            right.
            right.
            eauto.
          +++
            left.
            eauto.
          +++
            eauto.
        }
        door.
        +++
          eauto.
        +++
          door.
          ++++
            eauto.
          ++++
            subst.
            eauto.
    +
      door.
      eauto.
      eauto.
       *)

      
Qed.

Lemma evsub_transitive: forall e e' e'',
    EvSub e e' ->
    EvSub e' e'' ->
    EvSub e e''.
Proof.
  intros e e' e'' H H0.
  generalizeEverythingElse e''.
  induction e''; intros; fff; invc H0; eauto.
Defined.

(*
Inductive Ev_Shape: EvidenceC -> Evidence -> Prop :=
| mtt: Ev_Shape mtc mt
| uut: forall params q bs e et,
    Ev_Shape e et ->
    Ev_Shape (uuc params q bs e ) (uu params q et)
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
*)

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

(*
Definition peel_bs (ls:RawEv) : option (BS * RawEv) :=
  match ls with
  | bs :: ls' => Some (bs, ls')
  | _ => None
  end.
*)

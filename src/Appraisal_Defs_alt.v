Require Import Term_Defs Term StAM Maps ConcreteEvidence (*MonadAM*).

Require Import StructTactics.

Require Import List.
Import ListNotations.

Require Import alt_Impl_appraisal OptMonad.


Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args tpl tid, evidenceEvent (umeas n p i args tpl tid).

Definition measEvent (t:AnnoTerm) (p:Plc) (e:Evidence) (ev:Ev) : Prop :=
  events t p e ev /\ evidenceEvent ev.

Inductive appEvent_Evidence : Ev -> EvidenceC -> Prop :=
  aeu: forall i args tpl tid e n p,
    EvSub (BitsV (checkASP i args tpl tid n)) e ->
    appEvent_Evidence (umeas n p i args tpl tid) e
| ahu: forall i args tpl tid e' et n p pi bs e,
    EvSubT (uu i args tpl tid  e') et ->
    EvSub (BitsV (checkHash et pi bs)) e ->
    appEvent_Evidence (umeas n p i args tpl tid) e.

Inductive appEvent_EvidenceC : Ev -> EvidenceC -> Prop :=
  aeuc: forall i args tpl tid e n p,
    EvSub (BitsV (checkASP i args tpl tid n)) e ->
    appEvent_EvidenceC (umeas n p i args tpl tid) e
| ahuc: forall i args tpl tid e' et n p pi bs e,
    EvSubT (uu i args tpl tid  e') et ->
    EvSub (BitsV (checkHash et pi bs)) e ->
    appEvent_EvidenceC (umeas n p i args tpl tid) e.



(*
Inductive hsh_appEvent: Ev -> Evidence -> Prop :=
| hshappev: forall n p i args tpl tid e e',
    EvSubT (uu i args tpl tid e) e' ->
    hsh_appEvent (umeas n p i args tpl tid) e'.
 *)

(*
Inductive Evidence: Set :=
| mt: Evidence
| uu: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> Evidence -> Evidence
| gg: Plc -> Evidence -> Evidence
| hh: Plc -> Evidence -> Evidence
| nn: N_ID -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence
| pp: Evidence -> Evidence -> Evidence.
*)






(*
Fixpoint evidence_size (e:Evidence): nat :=
  match e with
  | mt => 0
  | uu _ _ _ _ e' => 1 + evidence_size e'
  | gg _ e' => 1 + evidence_size e'
  | hh _ e' => 1 + evidence_size e'
  | nn _ e' => 1 + evidence_size e'
  | ss e1 e2 => (evidence_size e1) + (evidence_size e2)
  | pp e1 e2 => (evidence_size e1) + (evidence_size e2)
  end.
    
  



  
Inductive EvidenceC: Set :=
| mtc: EvidenceC
| uuc: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> BS -> EvidenceC -> EvidenceC
| ggc: Plc -> BS -> EvidenceC -> EvidenceC
| hhc: Plc -> BS -> Evidence -> EvidenceC
| nnc: N_ID -> BS -> EvidenceC
| ssc: EvidenceC -> EvidenceC -> EvidenceC
| ppc: EvidenceC -> EvidenceC -> EvidenceC.

Inductive Evidence_Cannon: Set :=
| OBS: BS -> Evidence_Cannon
| RBS: BS -> Evidence_Cannon -> Evidence_Cannon
| PBS: Evidence_Cannon -> Evidence_Cannon -> Evidence_Cannon.

Definition Evidence_Cannon' := list BS.

Fixpoint to_cannon' (e:EvidenceC): Evidence_Cannon' :=
  match e with
  | mtc => []
  | uuc _ _ _ _ bs e' => bs :: (to_cannon' e')
  | ggc _ bs e' => bs :: (to_cannon' e')
  | hhc _ bs _ => [bs]
  | nnc bs e' => [bs]
  | ssc e1 e2 => (to_cannon' e1) ++ (to_cannon' e2)
  | ppc e1 e2 => (to_cannon' e1) ++ (to_cannon' e2)
  end.

Fixpoint to_cannon (e:EvidenceC): Evidence_Cannon :=
  match e with
  | mtc => OBS 0
  | uuc _ _ _ _ bs e' => RBS bs (to_cannon e')
  | ggc _ bs e' => RBS bs (to_cannon e')
  | hhc _ bs _ => OBS bs
  | nnc bs e' => OBS bs
  | ssc e1 e2 => PBS (to_cannon e1) (to_cannon e2)
  | ppc e1 e2 => PBS (to_cannon e1) (to_cannon e2)
  end.

Fixpoint from_cannon (c:Evidence_Cannon) (et:Evidence): EvidenceC :=
  match (et,c) with
  | (mt, OBS 0) => mtc
  | (uu i args tpl tid et', RBS bs c') =>
    uuc i args tpl tid bs
        (from_cannon c' et')
  | (gg p et', RBS bs c') =>
    ggc p bs
        (from_cannon c' et')
  | (nn nid et', OBS bs) =>
    nnc nid bs
  | (ss e1 e2, PBS c1 c2) =>
    ssc (from_cannon c1 e1) (from_cannon c2 e2)
  | (pp e1 e2, PBS c1 c2) =>
    ppc (from_cannon c1 e1) (from_cannon c2 e2)
  | _ => mtc
  end.



Fixpoint from_cannon' (c:Evidence_Cannon') (et:Evidence): option EvidenceC :=
  match (et,c) with
  | (mt, []) => Some mtc
  | (uu i args tpl tid et', bs :: c') =>
    ec' <- from_cannon' c' et' ;;
    ret (uuc i args tpl tid bs ec')
  | (gg p et', bs :: c') =>
    ec' <- from_cannon' c' et' ;;
    ret (ggc p bs ec')
  | (nn nid et', [bs]) =>
    ret (nnc nid bs)
  | (ss e1 e2, l) =>
    ec1 <- from_cannon' (firstn (evidence_size e1) l) e1 ;;
    ec2 <- from_cannon' (skipn (evidence_size e1) l) e2 ;;
    ret (ssc ec1 ec2)
  | (pp e1 e2, l) =>
    ec1 <- from_cannon' (firstn (evidence_size e1) l) e1 ;;
    ec2 <- from_cannon' (skipn (evidence_size e1) l) e2 ;;
    ret (ppc ec1 ec2)
  | _ => None
  end.
    
Lemma to_from_cannon': forall et ec,
  length (to_cannon' ec) = evidence_size et ->
  from_cannon' (to_cannon' ec) et = Some ec.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    cbn in *.

    Compute (from_cannon' [] (ss mt mt)).
 *)   




  






(*

Inductive appEvent : Ev -> AM_St -> Ev -> Prop :=
| aeu : forall p p' i i' n n' m args tpl tpl' tid tid' st,
    m = st_aspmap st ->
    bound_to m (tpl,i) i' ->
    appEvent (umeas n p i args tpl tid) st (umeas n' p' i' ([n] ++ args) tpl' tid')
| ahu : forall n n' p p' i e e' args args' tpl tpl' tid tid' st,
    (*hsh_appEvent ev e -> *)
    EvSubT (uu i args' tpl' tid' e') e ->
    appEvent (umeas n' p' i args' tpl' tid') st (umeas n p 1 ([hashEvT e] ++ args) tpl tid).
(*| asu : forall p q i' n n' m  args st,
    m = st_sigmap st ->
    bound_to m p i' ->
    appEvent (sign n p) st (umeas n' q i' ([n] ++ args)). *)

*)

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

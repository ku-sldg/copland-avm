Require Export Term.

Require Import StructTactics.

Notation BS := nat (only parsing).

(** * Concrete Evidence *)
Inductive EvidenceC: Set :=
| mtc: EvidenceC
(*| sp: EvidenceC -> EvidenceC -> EvidenceC*)
(* | kkc: ASP_ID -> (list Arg) -> (*Plc ->*) Plc -> BS -> EvidenceC -> EvidenceC *)
| uuc: ASP_ID -> (* Plc -> *) BS -> EvidenceC -> EvidenceC
| ggc: (*Plc ->*) BS -> EvidenceC -> EvidenceC
| hhc: (*Plc ->*) BS -> EvidenceC -> EvidenceC (* TODO: remove Ev param *)
| nnc: (*Plc ->*) N_ID -> BS -> EvidenceC -> EvidenceC
| ssc: EvidenceC -> EvidenceC -> EvidenceC
| ppc: EvidenceC -> EvidenceC -> EvidenceC.



(*
Fixpoint et_fun (p:Plc) (ec:EvidenceC) : Evidence :=
  match ec with
  | mtc => mt
(*  | kkc i A q _ ec' => kk i p q A (et_fun p ec') *)
  | uuc i _ ec' => uu i p (et_fun p ec')
  | ggc q _ ec' => gg q (et_fun p ec')
  | hhc _ ec' => hh p (et_fun p ec')
  | nnc n _ ec' => nn n (et_fun p ec')
  | ssc ec1 ec2 => ss (et_fun p ec1) (et_fun p ec2)
  | ppc ec1 ec2 => pp (et_fun p ec1) (et_fun p ec2)
  end.
 *)


Inductive Ev_Shape: EvidenceC -> Evidence -> Prop :=
| mtt: Ev_Shape mtc mt
| uut: forall id p bs e et,
    Ev_Shape e et ->
    Ev_Shape (uuc id bs e) (uu id p et)
| ggt: forall p bs e et,
    Ev_Shape e et ->
    Ev_Shape (ggc bs e) (gg p et)
| hht: forall p bs e et,
    Ev_Shape e et ->
    Ev_Shape (hhc bs e) (hh p et)
| nnt: forall bs e et i,
    Ev_Shape e et ->
    Ev_Shape (nnc i bs e) (nn i et)
| sst: forall e1 e2 e1t e2t,
    Ev_Shape e1 e1t ->
    Ev_Shape e2 e2t ->
    Ev_Shape (ssc e1 e2) (ss e1t e2t)
| ppt: forall e1 e2 e1t e2t,
    Ev_Shape e1 e1t ->
    Ev_Shape e2 e2t ->
    Ev_Shape (ppc e1 e2) (pp e1t e2t).
Hint Constructors Ev_Shape.

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

(** * Eval function definition *)
Definition splitEv (sp:SP) (e:EvidenceC) : EvidenceC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.



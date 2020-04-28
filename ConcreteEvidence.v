Require Export Term.

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

(** * Place-holder axioms for IO operations *)
(* Definition invokeKIM (i:ASP_ID) (q:Plc) (*(args:list Arg)*) : BS. 
Admitted. *)
Definition invokeUSM (i:ASP_ID) (*(args:list Arg)*) : BS.
Admitted.
Definition signEv (e:EvidenceC) : BS.
Admitted.
Definition hashEv (e:EvidenceC) : BS.
Admitted.
Definition toRemote (t:Term) (pTo:Plc) (e:EvidenceC) : EvidenceC.
Admitted.
Definition parallel_eval_thread (t:Term) (e:EvidenceC) : EvidenceC.
Admitted.

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


Inductive ET: EvidenceC -> Evidence -> Prop :=
| mtt: ET mtc mt
(* | kkt: forall id A p q bs e et,
    ET p e et -> 
    ET p (kkc id A q bs e) (kk id p q A et) *)
| uut: forall id p bs e et,
    ET e et ->
    ET (uuc id bs e) (uu id p et)
| ggt: forall p bs e et,
    ET e et ->
    ET (ggc bs e) (gg p et)
| hht: forall p bs e et,
    ET e et ->
    ET (hhc bs e) (hh p et)
| nnt: forall bs e et i,
    ET e et ->
    ET (nnc i bs e) (nn i et)
| sst: forall e1 e2 e1t e2t,
    ET e1 e1t ->
    ET e2 e2t ->
    ET (ssc e1 e2) (ss e1t e2t)
| ppt: forall e1 e2 e1t e2t,
    ET e1 e1t ->
    ET e2 e2t ->
    ET (ppc e1 e2) (pp e1t e2t).
Hint Constructors ET.

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


Definition eval_asp (a:ASP) (e:EvidenceC) : EvidenceC :=
  match a with
  | CPY => e
(*  | KIM i q args =>
    let bs := invokeKIM i q args in
    (kkc i args q bs e) *)
  | ASPC i =>
    let bs := invokeUSM i in
    (uuc i bs e)
  | SIG =>
    let bs := signEv e in
    (ggc bs e)
  | HSH =>
    let bs := hashEv e in
    (hhc bs e)
  end.



Fixpoint eval (t:Term) (* (p:Plc) *) (e:EvidenceC) : EvidenceC :=
  match t with
  | asp a => eval_asp a e
  | att q t1 => toRemote t1 q e
  | lseq t1 t2 =>
    let e1 := eval t1 e in
    eval t2 e1
         
  | bseq (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := eval t1 e1 in
    let e2' := eval t2 e2 in
    (ssc e1' e2') 
  | bpar (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := parallel_eval_thread t1 e1 in
    let e2' := parallel_eval_thread t2 e2 in
    (ppc e1' e2')
  end.



Inductive EvcT: Term -> EvidenceC -> EvidenceC -> Prop :=
| mttc: forall e, EvcT (asp CPY) e e
(* | kkt: forall id A p q bs e et,
    EvcT p e et -> 
    EvcT p (kkc id A q bs e) (kk id p q A et) *)
| uutc: forall i bs e,
    EvcT (asp (ASPC i)) e (uuc i bs e)
| ggtc: forall bs e,
    EvcT (asp SIG) e (ggc bs e)
| hhtc: forall bs e,
    EvcT (asp HSH) e (hhc bs e)
| atc: forall q t' e e',
    EvcT t' e e' ->
    EvcT (att q t') e e'
| lseqc: forall t1 t2 e e' e'',
    EvcT t1 e e' ->
    EvcT t2 e' e'' ->
    EvcT (lseq t1 t2) e e''
| bseqc: forall t1 t2 sp1 sp2 e e1 e2,
    EvcT t1 (splitEv sp1 e) e1 ->
    EvcT t2 (splitEv sp2 e) e2 ->
    EvcT (bseq (sp1,sp2) t1 t2) e (ssc e1 e2)
| bparc: forall t1 t2 sp1 sp2 e e1 e2,
    EvcT t1 (splitEv sp1 e) e1 ->
    EvcT t2 (splitEv sp2 e) e2 ->
    EvcT (bpar (sp1,sp2) t1 t2) e (ppc e1 e2).
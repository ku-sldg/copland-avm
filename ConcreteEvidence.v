Require Export Term.

Notation BS := nat (only parsing).

(** * Concrete Evidence *)
Inductive EvidenceC: Set :=
| mtc: EvidenceC
(*| sp: EvidenceC -> EvidenceC -> EvidenceC*)
(* | kkc: ASP_ID -> (list Arg) -> (*Plc ->*) Plc -> BS -> EvidenceC -> EvidenceC *)
| uuc: ASP_ID -> (list Arg) -> (*Plc ->*) BS -> EvidenceC -> EvidenceC
| ggc: Plc -> EvidenceC -> BS -> EvidenceC
| hhc: (*Plc ->*) BS -> EvidenceC -> EvidenceC
| nnc: (*Plc ->*) N_ID -> BS -> EvidenceC -> EvidenceC
| ssc: EvidenceC -> EvidenceC -> EvidenceC
| ppc: EvidenceC -> EvidenceC -> EvidenceC.

(** * Place-holder axioms for IO operations *)
Definition invokeKIM (i:ASP_ID) (q:Plc) (args:list Arg) : BS.
Admitted.
Definition invokeUSM (i:ASP_ID) (args:list Arg) : BS.
Admitted.
Definition signEv (e:EvidenceC) : BS.
Admitted.
Definition hashEv (e:EvidenceC) : BS.
Admitted.
Definition toRemote (t:Term) (pTo:Plc) (e:EvidenceC) : EvidenceC.
Admitted.
Definition parallel_eval_thread (t:Term) (e:EvidenceC) : EvidenceC.
Admitted.

Fixpoint et_fun (p:Plc) (ec:EvidenceC) : Evidence :=
  match ec with
  | mtc => mt
(*  | kkc i A q _ ec' => kk i p q A (et_fun p ec') *)
  | uuc i A _ ec' => uu i p A (et_fun p ec')
  | ggc q ec' _ => gg q (et_fun p ec')
  | hhc _ ec' => hh p (et_fun p ec')
  | nnc n _ ec' => nn p n (et_fun p ec')
  | ssc ec1 ec2 => ss (et_fun p ec1) (et_fun p ec2)
  | ppc ec1 ec2 => pp (et_fun p ec1) (et_fun p ec2)
  end.
    
(** * Types *)
Inductive ET: Plc -> EvidenceC -> Evidence -> Prop :=
| mtt: forall p, ET p mtc mt
(* | kkt: forall id A p q bs e et,
    ET p e et -> 
    ET p (kkc id A q bs e) (kk id p q A et) *)
| uut: forall id A p bs e et,
    ET p e et -> 
    ET p (uuc id A bs e) (uu id p A et)
| ggt: forall n p bs e et,
    ET n e et ->
    ET n (ggc p e bs) (gg p et)
| hht: forall p bs e et,
    ET p e et ->
    ET p (hhc bs e) (hh p et)
| nnt: forall p bs e et i,
    ET p e et ->
    ET p (nnc i bs e) (nn p i et)
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

(** * Eval function definition *)
Definition splitEv (sp:SP) (e:EvidenceC) : EvidenceC :=
  match sp with
  | ALL => e
  | NONE => mtc
  end.

Definition eval_asp (a:ASP) (e:EvidenceC) (p:Plc) : EvidenceC :=
  match a with
  | CPY => e
(*  | KIM i q args =>
    let bs := invokeKIM i q args in
    (kkc i args q bs e) *)
  | ASPC i args =>
    let bs := invokeUSM i args in
    (uuc i args bs e)
  | SIG =>
    let bs := signEv e in
    (ggc p e bs)
  | HSH =>
    let bs := hashEv e in
    (hhc bs e)
  end.

Fixpoint eval (t:Term) (e:EvidenceC) (p:Plc): EvidenceC :=
  match t with
  | asp a => eval_asp a e p
  | att q t1 => toRemote t1 q e
  | lseq t1 t2 =>
    let e1 := eval t1 e p in
    eval t2 e1 p
         
  | bseq (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := eval t1 e1 p in
    let e2' := eval t2 e2 p in
    (ssc e1' e2') 
  | bpar (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := parallel_eval_thread t1 e1 in
    let e2' := parallel_eval_thread t2 e2 in
    (ppc e1' e2')
  end.
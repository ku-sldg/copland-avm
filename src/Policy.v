Require Import Term_Defs StructTactics.

Check Term.

Definition secret_evidence_rel := Evidence -> Plc -> Prop.

Definition evidence_subset_of (e:Evidence) (e':Evidence): Prop.
Admitted.

Definition policy_protects : secret_evidence_rel.
Admitted.

Inductive evidence_disclosed : Plc -> Plc -> Evidence -> Term -> secret_evidence_rel :=
| always_me_init: forall requester me init t, evidence_disclosed requester me init t init me
| always_requester_init: forall requester me init t, evidence_disclosed requester me init t init requester
(*| ed_asp_val: forall requester me init, evidence_disclosed requester me init (asp SIG) init requester *)
| ed_asp:     forall requester me init a, evidence_disclosed requester me init (asp a) (eval_asp a me init) requester
| ed_at: forall requester me init q t',
    evidence_disclosed requester me init (att q t') init q
| ed_at': forall requester me init q q' t' e,
    evidence_disclosed me q init t' e q' ->
    evidence_disclosed requester me init (att q t') e q'
| ed_ln_l: forall requester me init t1 t2 q e,
    evidence_disclosed requester me init t1 e q ->
    evidence_disclosed requester me init (lseq t1 t2) e q
| ed_ln_r: forall requester me init t1 t2 q e,
    evidence_disclosed requester me init t1 e q ->
    evidence_disclosed requester me init (lseq t1 t2) e q
| ed_bseq_l: forall requester me init t1 t2 q e sp1 sp2,
    evidence_disclosed requester me (splitEv_T sp1 init) t1 e q ->
    evidence_disclosed requester me init (bseq (sp1,sp2) t1 t2) e q
| ed_bseq_r: forall requester me init t1 t2 q e sp1 sp2,
    evidence_disclosed requester me (splitEv_T sp2 init) t1 e q ->
    evidence_disclosed requester me init (bseq (sp1,sp2) t1 t2) e q
| ed_bpar_l: forall requester me init t1 t2 q e sp1 sp2,
    evidence_disclosed requester me (splitEv_T sp1 init) t1 e q ->
    evidence_disclosed requester me init (bpar (sp1,sp2) t1 t2) e q
| ed_bpar_r: forall requester me init t1 t2 q e sp1 sp2,
    evidence_disclosed requester me (splitEv_T sp2 init) t1 e q ->
    evidence_disclosed requester me init (bpar (sp1,sp2) t1 t2) e q.


Definition disclosure_event (event:Ev) (e:Evidence) (requester:Plc) (bad_place:Plc) : Prop.
Admitted.

Require Import List.
Import List.ListNotations.
Require Import MonadVM VmSemantics Impl_vm Term_Defs ConcreteEvidence. 

Lemma cvm_respects_disclosed: forall t ev tr p bad_p requester o e init_ev et,
  st_trace
    (run_cvm (annotated t []) (mk_st init_ev [] p o)) = tr ->
  In ev tr ->                                   
  disclosure_event ev e requester bad_p ->
  Ev_Shape init_ev et ->
  evidence_disclosed requester p et t e bad_p.
Proof.
Abort.



Definition policy_check_rel := Term -> Prop.

Inductive policy1: policy_check_rel :=
| allSigs: policy1 (asp SIG).

Definition my_secrets (e:Evidence) (p:Plc) :=
  match (e,p) with
  | (mt,3)  => True
  | _ => False
  end.

Definition passes_policy
           (policy:policy_check_rel)
           (secrets:secret_evidence_rel)
           (requester:Plc)
           (me:Plc)
           (init:Evidence) : Prop :=
  forall t e q,
    policy t ->
    secrets e q ->
    not (evidence_disclosed requester me init t e q).

Lemma policy1_passes : passes_policy policy1 my_secrets 0 1 mt.
Proof.
  cbv in *;
    intros.
  invc H.
  destruct e; try solve_by_inversion.
  (*
  repeat (destruct q; try solve_by_inversion).
  invc H1. *)
Defined.

Definition derive_policy (secrets:secret_evidence_rel) : policy_check_rel.
Proof.
  cbv in *.
Admitted.

Lemma derive_passes_policy:
  forall secrets requester me init,
    passes_policy (derive_policy secrets) secrets requester me init.
Proof.
Admitted.

  


  
    
    
  









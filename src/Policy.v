Require Import Term_Defs StructTactics.

Check Term.

Require Import List.
Import List.ListNotations.
Require Import MonadVM VmSemantics Impl_vm Term_Defs ConcreteEvidence. 

Definition secret_evidence_rel := Evidence -> Plc -> Prop.

Definition evidence_subset_of (e:Evidence) (e':Evidence): Prop.
Admitted.

Definition policy_protects : secret_evidence_rel.
Admitted.

Inductive evidence_disclosed' : Plc -> Plc -> Evidence -> Term -> secret_evidence_rel :=
| cumul_req: forall t e e' init requester me,
    evidence_subset_of e e' ->
    e' = eval t me init ->
    evidence_disclosed' requester me init t e requester
| cumul_me: forall t e e' init requester me,
    evidence_subset_of e e' ->
    e' = eval t me init ->
    evidence_disclosed' requester me init t e me

(* These two NOT redundant since t could clear init *)
| always_me_init': forall requester me init t,
    evidence_disclosed' requester me init t init me
| always_requester_init': forall requester me init t,
    evidence_disclosed' requester me init t init requester
                        
| ed_at'': forall requester me init q t',
    evidence_disclosed' requester me init (att q t') init q
| ed_at''': forall requester me init q q' t' e,
    evidence_disclosed' me q init t' e q' ->
    evidence_disclosed' requester me init (att q t') e q'.

Inductive evidence_disclosed : Plc -> Plc -> Evidence -> Term -> secret_evidence_rel :=
| always_me_init: forall requester me init t, evidence_disclosed requester me init t init me
| always_requester_init: forall requester me init t, evidence_disclosed requester me init t init requester
(*| ed_asp_val: forall requester me init, evidence_disclosed requester me init (asp SIG) init requester *)
| ed_asp: forall requester me init a, evidence_disclosed requester me init (asp a) (eval_asp a me init) requester
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


Inductive disclosure_event: Ev -> Plc -> (*Plc ->*) Evidence -> Plc -> Prop :=
| req_dis: forall i loc requester (* me them *) p q q' ev t e b,
    events (annotated t []) q ev ->
    disclosure_event ev q' e b ->
    disclosure_event (req i loc p q t) requester e b
| asp_dis: forall i p id args requester init,
    disclosure_event (umeas i p id args) requester (eval_asp (ASPC id args) p init) requester.


Inductive events: AnnoTerm -> Plc -> Evidence -> Ev -> Prop :=.

Require Import Trace Main Term.

Require Import ConcreteEvidence.

Fixpoint evshape (e:EvidenceC) :=
  match e with
  | mtc => mt
  | uuc i _ e' => uu i [] 0 (evshape e')
  | ggc p e' => gg p (evshape e')
  | hhc p e' => hh p (evshape e')
  | nnc i _ e' => nn i (evshape e')
  | ssc e1 e2 => ss (evshape e1) (evshape e2)
  | ppc e1 e2 => ss (evshape e1) (evshape e2)
  end.


Lemma evshape_eval: forall init,
    Ev_Shape init (evshape init).
Proof.
Admitted.

Inductive trace: AnnoTerm -> Plc -> Evidence ->
                 list Ev -> Prop :=.

Lemma cvm_respects_disclosed': forall t ev tr p bad_p requester e  et,
  well_formed t ->
  (* copland_compile t (mk_st init_ev [] p o) = (Some tt, (mk_st e' tr p' o')) -> *)
  (*st_trace (run_cvm t
                    (mk_st e [] p o)) = tr -> *)
  (*st_trace
    (run_cvm t (mk_st init_ev [] p o)) = tr -> *)

   trace t p et tr ->
   In ev tr ->                            
  disclosure_event ev requester e bad_p ->
  (*Ev_Shape init_ev et -> *)
  evidence_disclosed requester p et (unanno t) e bad_p.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a.
    (*
      solve_by_inversion.
  -
    invc H1.
    invc H3.
    invc H4.
    invc H5.
    invc H3.
    solve_by_inversion.
  -
    solve_by_inversion.
  -
    solve_by_inversion.
  -
    solve_by_inversion.
Defined.
     *)
Admitted.

(*
    invc H0
      try (
    
      invc H0;
      cbn;
      invc H1; solve_by_inversion).
    +
      (*
      assert (Ev_Shape init_ev (evshape init_ev)).
      {
        eapply evshape_eval; eauto.
      }
      
      assert (et = evshape init_ev). admit.
      subst.
       *)

      (*
      
      
      invc H4.
      invc H1; try solve_by_inversion.
      cbn.
      invc H2.
      assert (et = init). admit.
      subst.
      econstructor.
  -
*)
Admitted.
*)

Lemma cvm_respects_disclosed: forall t ev tr p bad_p requester o e init_ev et e' p' o',
  well_formed t ->
  copland_compile t (mk_st init_ev [] p o) = (Some tt, (mk_st e' tr p' o')) ->
  (*st_trace (run_cvm t
                    (mk_st e [] p o)) = tr -> *)
  (*st_trace
    (run_cvm t (mk_st init_ev [] p o)) = tr -> *)
  In ev tr ->                                   
  disclosure_event ev requester e bad_p ->
  Ev_Shape init_ev et ->
  evidence_disclosed requester p et (unanno t) e bad_p.
Proof.
  intros.
    assert (trace t p et tr).
    {
      (*
    eapply lstar_trace.
    eapply wf_implies_wfr; eauto.

    eapply cvm_refines_lts_event_ordering; eauto.
       *)
      admit.
    }
    eapply cvm_respects_disclosed'; eauto.
Admitted.




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

Check annotated.

Definition cvm_passes_policy
           (policy:policy_check_rel)
           (secrets:secret_evidence_rel)
           (requester:Plc)
           (me:Plc)
           (init:EvidenceC) : Prop :=
  forall t e q ev et o o' p' tr e',
    policy (unanno t) ->
    secrets e q ->
    Ev_Shape init et ->
    well_formed t ->
    (* events t me et ev -> *)
    copland_compile t (mk_st init [] me o) = (Some tt, (mk_st e' tr p' o')) ->
    In ev tr ->
    not (disclosure_event ev requester e q).

Lemma passes_implies_cvm_passes: forall p s r m i i',
  Ev_Shape i i' ->
  passes_policy p s r m i' ->
  cvm_passes_policy p s r m i.
  Proof.
    intros.
    unfold cvm_passes_policy in *.
    unfold passes_policy in *.

    intros.
    unfold not in *.
    intros.
    eapply H0.
    eassumption.
    eassumption.

    eapply cvm_respects_disclosed with (init_ev:=i).
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
  Defined.

    
    

  
(*
    not (evidence_disclosed requester me init t e q). *)

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



Lemma derive_passes_cvm_policy:
  forall secrets requester me init,
    cvm_passes_policy (derive_policy secrets) secrets requester me init.
Proof.
  intros.
  eapply passes_implies_cvm_passes.
  eapply evshape_eval.
  eapply derive_passes_policy.
Defined.


  


  
    
    
  









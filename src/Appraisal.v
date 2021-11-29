Require Import Event_system Term_system ConcreteEvidence StVM.
Require Import Impl_VM Helpers_VmSemantics VmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp.

Require Import Appraisal_Defs Impl_appraisal.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad Appraisal_Evidence Helpers_Appraisal.

Require Import Lia Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
 *)

Lemma ggc_app: forall p0 sigbs H4 e',
    EvSub (ggc p0 sigbs H4) e' ->
    exists e'',
      EvSub
        (ggc p0 (checkSigF H4 p0 sigbs) e'')
        (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff.
  -
    evSubFacts.
    edestruct IHe'; eauto.
  -
    ff.
    invc H.
    +
      exists ((build_app_comp_evC e')).
      econstructor.
    +
      edestruct IHe'; eauto.
    
  -
    evSubFacts.
    +
      edestruct IHe'1; eauto.
    +
      edestruct IHe'2; eauto.
  -
    evSubFacts.
    +
      edestruct IHe'1; eauto.
    +
      edestruct IHe'2; eauto.
Defined.

Lemma appraisal_correct_sig : forall t annt e e' p ev,
    annoP annt t ->
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    cvm_evidence_denote annt p e = e' ->

    sigEvent annt p (et_fun e) ev ->
    appEvent_Sig_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.
  sigEventFacts.
  sigEventPFacts.

  edestruct gg_preserved'.
  2: { eassumption. }
  2: { eassumption. }
  eassumption.
  eassumption.
  reflexivity.

  destruct_conjs.

  edestruct ggc_app.
  eassumption.

  econstructor.
  dd.
  eassumption.
Defined.

Lemma appraisal_correct : forall t annt e' p ev e,
    annoP annt t ->
    not_none_none t ->
    cvm_evidence_denote annt p e = e' ->
    measEvent annt p (et_fun e) ev ->
    appEvent_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.
  measEventFacts.
  evEventFacts.
  edestruct uu_preserved'.
  eassumption.
  eassumption.
  eassumption.
  reflexivity.

  destruct_conjs.
    (*
    assert (e0 = et_fun H2).
    {
      Search (_ = et_fun _).
      eapply etfun_reconstruct; eauto.
    }
    subst.
     *)


  Check uuc_app.
  (*
uuc_app
     : forall (e' e'' : EvidenceC) (params : ASP_PARAMS) (p : Plc) (n : BS),
       EvSub (uuc params p n e'') e' ->
       EvSub (uuc params p (checkASPF params n) (build_app_comp_evC e''))
         (build_app_comp_evC e')
   *)

  apply uuc_app in H5.

  assert (e0 = et_fun H2).
  {
    eapply etfun_reconstruct; eauto.
  }
  subst.
  assert (H1 = encodeEv H2).
  {
    
    eapply recon_encodeEv.
    Search (_ -> wf_ec _).
    eapply wf_recon.
    eassumption.
    eassumption.
  }
  rewrite H6 in *.

  eapply aeuc.
  eassumption.
  destruct_conjs.

   eapply ahuc.
    eassumption.
    eapply hhc_app.
    eassumption.
Defined.


Require Import Impl_appraisal_alt Appraisal_AltImpls_Eq.

Lemma appraisal_correct_sig_alt :
  forall t annt pt e e' tr tr' p p' bits' et' ev ee i i',
    anno_parP pt t ->
    annoP_indexed annt t i i' -> 
    well_formed_r_annt annt ->
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    wf_ec ee ->
    reconstruct_evP ee e ->
    copland_compile pt
                    {| st_ev := ee; st_trace := tr; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := (evc bits' et');
                 st_trace := tr';
                 st_pl := p';
                 st_evid := i'|}) ->

    sigEvent annt p (get_et ee) ev ->
    Some e' = Impl_appraisal_alt.build_app_comp_evC et' bits' ->
    appEvent_Sig_EvidenceC ev e'.
Proof.
  intros.
  wrap_ccp.
  do_wfec_preserved.
  do_somerecons.
  destruct ee.
  assert (et_fun e = e0).
  {
    symmetry.
    eapply etfun_reconstruct.
    eauto.
  }
  subst.
  
  erewrite appraisal_alt.
  eapply appraisal_correct_sig.
  econstructor. repeat eexists. invc H0. eassumption.
  eassumption.
  eassumption.

 
  eapply cvm_raw_evidence_denote_fact; eauto.
  eassumption.
  eassumption.
  eassumption.
  reflexivity.
Defined.

Lemma appraisal_correct_sig_alt_et :
  forall t annt pt bits et et' et'' e e' tr tr' p p' bits' ev i i',
    anno_parP pt t ->
    annoP_indexed annt t i i' ->
    well_formed_r_annt annt ->
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    wf_ec (evc bits et) ->
    et' = aeval annt p et ->
    reconstruct_evP (evc bits et) e ->
    copland_compile pt
                    {| st_ev := (evc bits et); st_trace := tr; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := (evc bits' et'');
                 st_trace := tr';
                 st_pl := p';
                 st_evid := i'|}) ->

    sigEvent annt p et ev ->
    Some e' = Impl_appraisal_alt.build_app_comp_evC et' bits' ->
    appEvent_Sig_EvidenceC ev e'.
Proof.
  intros.
  wrap_ccp.
  assert (et'' =  (aeval annt p et)).
  {
    rewrite <- eval_aeval'.
    
    assert (t = unanno annt).
    {
      invc H0.
      erewrite <- anno_unanno at 1.
      rewrite H5.
      tauto.
    }
    subst.
    
    eapply cvm_refines_lts_evidence.
    eassumption.
    eassumption.
  }

  subst.
  invc H7.
  eapply appraisal_correct_sig_alt; eauto.
Defined.


Lemma appraisal_correct_alt :
  forall t annt pt e' tr tr' p p' bits' et' ev ee i i',
    anno_parP pt t ->
    annoP_indexed annt t i i' ->
    well_formed_r_annt annt ->
    not_none_none t ->
    wf_ec ee ->
    copland_compile pt
                    {| st_ev := ee; st_trace := tr; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := (evc bits' et');
                 st_trace := tr';
                 st_pl := p'; st_evid := i' |}) ->

    measEvent annt p (get_et ee) ev ->
    Some e' = Impl_appraisal_alt.build_app_comp_evC et' bits' ->
    appEvent_EvidenceC ev e'.
Proof.
  intros.
  wrap_ccp.
  do_wfec_preserved.
  do_somerecons.
  destruct ee.
  assert (e = et_fun H9).
  {
    eapply etfun_reconstruct.
    eauto.
  }
  subst.
    
  erewrite appraisal_alt.
  eapply appraisal_correct.
  econstructor. repeat eexists. invc H0. eassumption.
  eassumption.
  eapply cvm_raw_evidence_denote_fact; eauto.

  eassumption.
  eassumption.
  eassumption.
  reflexivity.
Defined.

Lemma appraisal_correct_alt_et :
  forall t annt pt e' tr tr' p p' bits bits' et et' et'' ev i i',
    anno_parP pt t ->
    annoP_indexed annt t i i' ->
    well_formed_r_annt annt ->
    not_none_none t ->
    wf_ec (evc bits et) ->
    et' = aeval annt p et ->
    copland_compile pt
                    {| st_ev := (evc bits et); st_trace := tr; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := (evc bits' et'');
                 st_trace := tr';
                 st_pl := p';
                 st_evid := i'|}) ->

    measEvent annt p et ev ->
    Some e' = Impl_appraisal_alt.build_app_comp_evC et' bits' ->
    appEvent_EvidenceC ev e'.
Proof.
  intros.
  wrap_ccp.
  assert (et'' = (aeval annt p et)).
  {
    assert (t = unanno annt).
    {
      invc H0.
      erewrite <- anno_unanno at 1.
      rewrite H4.
      tauto.
    }
    subst.

    erewrite <- eval_aeval'.
    eapply cvm_refines_lts_evidence.
    eassumption.
    eassumption.
  }
  
  subst.

  eapply appraisal_correct_alt.
  6: {
    wrap_ccp.
    eassumption.
  }
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
Defined.

Require Import Maps Event_system Term_system MonadVM ConcreteEvidence.
Require Import Impl_vm Helpers_VmSemantics VmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp.

Require Import StAM Appraisal_Defs Impl_appraisal (*MonadAM*).

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad Helpers_Appraisal.

Require Import Lia Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

Lemma ggc_app: forall p0 x e H4 e',
    EvSub (ggc p0 (do_sig (MonadVM.encodeEv (evc x e)) p0) H4) e' ->
    exists e'' sigbs,
      EvSub
        (ggc p0 (checkSig H4 p0 sigbs) e'')
        (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff.
  -
    evSubFacts.
    edestruct IHe'; eauto.
    destruct_conjs.
    subst.
    repeat eexists.
    eauto.
  -
    ff.
    invc H.
    +
      exists ((build_app_comp_evC e')).
      exists ((do_sig (MonadVM.encodeEv (evc x e)) n)).
      econstructor.
    +
      edestruct IHe'; eauto.
      destruct_conjs.
      subst.
      repeat eexists.
      eauto.
  -
    ff.
    invc H.
    ff.
    repeat eexists.
    econstructor.
    ff.
    eassumption.
    
  -
    evSubFacts.
    +
      edestruct IHe'1; eauto.
      destruct_conjs.
      subst.
      repeat eexists.
      eauto.
    +
      edestruct IHe'2; eauto.
      destruct_conjs.
      subst.
      repeat eexists.
      eauto.
  -
    evSubFacts.
    +
      edestruct IHe'1; eauto.
      destruct_conjs.
      subst.
      repeat eexists.
      eauto.
    +
      edestruct IHe'2; eauto.
      destruct_conjs.
      subst.
      repeat eexists.
      eauto.
      Unshelve.
      eauto.
Defined.

Lemma appraisal_correct_sig : forall t e e' tr tr' p p' ecc ev ee,
    well_formed_r t ->
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    wf_ec ee ->
    Some e = (reconstruct_ev ee) ->
    Some e' = (reconstruct_ev ecc) ->
    copland_compile t
                    {| st_ev := ee; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc;
                 st_trace := tr';
                 st_pl := p' |}) ->

    sigEvent t p (get_et ee) ev ->
    appEvent_Sig_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    sigEventFacts.
    sigEventPFacts.
    destruct ee.
    inv_events.
    ff.
    break_match; try solve_by_inversion.
    invc H4.
    ff.
    assert (e0 = et_fun e2).
    {
      rewrite fold_recev in *.
      eapply etfun_reconstruct; eauto.
    }
    subst.
    
    repeat econstructor.
  -
    sigEventFacts.
    sigEventPFacts.
    invEvents.
    vmsts.
    ff.
    do_wf_pieces.
    do_not_none.
    invc H1.
    do_not_hshsig.
    eapply IHt.
    eassumption.
    eassumption.
    econstructor.
    eassumption.
    split; try eassumption.
    intros.
    unfold not in *; intros.
    apply H9.
    eassumption.
    invc H11.
    econstructor.
    econstructor.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    eapply copland_compile_at.
    eassumption.
    econstructor.
    eassumption.
    econstructor.
  - (* alseq case *)
    
    do_wf_pieces.
    do_not_none.
    do_not_hshsig.
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.

    sigEventFacts.
    repeat do_pl_immut.
    subst.
    sigEventPFacts.
    do_wfec_preserved.
    do_somerecons.
    inv_events.
    + (* t1 case *)

      destruct ee.
      
      edestruct gg_preserved' with (t:= alseq r t1 t2).
      eassumption.
      eassumption.
      eassumption.
      4: { eassumption. }
      ff. eassumption.
      eassumption.
      2: {
        vmsts.
        rewrite <- Heqp1.
        repeat ff; try solve_by_inversion.
        vmsts.
        repeat ff.
        destruct o; try solve_by_inversion.
        repeat ff.
        do_pl_immut.
        do_pl_immut.
        do_pl_immut.
        subst.
        rewrite Heqp0 in Heqp2.
        ff.
        
        vmsts.
        subst.
        do_pl_immut.
        do_pl_immut.
        do_pl_immut.
        subst.
        rewrite Heqp0 in Heqp2.
        solve_by_inversion.
      }
      eassumption.
      jkjke'.
      jkjke'.
      ff.
      
      destruct_conjs.

      edestruct ggc_app.
      eassumption.
      
      destruct_conjs.

      subst.
      econstructor.
      repeat jkjke'.
      repeat ff.
      
    + (* t2 case *)

      do_wfec_preserved.
      destruct ecc.
      destruct st_ev.
      
      eapply IHt2.
      eassumption.
      eassumption.
      4: { eassumption. }
      4: { eassumption. }
      2: { eassumption. }
      2: { eassumption. }
      jkjke'.
      jkjke'.
      ff.
      destruct ee.
      rewrite fold_recev in *.
      eapply sig_term_ev_lseqr.
      apply H7.
      3: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      eassumption.

      destruct ee.
      ff.
      assert (e4 = aeval t1 p e6).
      {
        rewrite <- eval_aeval.
        eapply cvm_refines_lts_evidence.
        eassumption.
        eassumption.
      }
      subst.
      econstructor.
      eassumption.
      econstructor.
      
  - (* abseq case *)
    do_wf_pieces.
    do_not_none.
    (*
    invc H1. *)
    do_not_hshsig.
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    
    repeat ff.

    sigEventFacts.
    sigEventPFacts.
    repeat do_pl_immut.
    subst.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.
    

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)

      assert (appEvent_Sig_EvidenceC (sign n1 p0 e6) (build_app_comp_evC e4)).
      {
        destruct ee; ff.

        rewrite fold_recev in *.

        assert (exists ee, Some ee = reconstruct_ev (splitEv_l s (evc e7 e8))).
        {
          destruct s.
          destruct s; destruct s0; ff.
          eauto.
          eauto.
          eauto.
          eauto.
        }
        destruct_conjs.
        
        assert (not_hash_sig_ev H13).
        {
          invc H1.
          
          destruct s; destruct s; destruct s0; ff.
          rewrite fold_recev in *.
          repeat jkjke'. ff.
          repeat jkjke'. ff.
          repeat jkjke'. ff.
          repeat jkjke'; ff.
          
          cbv. intros. invc H13. destruct_conjs. solve_by_inversion.
          cbv. intros. invc H13. destruct_conjs. solve_by_inversion.
        }
        
        eapply IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        eassumption.
        eassumption.
        
        4: { eassumption. }
        eassumption.

        destruct s. destruct s; destruct s0; ff.
        jkjke'. 

        ff.
        econstructor.
        destruct s; destruct s; ff.
        econstructor.
      }
      invc H13.
      econstructor.
      ff.
    + (* t2 case *)


      assert (appEvent_Sig_EvidenceC (sign n1 p0 e6) (build_app_comp_evC e5)).
      {
        destruct ee; ff.

        rewrite fold_recev in *.

        assert (exists ee, Some ee = reconstruct_ev (splitEv_r s (evc e7 e8))).
        {
          destruct s.
          destruct s; destruct s0; ff.
          eauto.
          eauto.
          eauto.
          eauto.
        }
        destruct_conjs.
        
        assert (not_hash_sig_ev H13).
        {
          invc H1.
          
          destruct s; destruct s; destruct s0; ff.
          rewrite fold_recev in *.
          destruct_conjs.
          repeat jkjke'. ff.
          cbv. intros. invc H13. destruct_conjs. solve_by_inversion.
          repeat jkjke'. ff.
          repeat jkjke'. ff.
          cbv. intros. invc H13. destruct_conjs. solve_by_inversion.
        }
        
        eapply IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        eassumption.
        eassumption.
        
        4: { eassumption. }
        eassumption.
        destruct s. destruct s; destruct s0; ff.
        symmetry. eassumption.

        econstructor.
        destruct s; destruct s; destruct s0; ff.
        econstructor.
      }
      invc H13.
      econstructor.
      ff.

  - (* abpar case *)
    
    do_wf_pieces.
    do_not_none.
    (*
    invc H1. *)
    do_not_hshsig.
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    
    repeat ff.

    sigEventFacts.
    sigEventPFacts.
    repeat do_pl_immut.
    subst.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.
    

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)


      assert (appEvent_Sig_EvidenceC (sign n1 p0 e6) (build_app_comp_evC e4)).
      {
        destruct ee; ff.

        rewrite fold_recev in *.

        assert (exists ee, Some ee = reconstruct_ev (splitEv_l s (evc e7 e8))).
        {
          destruct s.
          destruct s; destruct s0; ff.
          eauto.
          eauto.
          eauto.
          eauto.
        }
        destruct_conjs.
        
        assert (not_hash_sig_ev H13).
        {
          invc H1.
          
          destruct s; destruct s; destruct s0; ff.
          rewrite fold_recev in *.
          repeat jkjke'. ff.
          repeat jkjke'. ff.
          repeat jkjke'. ff.
          repeat jkjke'; ff.
          
          
          cbv. intros. invc H13. destruct_conjs. solve_by_inversion.
          cbv. intros. invc H13. destruct_conjs. solve_by_inversion.
        }
        
        
        eapply IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        eassumption.
        eassumption.
        
        4: { eassumption. }
        eassumption.
        
        destruct s. destruct s; destruct s0; ff.
        jkjke'. 

        ff.
        econstructor.
        destruct s; destruct s; ff.
        econstructor.
      }
      invc H13.
      econstructor.
      ff.
    + (* t2 case *)


      assert (appEvent_Sig_EvidenceC (sign n1 p0 e6) (build_app_comp_evC e5)).
      {
        destruct ee; ff.

        rewrite fold_recev in *.

        assert (exists ee, Some ee = reconstruct_ev (splitEv_r s (evc e7 e8))).
        {
          destruct s.
          destruct s; destruct s0; ff.
          eauto.
          eauto.
          eauto.
          eauto.
        }
        destruct_conjs.
        
        assert (not_hash_sig_ev H13).
        {
          invc H1.
          
          destruct s; destruct s; destruct s0; ff.
          rewrite fold_recev in *.
          destruct_conjs.
          repeat jkjke'. ff.
          cbv. intros. invc H13. destruct_conjs. solve_by_inversion.
          repeat jkjke'. ff.
          repeat jkjke'. ff.
          cbv. intros. invc H13. destruct_conjs. solve_by_inversion.
        }
        
        
        eapply IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        eassumption.
        eassumption.
        
        4: { eassumption. }
        eassumption.
        destruct s. destruct s; destruct s0; ff.
        symmetry. eassumption.

        econstructor.
        destruct s; destruct s; destruct s0; ff.
        econstructor.
      }
      invc H13.
      econstructor.
      ff.
Defined.

Lemma appraisal_correct : forall t e' tr tr' p p' ecc ev ee,
    well_formed_r t ->
    not_none_none t ->
    wf_ec ee ->
    Some e' = (reconstruct_ev ecc) ->
    copland_compile t
                    {| st_ev := ee; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc;
                 st_trace := tr';
                 st_pl := p' |}) ->

    measEvent t p (get_et ee) ev ->
    appEvent_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    measEventFacts.
    evEventFacts.
    destruct ee.
    inv_events.
    ff.
    break_match; try solve_by_inversion.
    invc H2.
    
    repeat econstructor.

  - (* aatt case *)
    measEventFacts.
    evEventFacts.
    invEvents.
    vmsts.
    ff.
    do_wf_pieces.
    do_not_none.
    eapply IHt.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    eapply copland_compile_at.
    eassumption.
    econstructor.
    eassumption.
    econstructor.
  - (* alseq case *)
    
    do_wf_pieces.
    do_not_none.
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.

    measEventFacts.
    repeat do_pl_immut.
    subst.
    invc H9.
    inv_events.
    + (* t1 case *)

      edestruct uu_preserved.
      apply H5.
      apply H6.
      eassumption.
      eassumption.
      4: { eassumption. }
      4: { eassumption. }
      eassumption.
      eassumption.
      eassumption.

      destruct_conjs.

      assert (
          exists e'', EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e'')
                       (build_app_comp_evC e')).
      {
        
        eapply uuc_app; eauto.
      }
      destruct_conjs.
      econstructor.
      eassumption.
      destruct_conjs.
      eapply ahuc.
      eassumption.
      eapply hhc_app; eauto.
      
    + (* t2 case *)

      do_wfec_preserved.
      destruct ecc.
      destruct st_ev.
      
      eapply IHt2.
      eassumption.
      eassumption.
      3: { eassumption. }
      eassumption.
      eassumption.
      econstructor.
      destruct ee.
      ff.
      assert (e2 = aeval t1 p e4).
      {
        rewrite <- eval_aeval.
        eapply cvm_refines_lts_evidence.
        eassumption.
        eassumption.
      }
      subst.
      eassumption.
      econstructor.
      
  - (* abseq case *)
    
    do_wf_pieces.
    do_not_none.
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    
    repeat ff.

    measEventFacts.
    repeat do_pl_immut.
    subst.
    invc H3.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)

      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        destruct ee; ff.

        rewrite fold_recev in *.
        
        eapply IHt1.
        eassumption.
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. ff.
        destruct s; destruct s; ff.
        econstructor.
      }
      
      invc H11.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.

    + (* t1 case *)

      assert (appEvent_EvidenceC
                (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {      
        destruct ee; ff.

        rewrite fold_recev in *.
        
        eapply IHt2.
        eassumption.
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. ff.
        destruct s; destruct s0; ff.
        econstructor.
      }

      invc H11.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.

  - (* abpar case *)
    do_wf_pieces.
    do_not_none.
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H3.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)

      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        destruct ee; ff.

        rewrite fold_recev in *.
        
        eapply IHt1.
        eassumption.
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. ff.
        destruct s; destruct s; ff.
        econstructor.
      }

      invc H11.
      +++
        econstructor.
        econstructor.   
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.

    + (* t1 case *)

      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        destruct ee; ff.

        rewrite fold_recev in *.
        
        eapply IHt2.
        eassumption.
        eassumption.
        2: { jkjke'. }
        2: { eassumption. }
        eassumption.
        econstructor. ff.
        destruct s; destruct s0; ff.
        econstructor.
      }

      invc H11.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
Defined.

Require Import Impl_appraisal_alt Appraisal_AltImpls_Eq.


Lemma appraisal_correct_alt : forall t e' tr tr' p p' bits' et' ev ee,
    well_formed_r t ->
    not_none_none t ->
    wf_ec ee ->
    copland_compile t
                    {| st_ev := ee; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := (evc bits' et');
                 st_trace := tr';
                 st_pl := p' |}) ->

    measEvent t p (get_et ee) ev ->
    Some e' = Impl_appraisal_alt.build_app_comp_evC et' bits' ->
    appEvent_EvidenceC ev e'.
Proof.
  intros.
  ff.
  do_wfec_preserved.
  do_somerecons.
  erewrite appraisal_alt.
  eapply appraisal_correct.
  eassumption.
  eassumption.
  3: { eassumption. }
  eassumption.
  2: { eassumption. }
  2: { eassumption. }
  3: { tauto. }
  eassumption.
  eassumption.
Defined.

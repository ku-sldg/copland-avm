Require Import Maps Event_system Term_system MonadVM ConcreteEvidence.
Require Import Impl_vm Helpers_VmSemantics VmSemantics.
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

Lemma appraisal_correct_sig : forall t annt n e e' p ev,
    annoP annt t n ->
    (*well_formed_r pt -> *)
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    (*wf_ec ee ->
    reconstruct_evP ee e ->
    reconstruct_evP ecc e' ->
    copland_compileP pt
                     {| st_ev := ee; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc;
                        st_trace := tr';
                        st_pl := p' |} ->
     *)
    cvm_evidence_denote annt p e = e' ->

    sigEvent annt p (et_fun e) ev ->
    appEvent_Sig_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.


  sigEventFacts.
  sigEventPFacts.



  edestruct gg_preserved'.
      Check ggc_app.
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
      

(*
        econstructor.
           eassumption.
           split.
           eassumption.
           eassumption.
      }
      2: { apply H9. }
      2: { dd. reflexivity. }
      econstructor.
      dd.
      rewrite Heqp1 in *.
      dd.
      rewrite Heqp0 in *.
      dd.
      tauto.





  
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    dd.
    invc H.
    dd.
    
    sigEventFacts.
    sigEventPFacts.
    (*
    destruct ee.
     *)
    
    inv_events.
    ff.
    (*
    do_rewrap_reconP. *)
    unfold checkSigF.
    unfold checkSig.
    fold checkSigBitsF.

    assert (


        checkSigBitsF (encodeEv e)
                      p0
                      (do_sig (encodeEvRaw (encodeEv e)) p0 n) =
        
        (fromSome default_bs
          (checkSigBits (encodeEv e) p0
                        (do_sig (encodeEvRaw (encodeEv e)) p0 n)))
      ) as H5.
    { tauto. }
           

    (*
    assert (
        checkSigBitsF (encodeEv e)
                      p0
                      (do_sig (encodeEvBits (evc r e0)) p0 n) =
        (fromSome default_bs
          (checkSigBits (encodeEv e) p0
             (do_sig (encodeEvBits (evc r e0)) p0 n)))


      ) as H5.
    { tauto. }
     *)
    rewrite <- H5.
    (*
    assert (r = encodeEv e1).
    {
      eapply recon_encodeEv.
      eassumption.
      eassumption.
    }
    rewrite <- H7.
    assert (r = get_bits (evc r e0)).
    { tauto. }
    assert (e0 = get_et (evc r e0)).
    {
      tauto.
    }
    
    rewrite H8.
    rewrite H9.
     *)
    assert (
        (encodeEvRaw (encodeEv e)) =
        (encodeEvBits (evc (encodeEv e) (et_fun e)))
      ).
    {
      admit.
    }
    rewrite H2.
    
           
    repeat econstructor.
    

  - (* aatt case *)
    (*
    wrap_ccp.
     *)
    dd.
    invc H.
    dd.
    do_anno_redo.
    
    sigEventFacts.
    sigEventPFacts.
    invEvents.

    do_not_none.
    inversion H1.
    do_not_hshsig.

    

    do_assume_remote t (evc (encodeEv e) (et_fun e)) n (S n0) HHH.
    
    eapply IHt.
    eassumption.
    (*
    econstructor.
    reflexivity.
    eapply wfr_annt_implies_wfr_par.
     *)
    
    eassumption.

    (*
    econstructor.
    tauto. 
    eassumption. *)
    econstructor.
    eassumption.
    split; try eassumption.
    intros.
    unfold not in *; intros.
    apply H5.
    eassumption.
    econstructor. eauto.
    reflexivity.
    econstructor; eauto.
    econstructor.
    
  - (* alseq case *)

    (*
    (*
    wrap_ccp.
     *)  
    inversion H2.
    (*
    do_wf_pieces.
     *)
     *)

    (*
    assert (exists annot1, annoP annot1 t1 n).
    {
      admit.
    }
    assert (exists annot2 n', annoP annot2 t2 n').
    {
      admit.
    }
    destruct_conjs.
    dd.
    invc H.
    dd.
     *)
    
    
    

    (*
    dd.
    invc H.
    dd.

    repeat do_anno_redo.
     *)
    
    
    invc H1.
    
    do_not_none.
    do_not_hshsig.
    
    sigEventFacts.

    sigEventPFacts.
    invc H.
    dd.
    (*
    do_wfec_preserved.
    do_somerecons.
    do_reconP_determ.
     *)
    
    inv_events.
    + (* t1 case *)

      (*

      destruct ee. *)

      Check gg_preserved'.

      edestruct gg_preserved' with (t:= lseq t1 t2).
      Check ggc_app.
      2: { eassumption. }
      2: { econstructor.
           eassumption.
           split.
           eassumption.
           eassumption.
      }
      2: { apply H9. }
      2: { dd. reflexivity. }
      econstructor.
      dd.
      rewrite Heqp1 in *.
      dd.
      rewrite Heqp0 in *.
      dd.
      tauto.



      (*
     
      
      edestruct gg_preserved' with (t:= lseq t1 t2) (e:= cvm_evidence_denote a p e) (e':= cvm_evidence_denote a0 p (cvm_evidence_denote a p e)).
      admit.
      eassumption.
      econstructor.
      eassumption.
      split; try eassumption.
      eapply hshsig_ev_term_contra.
      2 : { econstructor.
            apply H7.
            split. apply H5.
            intros.
            unfold not in *; intros.
            eapply H6.
            eassumption.
            eauto.
      }
      econstructor.
      jkjke.
      simpl.
      reflexivity.
      
      
            split; try eassumption.
      
      Print do_ste.
      Print do_hste_contra.
      eapply sig_term_ev_lseqr.
      2: { econstructor.
           eassumption.
           split; eassumption.
      }
      econstructor.
      jkjke.
      reflexivity.
      intros.
      unfold not; intros.
      
      
      eassumption.
      reflexivity.
       *)
      


(*
      
      eassumption.
      econstructor.
      reflexivity.
      eassumption.
      econstructor.
      eassumption.
      split; eassumption.
      eassumption.
      inversion Heqp0.
      inversion Heqp1.
      dd.
      reflexivity.
      
      jkjke.
      eassumption.
      eassumption.
      eassumption.
      5: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      2: {
        eassumption.
      }
      eassumption.
 *)
      
      
      
      destruct_conjs.
      (*
      assert (encodeEv H18 = x).
      {
        symmetry.
        eassumption.
      }
       *)

      Check ggc_app.
      
      

      edestruct ggc_app.

      eassumption.

      unfold checkSigF in *.
      unfold checkSig in *.
      (*
      rewrite H11 in *; clear H11. *)
      econstructor.
      subst.


      
      (*
      exact (evc x (et_fun H18)).
      assert (
          checkSigBitsF (encodeEv H18)
                        p0
                        (do_sig (encodeEvBits (evc x (et_fun H18))) p0 n) =

          
          (fromSome default_bs
                (checkSigBits (encodeEv H18) p0
                              (do_sig (encodeEvBits (evc x (et_fun H18))) p0 n)))).
      {
        tauto. }
      rewrite <- H20 in *. *)
      eassumption.

      
    + (* t2 case *)
      (*
      wrap_ccp.
       *)


      (*

      do_wfec_preserved.
      
      assert (wf_ec ecc).
      {
        eapply wf_ec_preserved_by_cvm.
        eassumption.
        eassumption.
        eassumption.
      }
      do_somerecons.
      do_reconP_determ.

        destruct ee;
        destruct st_ev0.
       *)
      

      repeat do_anno_redo.
      
      eapply IHt2.
      eassumption.
      eassumption.
      eapply sig_term_ev_lseqr.
      apply Heqp1.
      econstructor.
      eassumption.
      split.
      eassumption.
      eassumption.
      reflexivity.
      reflexivity.
      econstructor.
      assert ((et_fun (cvm_evidence_denote a p e)) =
              (aeval a p (et_fun e))).
      {
        eapply cvm_ev_deonte_evtype.
        eassumption.
      }
      rewrite H.
      eassumption.
      econstructor.

      
  - (* abseq case *)

        (*
    wrap_ccp.
     *)
    
    inversion H2.
    (*
    do_wf_pieces.
     *)
    
    do_not_none.
    do_not_hshsig.

    sigEventFacts.
    sigEventPFacts.
    do_wfec_preserved.
    do_somerecons.
    do_reconP_determ.

    wrap_ccp.

    do_rewrap_reconP.
    

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.
    
    inv_events.
    + (* t1 case *)

      assert (appEvent_Sig_EvidenceC (sign n p0 e0) (build_app_comp_evC e2)).
      {
        destruct ee; ff.
              
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        
        4: { eassumption. }
        eassumption.

        destruct s. destruct s; destruct s0; ff.
        econstructor; tauto.
        econstructor; tauto.
        eassumption.
       

        destruct s; destruct s; destruct s0; ff.
        econstructor. eassumption. econstructor.
        econstructor. eassumption. econstructor.
        econstructor. eassumption. econstructor.
        econstructor. eassumption. econstructor.
      }
      invc H21.
      econstructor.
      eauto.

    + (* t2 case *)

      assert (appEvent_Sig_EvidenceC (sign n p0 e0) (build_app_comp_evC e3)).
      {
        destruct ee; ff.
              
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        
        4: { eassumption. }
        eassumption.

        destruct s. destruct s; destruct s0; ff.
        econstructor; tauto.
        econstructor; tauto.
        eassumption.

        destruct s; destruct s; destruct s0; ff.
        econstructor. eassumption. econstructor.
        econstructor. eassumption. econstructor.
        econstructor. eassumption. econstructor.
        econstructor. eassumption. econstructor.
      }
      invc H21.
      econstructor.
      eauto.

  - (* NEW abpar case *)

        (*
    wrap_ccp.
     *)
    
    inversion H2.
    (*
    do_wf_pieces.
     *)
    
    do_not_none.
    do_not_hshsig.

    sigEventFacts.   
    sigEventPFacts.
    do_wfec_preserved.
    do_somerecons.

    do_reconP_determ.

    wrap_ccp.

    do_rewrap_reconP.
    

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    do_reconP_determ.

    inv_events.
    + (* t1 case *)

      assert (appEvent_Sig_EvidenceC (sign n p0 e0) (build_app_comp_evC e2)).
      {
        destruct ee; dd.
              
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        
        4: { eassumption. }
        eassumption.

        destruct s. destruct s; destruct s0; ff.
        econstructor; tauto.
        econstructor; tauto.
        eassumption.
        destruct s; destruct s; destruct s0; ff.
        econstructor. eassumption. econstructor.
        econstructor. eassumption. econstructor.
        econstructor. eassumption. econstructor.
        econstructor. eassumption. econstructor.

      }
      invc H20.
      econstructor.
      eauto.
      
    + (* NEW t2 case *)
          
      assert (appEvent_Sig_EvidenceC (sign n p0 e0) (build_app_comp_evC e3)).
      {
        destruct ee; ff.
        
        do_assume_remote t2 (splitEv_r s (evc r e4)) p HHH.
        eapply IHt2.
        econstructor.
        reflexivity.
        eapply wfr_annt_implies_wfr_par.
        eassumption.
        econstructor. tauto.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        
        4: {
          rewrite H20.
          simpl.
          econstructor.
          eassumption. }
        eassumption.

        destruct s. destruct s; destruct s0; ff.
        econstructor; tauto.
        econstructor; tauto.

        rewrite at_evidence.
        rewrite par_evidence in *.
        rewrite <- H22.
        rewrite Heqe1.
        eassumption.
        econstructor.
        destruct s; destruct s; destruct s0; ff.
        econstructor.
      }
      invc H20.
      econstructor.
      ff.
Defined.
 *)

Lemma appraisal_correct : forall t annt n e' p ev e,
    annoP annt t n ->
    (*well_formed_r pt -> *)
    not_none_none t ->
    (*wf_ec ee ->
    reconstruct_evP ecc e' ->
    copland_compileP pt
                     {| st_ev := ee; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc;
                        st_trace := tr';
                        st_pl := p' |} ->
     *)
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

  -
    destruct_conjs.
    edestruct uuc_app.
    eassumption.

    
    econstructor.
    eassumption.
  -
    destruct_conjs.

    eapply ahuc.
    eassumption.
    eapply hhc_app.
    eassumption.
Defined.


(*
Lemma appraisal_correct : forall t pt loc e' tr tr' p p' ecc ev ee,
    anno_parP pt t loc ->
    well_formed_r pt ->
    not_none_none t ->
    wf_ec ee ->
    reconstruct_evP ecc e' ->
    copland_compileP pt
                     {| st_ev := ee; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc;
                        st_trace := tr';
                        st_pl := p' |} ->

    measEvent t p (get_et ee) ev ->
    appEvent_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    wrap_ccp.

    measEventFacts.
    evEventFacts.
    destruct ee.
    inv_events.
    ff.
    do_rewrap_reconP.
    
    repeat econstructor.

  - (* aatt case *)
    wrap_ccp.
    measEventFacts.
    evEventFacts.
    invEvents.
    do_not_none.
    
    do_assume_remote t ee n HHH.
    
    eapply IHt.
    econstructor.
    reflexivity.
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    econstructor.
    tauto.
    eassumption.
    eassumption.
    eassumption.
    econstructor.
    rewrite H6.
    rewrite H8.
    simpl.
    eassumption.
    econstructor.
    eassumption.
    econstructor.    
    
  - (* alseq case *)

    
    wrap_ccp.
    
    do_not_none.
    measEventFacts.
    evEventFacts.
    do_wfec_preserved.
    do_somerecons.
    inv_events.

    + (* NEW t1 case *)
      edestruct uu_preserved.
      apply Heqp0.
      apply Heqp1.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      4: { eassumption. }
      4: { eassumption. }
      eassumption.
      eassumption.
      eassumption.

      destruct_conjs.

      assert (
          exists e'', EvSub (uuc (asp_paramsC i args tpl tid) p0 (checkASPF (asp_paramsC i args tpl tid) (do_asp (asp_paramsC i args tpl tid) p0 n)) e'')
                       (build_app_comp_evC e')).
      {
        do_reconP_determ.
        
        eapply uuc_app; eauto.
      }
      destruct_conjs.
      econstructor.
      eassumption.
      destruct_conjs.
      eapply ahuc.
      eassumption.
      do_reconP_determ.
      eapply hhc_app; eauto.
      
    + (* t2 case *)
      wrap_ccp.
      do_reconP_determ.
      
      do_somerecons.
      do_reconP_determ.

        destruct ee;
        destruct st_ev0.
      
      eapply IHt2.
      eassumption.
      eassumption.
      eassumption.
      3: { eassumption. }
      eassumption.
      eassumption.
      
      econstructor.
      simpl in *.
      assert (e0 = aeval t1 p e).
      {
        rewrite <- eval_aeval.
        inversion Heqp0.
        assert (t1 = unannoPar a1).
        {
          erewrite anno_unanno_par.
          reflexivity.
          subst.
          eapply annopar_fst_snd.
        }
        find_rw_in_goal.
             
        eapply cvm_refines_lts_evidence.
        eassumption.
        eassumption.
      }
      subst.
      eassumption.
      
      econstructor.
   
  - (* abseq case *)
    
    wrap_ccp.

    do_rewrap_reconP.
    
    do_not_none.
    measEventFacts.
    evEventFacts.
    
    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.
    
    inv_events.

    + (* t1 case NEW *)

      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e1))).
      {
        destruct ee; ff.
        
        eapply IHt1.
        eassumption.
        
        eassumption.
        eassumption.
        2: { eassumption. }
        2: { eassumption. }
        eassumption.
        econstructor.
        destruct s; destruct s; ff.
        econstructor.
      }
      
      invc H12.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.

    + (* t2 case NEW *)

      assert (appEvent_EvidenceC
                (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e2))).
      {      
        destruct ee; ff.
        
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
        2: { eassumption. }
        2: { eassumption. }
        eassumption.
        econstructor.
        destruct s; destruct s0; ff.
        econstructor.
      }

      invc H12.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
  - (* NEW abpar case *)
    
        
    wrap_ccp.

    do_rewrap_reconP.
    
    do_not_none.

    measEventFacts.
    evEventFacts.
    
    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    inv_events.

    + (* t1 case *)

      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e1))).
      {
        destruct ee; ff.
        
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        2: { eassumption. }
        2: { eassumption. }
        eassumption.
        econstructor.
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

    + (* t2 case *)

      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e2))).
      {
        destruct ee; ff.

        do_assume_remote t2 (splitEv_r s (evc r e3)) p HHH.
        
        
        eapply IHt2.
        econstructor.
        reflexivity.
        eapply wfr_annt_implies_wfr_par.
        eassumption.
        econstructor.
        tauto.
        eassumption.
        3: {
          rewrite H11.
          simpl.
          econstructor.
          eassumption. }
        eassumption.

        rewrite at_evidence.
        rewrite par_evidence in *.
        rewrite <- H13.
        rewrite Heqe0.
        eassumption.
        econstructor.
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
*)

Require Import Impl_appraisal_alt Appraisal_AltImpls_Eq.

Lemma appraisal_correct_sig_alt : forall t annt pt loc e e' tr tr' p p' bits' et' ev ee i i',
    anno_parP pt t loc ->
    annoP annt t i -> 
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
  eassumption.
  eassumption.
  eassumption.
 
  eapply cvm_raw_evidence_denote_fact; eauto.
  eassumption.
  eassumption.
  eassumption.
  reflexivity.
Defined.

Lemma appraisal_correct_sig_alt_et : forall t annt pt loc bits et et' et'' e e' tr tr' p p' bits' ev i i',
    anno_parP pt t loc ->
    annoP annt t i ->
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
    invc H0.

    rewrite <- eval_aeval.
    inversion H.
    assert (t = unannoPar pt).
    {
      erewrite anno_unanno_par.
      reflexivity.
      
      rewrite H0.
      eapply annopar_fst_snd.
    }
    rewrite H12.
 
    eapply cvm_refines_lts_evidence.
    rewrite <- H12.
    eassumption.
    eassumption.
  }
  subst.
  invc H7.
  eapply appraisal_correct_sig_alt; eauto.
Defined.


Lemma appraisal_correct_alt : forall t annt pt loc e' tr tr' p p' bits' et' ev ee i i',
    anno_parP pt t loc ->
    annoP annt t i ->
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
  eassumption.
  eassumption.
  eapply cvm_raw_evidence_denote_fact; eauto.

  eassumption.
  eassumption.
  eassumption.
  reflexivity.
Defined.

Lemma appraisal_correct_alt_et : forall t annt pt loc e' tr tr' p p' bits bits' et et' et'' ev i i',
    anno_parP pt t loc ->
    annoP annt t i ->
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
    invc H0.
    erewrite <- eval_aeval.
    eapply cvm_refines_lts_evidence.
    eassumption.
    eassumption.
  }


  (*
  


    
    subst.
    inversion H.
    assert (t = unannoPar pt).
    {
      erewrite anno_unanno_par.
      reflexivity.
      rewrite H4.
      eapply annopar_fst_snd.
    }
    invc H0.
    
    
    rewrite <- eval_aeval.
    invc H.
    
    
    eapply cvm_refines_lts_evidence.
    econstructor.
    reflexivity.
    rewrite H4.
    econstructor.
    eassumption.
    eassumption.
  }
   *)
  
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

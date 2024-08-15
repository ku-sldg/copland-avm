(*
  Primary results/proofs about the Copland Virtual Machine implementation, 
    linking it to the Copland reference semantics.

  Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Anno_Term_Defs ConcreteEvidenceT Appraisal_EvidenceT AutoApp Main.
Require Import ResultT Cvm_Monad Auto External_Facts.
Require Import Axioms_Io Helpers_CvmSemantics Attestation_Session.

Import ListNotations.
Require Import Coq.Program.Tactics.
Require Import Coq.Arith.Peano_dec Lia.


(*
Set Nested Proofs Allowed.
 *)

Lemma splitEv_T_l_LEFT: forall e bits bits' es e0 sp,
    et_size e = es ->
    splitEv_l (ALL,sp) (evc bits e) = (evc bits' e0) ->
    et_size e0 = es.
Proof.
  intros.
  ff.
Qed.

Lemma aeval_anno: forall a i n e0,
    (aeval (snd (anno (unanno a) i)) n e0 = aeval a n e0).
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros; ff;
    repeat jkjke';
    repeat jkjke.
Qed.

Lemma evc_inv: forall e,
    e = evc (get_bits e) (get_et e).
Proof.
  destruct e; eauto.
Qed.

Lemma front_app{A} :
  forall (x:A) xs ys,    
    x :: xs ++ ys = [x] ++ xs ++ ys.
Proof.
  tauto.
Qed.

Lemma back_app{A:Type}: forall (x y:A),
    [x; y] = [x] ++ [y].
Proof.
  tauto.
Qed.

Ltac inv_wfec :=
  repeat
    match goal with
    | [H: wf_ec _ |-  _ ] => invc H
    end.

Lemma wfec_firstn: forall e0 e1 e2,
    wf_ec (evc e0 e1) ->
    firstn (et_size e1) (e0 ++ e2) = e0.
Proof.
  intros.
  inv_wfec.
  jkjke'.
  eapply More_lists.firstn_append.
Qed.

Ltac do_wfec_firstn :=
  match goal with
  | [H: context[(firstn (et_size ?e1) (?e0 ++ ?e2))],
        H2: wf_ec (evc ?e0 ?e1)

     |- _] =>
    
    assert_new_proof_by
      (firstn (et_size e1) (e0 ++ e2) = e0)
      ltac: (eapply wfec_firstn; apply H2)
  end.

Lemma wfec_skipn: forall e0 e1 e2,
    wf_ec (evc e0 e1) ->
    skipn (et_size e1) (e0 ++ e2) = e2.
Proof.
  intros.
  inv_wfec.
  jkjke'.
  eapply More_lists.skipn_append.
Qed.

Ltac do_wfec_skipn :=
  match goal with
  | [H: context[(skipn (et_size ?e1) (?e0 ++ ?e2))],
        H2: wf_ec (evc ?e0 ?e1)

     |- _] =>
    
    assert_new_proof_by
      (skipn (et_size e1) (e0 ++ e2) = e2)
      ltac: (eapply wfec_skipn; apply H2)
  end.

Ltac clear_skipn_firstn :=
  match goal with
  | [H: firstn _ _ = _,
        H2: skipn _ _ = _ |- _]
    => rewrite H in *; clear H;
      rewrite H2 in *; clear H2
  end.

Lemma wfec_encodeEv_etfun:
  forall e,
    wf_ec (evc (encodeEv e) (et_fun e)).
Proof.
  intros.
    
  induction e; intros;
    dd;
    try (econstructor; tauto);
    try (repeat inv_wfec;
         econstructor;
         dd;
         try (erewrite app_length);
         jkjke).
Qed.


(* TODO:  this lemma does not hold for (Some eec ... = Some mtc) case

(** * Recontstructing an EvC value computed by encoding it and computing its type is the same as the original. *)
Lemma recon_same: forall e,
    Some e = reconstruct_ev (evc (encodeEv e) (et_fun e)).
*)


(** * Axiom:  assume parallel CVM threads preserve well-formednesplit_evt of EvC bundles *)
Axiom wf_ec_preserved_par: forall e l t2 p,
    wf_ec e ->
    wf_ec (parallel_vm_thread l t2 p e).

(** * Lemma:  CVM execution preserves well-formednesplit_evt of EvC bundles 
      (EvidenceT Type of sufficient length for raw EvidenceT). *)
Lemma wf_ec_preserved_by_cvm_weak : forall e e' t1 tr tr' i i' ac ac',
    wf_ec e ->
        build_cvmP t1
          {| st_ev := e; st_trace := tr; st_evid := i; st_config := ac |}
          (resultC tt)
          {| st_ev := e'; st_trace := tr'; st_evid := i'; st_config := ac' |} ->
    wf_ec (e').
Proof.
  intuition; eapply wf_ec_preserved_by_cvm; eauto.
Qed.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [(*H: well_formed_r ?t, *)
          H2: wf_ec ?stev,
          H3: build_cvmP ?t
              {| st_ev := ?stev; st_trace := _; st_evid := _; st_config := _ |}
              (resultC tt)
              {| st_ev := ?stev'; st_trace := _; st_evid := _; st_config := _ |}
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm_weak; [(*apply H |*) apply H2 | apply H3])
                                 
    end.

Ltac dest_evc :=
  repeat
    match goal with
    | [H: EvC |-  _ ] => destruct H
    end.


(** * If a raw EvidenceT sequence is non-empty, we can grab a first element. *)
Lemma some_recons' : forall e x,
    length e = S x ->
    exists bs ls', peel_bs e = Some (bs, ls').
Proof.
  intros.
  destruct e;
    ff; eauto.
Qed.

Ltac do_some_recons' :=
  match goal with
  | [H: length ?e = S _ |- _ ] =>
    edestruct some_recons'; [apply H | idtac]
                              
  end; destruct_conjs; jkjke.

Ltac do_rcih :=
  match goal with
  | [H: context[reconstruct_ev' _ _]
               

     |- context[reconstruct_ev' ?e' ?et] ] =>
    assert_new_proof_by
      (exists x, Some x = reconstruct_ev' e' et)
      ltac:(eapply H with (r:=e'); (* TODO:  make r lesplit_evt one-off *)
            try (eapply peel_fact; eauto; tauto);
            try (econstructor; first [eapply firstn_long | eapply skipn_long]; try eauto; try lia))      
  end.


(**  * Event ID spans same for a term and its corresponding core term. *)
Lemma event_id_spans_same : forall t,
    event_id_span' t = event_id_span (copland_compile t).
Proof.
  intros.
  induction t; ff.
  - unfold asp_term_to_core; ffa.
Qed.

(** * Lemma:  CVM increases event IDs according to event_id_span' denotation. *)
Lemma cvm_spans: forall t pt e tr i e' tr' i' ac ac',
    term_to_coreP t pt ->
    build_cvmP
      pt
      {| st_ev := e;
         st_trace := tr;
         st_evid := i;
         st_config := ac |}
      (resultC tt)
      {|
        st_ev := e';
        st_trace := tr';
        st_evid := i';
        st_config := ac'
      |} ->
    i' = i + event_id_span' t.
Proof.
  eapply cvm_spans.
Qed.
  
(** * CVM event ID span same as annotated term range *)
Lemma span_cvm: forall atp t annt i j e e' tr tr' i' ac ac',
    build_cvmP
      atp
      {| st_ev := e;
         st_trace := tr;
         st_evid := i;
         st_config := ac |} 
      (resultC tt)
      {| st_ev := e';
         st_trace := tr';
         st_evid := i';
         st_config := ac' |} ->
    
    term_to_coreP t atp -> 
    anno t i = (j, annt) ->
    j = i'.
Proof.
  eapply span_cvm.
Qed.

(** * Propositional version of span_cvm *)
Lemma anno_span_cvm: forall t pt annt i i' e e' tr tr' st_evid1 ac ac',
    anno t i = (i', annt) ->
    term_to_coreP t pt ->
    build_cvmP pt
      {|
        st_ev := e ;
        st_trace := tr ;
        st_evid := i;
        st_config := ac
      |} (resultC tt)
      {|
        st_ev := e';
        st_trace := tr';
        st_evid := st_evid1; st_config := ac'
      |} ->
    i' = st_evid1.
Proof.
  intros.
  invc H.
  eapply span_cvm; eauto.
Qed.

Axiom events_cvm_to_core_mt_evt: forall t p e,
    cvm_events_core (lseqc (aspc CLEAR) t) p e = cvm_events_core t p mt_evt.

Ltac do_sc_immut := 
  match goal with
  | H : build_cvmP _ 
        {| st_ev := _; st_trace := _; st_evid := _; st_config := ?ac |} 
        _ 
        {| st_ev := _; st_trace := _; st_evid := _; st_config := ?ac' |} 
      |- _ =>
    let HAC := fresh "HAC" in
    eapply build_cvmP_sc_immut in H as HAC;
    simpl in *; rewrite HAC in *; clear HAC
  end.

(** * Theorem:  Main Theorem stating that for an arbitrary Copland phrase, all of its execution traces 
      in the CVM are also captured in the LTS reference semantics. *)
Theorem cvm_refines_lts_events :
  forall t atp annt cvm_tr bits bits' et et' i i' ac ac',
    term_to_coreP t atp ->
    anno t i = (i', annt) ->
    build_cvmP atp
                     (mk_st (evc bits et) [] i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') cvm_tr i' ac') ->
    lstar (conf annt (session_plc ac) et) cvm_tr (stop (session_plc ac) (aeval annt (session_plc ac) et)).
Proof.
  intros t atp annt cvm_tr bits bits' et et' i i' ac ac' annoParPH annPH H'.
  generalizeEverythingElse t.
  induction t; intros; ffa.
  
  - (* aasp case *)
    wrap_ccp_anno.
    
    destruct a; invc annoParPH; ff;
    wrap_ccp_anno;
    
    try (econstructor; econstructor; reflexivity); ffa;
    wrap_ccp_anno; econstructor; econstructor.

 - (* aatt case *)
    wrap_ccp_anno.
    ff.
    assert (n = i + event_id_span' t + 1) by lia.
    subst.
    (* clear H2. *)
   
    assert (t = unanno a) as HN.
    {
      invc Heqp1.
      
      erewrite <- anno_unanno at 1.
      rewrite H.
      tauto.
    }
     
    assert (lstar (conf a p et) (cvm_events t p et) (stop p (aeval a p et))).
    {
      eapply remote_LTS.
      eassumption.
    }
    
    rewrite HN.

    eapply lstar_tran. 
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    rewrite <- HN.
    cbn.
    eassumption.

    simpl.
    assert (aeval a p et = eval (unanno a) p et).
    {
      rewrite <- eval_aeval'.
      tauto.
    }
    repeat find_rewrite.
    
    rewrite <- HN.
    simpl.

    assert (((i + 1 + event_id_span' t)) = Nat.pred (S (i + event_id_span' t + 1))) by lia.

    repeat find_rewrite.

    econstructor.

    apply stattstop.
    econstructor.

  -  (* alseq case *)

    invc annoParPH.
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    fold copland_compile in *.

    inversion annPH.
    subst.
    ff.
    do_anno_indexed_redo.
    do_anno_indexed_redo.
    
    assert (n = H0).
    {
      eapply anno_span_cvm.
      econstructor.
      invc Heqp.
      eassumption.
      2: { eauto. }
      econstructor; tauto.
    }
    subst.

    destruct x.
    
    econstructor.
    econstructor.
    eapply lstar_transitive.
    eapply lstar_stls.
    
    eapply IHt1; eauto.
    econstructor; tauto.

    eapply lstar_silent_tran.
    apply stlseqstop.

    assert (e = aeval a (session_plc ac') et).

     {
      rewrite <- eval_aeval'.
      assert (t1 = unanno a).
    {
      symmetry.
      invc Heqp.
      erewrite <- anno_unanno.
      rewrite H5.
      tauto.
    }
    eapply build_cvmP_sc_immut in H2 as HAC1.
    eapply build_cvmP_sc_immut in H4 as HAC2;
    simpl in *.
    eapply cvm_refines_lts_EvidenceT.
    econstructor; eauto.
    rewrite <- H5; eauto.
    subst; eauto.
     }
     subst.

    eapply build_cvmP_sc_immut in H' as HAC1.
    eapply build_cvmP_sc_immut in H2 as HAC2.
    simpl in *; subst.

    eapply IHt2; eauto. (*with (e:= x). *)

    econstructor; tauto.

  - (* abseq case *)

    wrap_ccp_anno;
    repeat (try cbn in *; ff);
    wrap_ccp_anno;
    repeat (try cbn in *; ff);
    repeat match goal with
    | u : unit |- _ => destruct u
    end;
    repeat do_sc_immut.
    +

    assert (n = st_evid1).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      eapply span_cvm.
      eassumption.
      econstructor; tauto.
      invc Heqp.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    assert (
        lstar (conf a (session_plc ac') et) blah' (stop (session_plc ac') (aeval a (session_plc ac') et))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1; eauto.
      econstructor; tauto.
      eapply restl.
      eassumption.
    }

    assert (
      lstar (conf a0 (session_plc ac')  et) blah (stop (session_plc ac') (aeval a0 (session_plc ac')  et))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      eapply IHt2; eauto.
      econstructor; tauto.
      eapply restl.
      eauto.
    }

    eapply lstar_transitive.
    simpl.

    eapply lstar_stbsl.
    eassumption.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
    eassumption.

    assert (st_evid = Nat.pred (st_evid + 1)) by lia.
    ffa.
    econstructor; eauto; simpl in *.
    +

    assert (n = st_evid1).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      eapply span_cvm.
      eassumption.
      econstructor; tauto.
      invc Heqp.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    assert (
        lstar (conf a (session_plc ac') et) blah' (stop (session_plc ac') (aeval a (session_plc ac') et))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1; eauto.
      econstructor; tauto.
      eapply restl.
      eauto.
    }

    assert (
      lstar (conf a0 (session_plc ac')  mt_evt) blah (stop (session_plc ac') (aeval a0 (session_plc ac') mt_evt))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
      eapply IHt2.
      econstructor; tauto.
      eassumption.
      eapply restl.
      eassumption.

    }

    eapply lstar_transitive.
    simpl.

    eapply lstar_stbsl.
    eassumption.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
    eassumption.

    assert (st_evid = Nat.pred (st_evid + 1)) by lia.
    ffa.

    
    econstructor.

    eapply stbsrstop.
    econstructor.

        +

    assert (n = st_evid1).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      eapply span_cvm.
      eassumption.
      econstructor; tauto.
      invc Heqp.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    assert (
        lstar (conf a (session_plc ac') mt_evt) blah' (stop (session_plc ac') (aeval a (session_plc ac') mt_evt))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eapply restl.
      eassumption.
    }

    assert (
      lstar (conf a0 (session_plc ac')  et) blah (stop (session_plc ac') (aeval a0 (session_plc ac')  et))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
      eapply IHt2.
      econstructor; tauto.
      eassumption.
      eapply restl.
      eassumption.

    }

    eapply lstar_transitive.
    simpl.

    eapply lstar_stbsl.
    eassumption.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
    eassumption.

    assert (st_evid = Nat.pred (st_evid + 1)) by lia.
    ffa.

    
    econstructor.

    eapply stbsrstop.
    econstructor.

        +

    assert (n = st_evid1).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      eapply span_cvm.
      eassumption.
      econstructor; tauto.
      invc Heqp.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    assert (
        lstar (conf a (session_plc ac') mt_evt) blah' (stop (session_plc ac') (aeval a (session_plc ac') mt_evt))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eapply restl.
      eassumption.
    }

    assert (
      lstar (conf a0 (session_plc ac')  mt_evt) blah (stop (session_plc ac') (aeval a0 (session_plc ac')  mt_evt))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
      eapply IHt2.
      econstructor; tauto.
      eassumption.
      eapply restl.
      eassumption.

    }

    eapply lstar_transitive.
    simpl.

    eapply lstar_stbsl.
    eassumption.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
    eassumption.

    assert (st_evid = Nat.pred (st_evid + 1)) by lia.
    ffa.

    
    econstructor.

    eapply stbsrstop.
    econstructor.

  - (* abpar case *)

    wrap_ccp_anno;
    repeat (try cbn in *; ff);
    wrap_ccp_anno;
    repeat (try cbn in *; ff);
    repeat match goal with
    | u : unit |- _ => destruct u
    end;
    repeat do_sc_immut.

    +

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      invc Heqp.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. 
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a (session_plc ac') et) blah (stop (session_plc ac') (aeval a (session_plc ac') et))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eapply restl.
      eassumption.

    }

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start 0 (session_plc ac') (copland_compile t2) et]
                ++
                blah ++
                [cvm_thread_end 0] =
              shuffled_events blah (cvm_events_core  (copland_compile t2) (session_plc ac') et)).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      jkjke.
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      ffa.

      eapply lstar_tran.

      apply stbpstop.
      econstructor.

    +

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      invc Heqp.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst.
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a (session_plc ac') et) blah (stop (session_plc ac') (aeval a (session_plc ac') et))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eapply restl.
      eassumption.

    }

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) et]
                ++
                blah ++
                [cvm_thread_end 0] =
              shuffled_events blah (cvm_events_core (lseqc (aspc CLEAR) (copland_compile t2)) (session_plc ac') et)).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      rewrite H2.
   
      rewrite events_cvm_to_core_mt_evt.
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      ffa.

      eapply lstar_tran.

      apply stbpstop.
      econstructor.

    +

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      invc Heqp.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst.
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a (session_plc ac') mt_evt) blah (stop (session_plc ac') (aeval a (session_plc ac') mt_evt))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eapply restl.
      eassumption.

    }

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start 0 (session_plc ac') ((copland_compile t2)) et]
                ++
                blah ++
                [cvm_thread_end 0] =
              shuffled_events blah (cvm_events_core (copland_compile t2) (session_plc ac') et)).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      rewrite H2.
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      ffa.

      eapply lstar_tran.

      

      apply stbpstop.
      econstructor.
    +

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      invc Heqp.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a (session_plc ac') mt_evt) blah (stop (session_plc ac') (aeval a (session_plc ac') mt_evt))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eapply restl.
      eassumption.

    }

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) et]
                ++
                blah ++
                [cvm_thread_end 0] =
              shuffled_events blah (cvm_events_core (lseqc (aspc CLEAR) (copland_compile t2)) (session_plc ac') et)).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      rewrite H2.
   
      rewrite events_cvm_to_core_mt_evt.
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      ffa.

      eapply lstar_tran.

      

      apply stbpstop.
      econstructor.
Qed.



(** * Main correctnesplit_evt theorem about CVM events:  event orderings respect the 
      event system (partial order) reference semantics. *)
Theorem cvm_respects_event_system :
  forall atp annt t cvm_tr ev0 ev1 bits bits' et et' i i' ac ac',
    anno t i = (i', annt) ->
    term_to_coreP t atp ->
    build_cvmP atp
                     (mk_st (evc bits et) [] i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') cvm_tr i' ac') ->
    prec (ev_sys annt (session_plc ac) et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  assert (well_formed_r_annt annt).
  {
  eapply anno_well_formed_r.
  invc H.
  eassumption.
  }
    
  eapply ordered.
  eapply anno_well_formed_r.
  invc H.
  eassumption.
  eapply cvm_refines_lts_events; eauto.
  eassumption.
Qed.





Lemma fufu : forall t1 cvmi p ct e ac ac' st_evid r0 e0 blah, 
p = (session_plc ac) ->
build_cvmP (copland_compile t1)
    {|
      st_ev := evc [] mt_evt;
      st_trace := [Term_Defs.split cvmi p; cvm_thread_start 0 p ct e];
      st_evid := S cvmi;
      st_config := ac
    |} (resultC tt)
    {|
      st_ev := evc r0 e0;
      st_trace :=
        Term_Defs.split cvmi p :: (cvm_thread_start 0 p ct e) :: blah;
      st_evid := st_evid;
      st_config := ac'
    |}
    =
    build_cvmP (copland_compile t1)
    {|
      st_ev := evc [] mt_evt;
      st_trace := [Term_Defs.split cvmi p; cvm_thread_start 0 p ct e];
      st_evid := S cvmi;
      st_config := ac
    |} (resultC tt)
    {|
      st_ev := evc r0 e0;
      st_trace :=
        ([Term_Defs.split cvmi p; cvm_thread_start 0 p ct e] ++ blah);
      st_evid := st_evid;
      st_config := ac'
    |}.
Proof.
  ff.
Qed.

Axiom cvm_thread_start_clear : forall t p e n,
(cvm_thread_start n p (lseqc (aspc CLEAR) (copland_compile t)) e) = 
(cvm_thread_start n p (copland_compile t)) mt_evt.

Axiom cvm_thread_in_ev : forall n p ev t e blah,
In ev ([cvm_thread_start n p (copland_compile t) e] ++ blah ++ [cvm_thread_end 0]) -> 
(In ev (cvm_events_core (copland_compile t) p e) \/ 
In ev blah).

Axiom cvm_EvidenceT_exists_remote : forall t p e,
  exists b et, 
  cvm_EvidenceT_core t p e = evc b et.


Lemma cvm_implies_events: forall t annt e e' bits bits' cvmi cvmi' cvm_tr ev ac ac',
    anno t cvmi = (cvmi', annt)->

    build_cvmP (copland_compile t)
      {| st_ev := evc bits e; st_trace := []; st_evid := cvmi; st_config := ac |} 
      (resultC tt) 
      {| st_ev := evc bits' e'; st_trace := cvm_tr; st_evid := cvmi'; st_config := ac' |} ->

    In ev cvm_tr ->

    events annt (session_plc ac) e ev.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* asp case *)
    wrap_ccp_anno;
    repeat ff;
    destruct a; invc H; repeat ff;
      wrap_ccp_anno;
      repeat ff;
      try destruct s; wrap_ccp_anno;
      try destruct f;
      try destruct H1;
      subst;
      try solve_by_inversion;
    
      try (econstructor; econstructor; reflexivity).
  -
    wrap_ccp_anno.
    ff.

    assert (n = cvmi + event_id_span' t + 1) by lia.
    subst.
   
    assert (t = unanno a) as H11.
    {
      invc Heqp0.
      
      erewrite <- anno_unanno at 1.
      rewrite H0.
      tauto.
    }


    door.
    +
      rewrite <- H0.
      rewrite H11.
      apply evtsattreq.
      auto.
    +
      assert ( (In ev (cvm_events t p e)) \/
               ev = (rpy (cvmi + 1 + event_id_span' t) (session_plc ac') p (eval t p e)
                         (* (get_et (IO_Stubs.doRemote_session t p (evc bits e))) *) )
             ).
      {

        apply in_app_or in H0.
        door.
        +
          left; eauto.
        +
          right.
          invc H0;
            try auto;
            try solve_by_inversion.
      }
      
      door; ffa using cvm_monad_unfold; eauto;
      try (subst; rewrite eval_aeval'; apply evtsattrpy; simpl; lia).
      econstructor.
      assert (exists ac, p = (session_plc ac)).
      {
        exists (Build_Session_Config p (ASP_to_APPR_ASP_Map ac')
          (aspCb ac') (plc_map ac') (pubkey_map ac') (policy ac'));
        ffa.
      }
      break_exists.
      ffa.
      pose proof (build_cvm_external (copland_compile (unanno a))
        (evc bits e) (S cvmi) x).
      simpl in *.
      rewrite ccp_iff_cc in *.
      unfold cvm_events.
      pose proof (cvm_EvidenceT_exists_remote 
        (copland_compile (unanno a)) (session_plc x) (evc bits e)).
      break_exists.
      find_rewrite.
      repeat rewrite event_id_works in *.
      repeat rewrite <- event_id_works in *.
      rewrite PeanoNat.Nat.add_1_r in *.
      eapply IHt; eauto.

  - (* alseq case *)
    invc H.
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    fold copland_compile in *.

    inversion H2.
    subst.
    ff.
    do_anno_indexed_redo.
    do_anno_indexed_redo.

    repeat do_sc_immut.
    
    assert (n = H3).
    {
      eapply anno_span_cvm; eauto;
      econstructor; eauto.
    }
    subst.

    
    destruct x.
     

    assert (In ev H \/ In ev H6).
    {
      apply in_app_or in H1.
        door.
        +
          left; eauto.
        +
          right.
          invc H0;
            try auto;
            try solve_by_inversion.
    }

    door.
    +
      apply evtslseql; ffa.
    +

      

    assert (e0 = aeval a (session_plc ac') e).
      {
      rewrite <- eval_aeval'.
      assert (t1 = unanno a).
    {
      symmetry.
      match goal with
      | H : annoP_indexed _ t1 _ _ |- _ => invc H
      end.
      erewrite <- anno_unanno.
      rewrite H8; ffa.
    }
    eapply cvm_refines_lts_EvidenceT.
    econstructor; eauto.
    rewrite <- H8.
    eassumption.
      }
      find_rewrite.
      

      match goal with
      | H : annoP_indexed _ t2 _ _ |- _ => invc H
      end.
      apply evtslseqr.
      eapply IHt2.
      econstructor.
      eassumption.
      eassumption.
      eassumption.
  - (* abseq case *)
    wrap_ccp_anno;
    repeat (try cbn in *; ff);
    wrap_ccp_anno;
    repeat (try cbn in *; ff);
    repeat match goal with
    | u : unit |- _ => destruct u
    end;
    repeat do_sc_immut.

    +

    assert (n = st_evid1).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      eapply span_cvm.
      eassumption.
      econstructor; tauto.
      invc Heqp.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi (session_plc ac') \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid (session_plc ac')).
    {
      apply in_app_or in H1.
      door.
      +
        
        apply in_app_or in H0.
        door.
        ++
          apply in_app_or in H0.
          door.
          +++
            invc H0; try eauto; try solve_by_inversion.
          +++
            eauto.
        ++
          eauto.
      +
        invc H0; try eauto; try solve_by_inversion.
    }

    door.
    subst.
    apply evtsbseqsplit.
    tauto.

    door.
    ff.

    apply evtsbseql.
    simpl.
    assert (S cvmi = cvmi + 1) by lia.
    rewrite <- H3 in *.
    subst.
    eapply IHt1.
    eassumption.
    eapply restl.
    assert (Term_Defs.split cvmi (session_plc ac') :: blah' = 
    [Term_Defs.split cvmi (session_plc ac')] ++ blah'). 
    {
      intuition.
    }
    repeat find_rewrite.
    eassumption.
    eassumption.


    door.

    apply evtsbseqr.
    simpl.

    eapply IHt2.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.

    subst.

    apply evtsbseqjoin.
    simpl.
    lia.

    +
          assert (n = st_evid1).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      eapply span_cvm.
      eassumption.
      econstructor; tauto.
      invc Heqp.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi (session_plc ac') \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid (session_plc ac')).
    {
            apply in_app_or in H1.
      door.
      +
        
        apply in_app_or in H0.
        door.
        ++
          apply in_app_or in H0.
          door.
          +++
            invc H0; try eauto; try solve_by_inversion.
          +++
            eauto.
        ++
          eauto.
      +
        invc H0; try eauto; try solve_by_inversion.
    }
    door.
    subst.
    apply evtsbseqsplit.
    tauto.

    door.
    ff.

    apply evtsbseql.
    simpl.
    assert (S cvmi = cvmi + 1) by lia.
    rewrite <- H3 in *.
    subst.
    eapply IHt1.
    eassumption.
    eapply restl.
    assert (Term_Defs.split cvmi (session_plc ac') :: blah' = 
    [Term_Defs.split cvmi (session_plc ac')] ++ blah'). 
    {
      intuition.
    }
    repeat find_rewrite.
    eassumption.
    eassumption.


    door.

    apply evtsbseqr.
    simpl.

    eapply IHt2.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.

    subst.

    apply evtsbseqjoin.
    simpl.
    lia.

    +
          assert (n = st_evid1).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      eapply span_cvm.
      eassumption.
      econstructor; tauto.
      invc Heqp.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi (session_plc ac') \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid (session_plc ac')).
    {
            apply in_app_or in H1.
      door.
      +
        
        apply in_app_or in H0.
        door.
        ++
          apply in_app_or in H0.
          door.
          +++
            invc H0; try eauto; try solve_by_inversion.
          +++
            eauto.
        ++
          eauto.
      +
        invc H0; try eauto; try solve_by_inversion.
    }
    door.
    subst.
    apply evtsbseqsplit.
    tauto.

    door.
    ff.

    apply evtsbseql.
    simpl.
    assert (S cvmi = cvmi + 1) by lia.
    rewrite <- H3 in *.
    subst.
    eapply IHt1.
    eassumption.
    eapply restl.
    assert (Term_Defs.split cvmi (session_plc ac') :: blah' = 
    [Term_Defs.split cvmi (session_plc ac')] ++ blah'). 
    {
      intuition.
    }
    repeat find_rewrite.
    eassumption.
    eassumption.


    door.

    apply evtsbseqr.
    simpl.

    eapply IHt2.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.

    subst.

    apply evtsbseqjoin.
    simpl.
    lia.

    +
          assert (n = st_evid1).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      eapply span_cvm.
      eassumption.
      econstructor; tauto.
      invc Heqp.
      eassumption.
    }
    subst.

    assert (n0 = st_evid) by lia.
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi (session_plc ac') \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid (session_plc ac')).
    {
            apply in_app_or in H1.
      door.
      +
        
        apply in_app_or in H0.
        door.
        ++
          apply in_app_or in H0.
          door.
          +++
            invc H0; try eauto; try solve_by_inversion.
          +++
            eauto.
        ++
          eauto.
      +
        invc H0; try eauto; try solve_by_inversion.
    }
    door.
    subst.
    apply evtsbseqsplit.
    tauto.

    door.
    ff.

    apply evtsbseql.
    simpl.
    assert (S cvmi = cvmi + 1) by lia.
    rewrite <- H3 in *.
    subst.
    eapply IHt1.
    eassumption.
    eapply restl.
    assert (Term_Defs.split cvmi (session_plc ac') :: blah' = 
    [Term_Defs.split cvmi (session_plc ac')] ++ blah'). 
    {
      intuition.
    }
    repeat find_rewrite.
    eassumption.
    eassumption.


    door.

    apply evtsbseqr.
    simpl.

    eapply IHt2.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.

    subst.

    apply evtsbseqjoin.
    simpl.
    lia.


  - (* abpar case *)

    wrap_ccp_anno;
    repeat (try cbn in *; ff);
    wrap_ccp_anno;
    repeat (try cbn in *; ff);
    repeat match goal with
    | u : unit |- _ => destruct u
    end;
    repeat do_sc_immut.


    +

    assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp.
      
      eapply span_cvm; eauto.
      
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi (session_plc ac') \/
            In ev ([cvm_thread_start 0 (session_plc ac') (copland_compile t2) e] ++
                   blah ++ [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')).
    {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi (session_plc ac');
            cvm_thread_start 0 (session_plc ac') (copland_compile t2) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi (session_plc ac')] ++ 
              ([(cvm_thread_start 0 (session_plc ac') (copland_compile t2) e)] ++ blah ++
                                                               [cvm_thread_end 0]))).
      {
        simpl.
        tauto.
      }
      rewrite H1 in H0.

        apply in_app_or in H0.
        door.
      ++
        invc H0; try eauto; try solve_by_inversion.
      ++
        eauto.

      + invc H0; try eauto; try solve_by_inversion.
    }


    door.
    subst.

    apply evtsbparsplit.
    auto.
    door.
    rewrite thread_bookend_peel in H0.

    assert (In ev [Term_Defs.split cvmi (session_plc ac')] \/ 
            In ev (cvm_events_core (copland_compile t2) (session_plc ac') e) \/ 
            In ev blah \/ 
            In ev [join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')]).
    {

    invc H1.
    left; eauto.
    auto with *.

    assert (In ev ([cvm_thread_start 0 (session_plc ac') (copland_compile t2) e] ++ blah ++ [cvm_thread_end 0]) \/ 
            In ev [join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')]).
            {
              auto with *.
            }

            invc H1.

            assert (In ev (cvm_events_core (copland_compile t2) (session_plc ac') e) \/ 
                    In ev blah).
                    {
                      eapply cvm_thread_in_ev; eassumption.
                    }

                    door.
                    eauto.
                    eauto.
                    eauto.
    }

    door.

    invc H4; try solve_by_inversion.

    door.

    eapply evtsbparr.

    pose (build_cvm_external (copland_compile t2) (evc bits e) st_evid ac').

    assert (exists b et, cvm_EvidenceT_core (copland_compile t2) (session_plc ac') (evc bits e) = 
    evc b et).
    {
      eapply cvm_EvidenceT_exists_remote.
    }
    destruct_conjs.
    rewrite H7 in *.

    eapply IHt2.
    eassumption.
    simpl.
    econstructor.
    eassumption.
    ffa.

    door.

    apply evtsbparl.
    eapply IHt1.

    eassumption.
    simpl.
    assert (S cvmi =  cvmi + 1) by lia.
    rewrite H5.
    eapply restl.
    eassumption.
    eassumption.

    invc H4; try solve_by_inversion; subst.
    auto.
    subst.

    eapply evtsbparjoin.
    simpl.
    lia.


    +
      assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.


    assert (ev = Term_Defs.split cvmi (session_plc ac') \/
            In ev ([cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah ++
                   [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')
           ).
    {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi (session_plc ac');
            cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi (session_plc ac')] ++ 
              ([(cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) e)] ++ blah ++
                                                               [cvm_thread_end 0]))).
      {
        simpl.
        tauto.
      }
      rewrite H1 in H0.

        apply in_app_or in H0.
        door.
      ++
        invc H0; try eauto; try solve_by_inversion.
      ++
        eauto.

      + invc H0; try eauto; try solve_by_inversion.
    }
  
    door.
    subst.

    apply evtsbparsplit.
    auto.
    door.
    rewrite thread_bookend_peel in H0; eauto.


    assert (In ev [Term_Defs.split cvmi (session_plc ac')] \/ 
    In ev (cvm_events_core (copland_compile t2) (session_plc ac') mt_evt) \/ 
    In ev blah \/ 
    In ev [join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')]).
  {

  invc H1.
  left; eauto.
  auto with *.



  Unset Printing Notations.

  assert (In ev ([cvm_thread_start 0 (session_plc ac') (copland_compile t2) mt_evt] ++ blah ++ [cvm_thread_end 0]) \/ 
          In ev [join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')]).
          {
            assert (
              (cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) e) = 
              (cvm_thread_start 0 (session_plc ac') (copland_compile t2)) mt_evt).
              {
                eapply cvm_thread_start_clear.
              }
              rewrite H1 in *; clear H1.

              auto with *.

          }

          invc H1.

          assert (In ev (cvm_events_core (copland_compile t2) (session_plc ac') mt_evt) \/ 
                  In ev blah).
                  {
                    eapply cvm_thread_in_ev; eassumption.
                  }

                  door.
                  eauto.
                  eauto.
                  eauto.

  }

  door.

  invc H4; try solve_by_inversion.

  door.

  eapply evtsbparr.

  pose (build_cvm_external (copland_compile t2) (evc bits mt_evt) st_evid ac').

  assert (exists b et, cvm_EvidenceT_core (copland_compile t2) (session_plc ac') (evc bits mt_evt) = 
  evc b et).
  {
    eapply cvm_EvidenceT_exists_remote.
  }
  destruct_conjs.
  rewrite H7 in *.

  eapply IHt2.
  eassumption.
  econstructor.
  simpl.
  eassumption.

  apply H4.


  door.

  apply evtsbparl.
  eapply IHt1.

  eassumption.
  simpl.
  assert (S cvmi =  cvmi + 1) by lia.
  rewrite H5.
  eapply restl.
  eassumption.
  eassumption.

  invc H4; try solve_by_inversion.
  ffa.

    +
      assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi (session_plc ac') \/
            In ev ([cvm_thread_start 0 (session_plc ac') (copland_compile t2) e] ++
                   blah ++ [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')).
        {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi (session_plc ac');
            cvm_thread_start 0 (session_plc ac') (copland_compile t2) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi (session_plc ac')] ++ 
              ([(cvm_thread_start 0 (session_plc ac') (copland_compile t2) e)] ++ blah ++
                                                               [cvm_thread_end 0]))).
      {
        simpl.
        tauto.
      }
      rewrite H1 in H0.

        apply in_app_or in H0.
        door.
      ++
        invc H0; try eauto; try solve_by_inversion.
      ++
        eauto.

      + invc H0; try eauto; try solve_by_inversion.
    }

    door.
    subst.

    apply evtsbparsplit.
    auto.
    door.
    rewrite thread_bookend_peel in H0.




    assert (In ev [Term_Defs.split cvmi (session_plc ac')] \/ 
    In ev (cvm_events_core (copland_compile t2) (session_plc ac') e) \/ 
    In ev blah \/ 
    In ev [join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')]).
  {

  invc H1.
  left; eauto.
  auto with *.

  assert (In ev ([cvm_thread_start 0 (session_plc ac') (copland_compile t2) e] ++ blah ++ [cvm_thread_end 0]) \/ 
          In ev [join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')]).
          {
            auto with *.
          }

          invc H1.

          assert (In ev (cvm_events_core (copland_compile t2) (session_plc ac') e) \/ 
                  In ev blah).
                  {
                    eapply cvm_thread_in_ev; eassumption.
                  }

                  door.
                  eauto.
                  eauto.
                  eauto.

  }

  door.

  invc H4; try solve_by_inversion.

  door.

  eapply evtsbparr.



  pose (build_cvm_external (copland_compile t2) (evc bits e) st_evid ac').

  assert (exists b et, cvm_EvidenceT_core (copland_compile t2) (session_plc ac') (evc bits e) = 
  evc b et).
  {
    eapply cvm_EvidenceT_exists_remote.
  }
  destruct_conjs.
  rewrite H7 in *.



  eapply IHt2.
  eassumption.

  simpl.
  econstructor.
  eassumption.

  apply H4.


  door.

  apply evtsbparl.
  eapply IHt1.

  eassumption.
  simpl.
  assert (S cvmi =  cvmi + 1) by lia.
  rewrite H5.
  eapply restl.
  eassumption.
  eassumption.

  invc H4; try solve_by_inversion.
  auto.
  ffa.

      +
        assert (n = st_evid).
      {
        assert (cvmi+1 = S cvmi) by lia.
        find_rewrite.
        invc Heqp.
        
        eapply span_cvm; eauto.
        econstructor; tauto.
      }
      subst.

      assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
      
      subst.
      
      
      
      do_suffix blah.

      destruct_conjs; subst.
      repeat do_restl.

      assert (ev = Term_Defs.split cvmi (session_plc ac') \/
              In ev ([cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah ++
                    [cvm_thread_end 0]) \/
              ev = join (st_evid + event_id_span (copland_compile t2)) (session_plc ac')
            ).
          {
        apply in_app_or in H1.
        door.
        +
        assert(
            (([Term_Defs.split cvmi (session_plc ac');
              cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah) ++
                                                                    [cvm_thread_end 0]) =
              ([Term_Defs.split cvmi (session_plc ac')] ++ 
                ([(cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) e)] ++ blah ++
                                                                [cvm_thread_end 0]))).
        {
          simpl.
          tauto.
        }
        rewrite H1 in H0.

          apply in_app_or in H0.
          door.
        ++
          invc H0; try eauto; try solve_by_inversion.
        ++
          eauto.

        + invc H0; try eauto; try solve_by_inversion.
      }

      door.
      subst.

      apply evtsbparsplit.
      auto.
      door.
      Unset Printing Notations.

      assert (
        (cvm_thread_start 0 (session_plc ac') (lseqc (aspc CLEAR) (copland_compile t2)) e) = 
        (cvm_thread_start 0 (session_plc ac') (copland_compile t2)) mt_evt).
        {
          eapply cvm_thread_start_clear.
        }
        rewrite H4 in *.

      assert (
              In ev (cvm_events_core (copland_compile t2) (session_plc ac') mt_evt) \/ 
              In ev blah).
              {

                eapply cvm_thread_in_ev; eassumption.


              }
      door.

      2: {

      apply evtsbparl.

      simpl in *.
      unfold mt_evc in *.
      assert (S cvmi = cvmi + 1) by lia.
      rewrite <- H6 in *.


      eapply IHt1.
      eassumption.
      eapply restl; eauto.

      rewrite fufu in *; eauto.
      eauto.
      }


      apply evtsbparr.



      pose (build_cvm_external (copland_compile t2) (evc bits mt_evt) st_evid ac').

  assert (exists b et, cvm_EvidenceT_core (copland_compile t2) (session_plc ac') (evc bits mt_evt) = 
  evc b et).
  {
    eapply cvm_EvidenceT_exists_remote.
  }
  destruct_conjs.
  rewrite H8 in *.





      simpl.

      eapply IHt2.
      eassumption.

      econstructor; ffa.
      ffa.
      ffa.
Qed.













































(*

NOTE:  this no longer holds with error results of CVM execution
TODO:  see if lemma can be generalized (i.e. to trace prefixes?)

(** * Slight reformulation of cvm_refines_events, in terms of st_trace. *)
Corollary cvm_refines_lts_event_ordering_corrolary :
  forall t annt atp cvm_tr bits et p i i' ac,
    anno t i = (i', annt) ->
    term_to_coreP t atp ->
    st_trace (run_cvm atp
                      (mk_st (evc bits et) [] p i ac)) = cvm_tr ->
    lstar (conf annt p et) cvm_tr (stop p (aeval annt p et)).
Proof.
  intros.
  destruct (build_cvm atp {| st_ev := (evc bits et);
                                   st_trace := [];
                                   st_pl := p;
                                   st_evid := i; st_config := ac |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  (* do_asome. *)
  subst.
  
  destruct st_ev.

  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.

  assert (i' = st_evid).
  {
    eapply anno_span_cvm; eauto.
    econstructor.
    eapply restl.
    eassumption.
  }
  subst.
  
  eapply cvm_refines_lts_events; eauto.
  econstructor; eauto.
Qed.

*)


(*

NOTE:  this no longer holds with error results of CVM execution
See note above for cvm_refines_lts_event_ordering_corrolary

Corollary cvm_respects_event_system_run :
  forall atp annt t cvm_tr ev0 ev1 bits et i i' plc_id ac,
    anno t i = (i', annt) ->
    term_to_coreP t atp ->
    st_trace (run_cvm atp (mk_st (evc bits et) [] plc_id i ac)) = cvm_tr ->
    
    prec (ev_sys annt plc_id et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  unfold run_cvm in *.
  ff.
  (* do_somett. *)
  vmsts.
  subst.
  simpl.
  do_pl_immut.
  subst.
  assert (i' = st_evid).
  {
    eapply anno_span_cvm; eauto.
    econstructor; eassumption.
  }
  subst.
  destruct st_ev.
  eapply cvm_respects_event_system; eauto.
  econstructor; eassumption.
Qed.

Corollary cvm_respects_event_system_run' : forall atp annt t cvm_tr ev0 ev1 bits et plc_id ac,
    annt = annotated t ->
    copland_compile t = atp ->
    st_trace (run_cvm atp (mk_st (evc bits et) [] plc_id 0 ac)) = cvm_tr ->
    
    prec (ev_sys annt plc_id et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  destruct (anno t 0) eqn: hi.

  assert (term_to_coreP t atp).
  {
    econstructor; eauto.
  }
  
  eapply cvm_respects_event_system_run; eauto.
  unfold annotated in *.
  ff.
  econstructor. eassumption.
Qed.

*)
  

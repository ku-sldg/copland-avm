(*
Proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Defs Term_Defs Anno_Term_Defs ConcreteEvidence LTS Event_system Term_system Main Appraisal_Evidence AutoApp.
Require Import Cvm_Monad StructTactics Auto.
Require Import Axioms_Io Cvm_Impl Cvm_Run External_Facts Helpers_CvmSemantics Evidence_Bundlers.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec Lia.


(*
Set Nested Proofs Allowed.
 *)

Lemma splitEv_T_l_LEFT: forall e bits bits' es e0 sp,
    et_size e = es ->
    splitEv_l (ALL,sp) (evc bits e) = (evc bits' e0) ->
    et_size e0 = es. (* (splitEv_T_l LEFT es). *)
Proof.
  intros.
  ff.
Defined.

Lemma aeval_anno: forall a i n e0,
    (aeval (snd (anno (unanno a) i)) n e0 = aeval a n e0).
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros; ff;
    repeat jkjke';
    repeat jkjke.
Defined.

Lemma evc_inv: forall e,
    e = evc (get_bits e) (get_et e).
Proof.
  destruct e; eauto.
Defined.

Lemma front_app{A} :
  forall (x:A) xs ys,    
    x :: xs ++ ys = [x] ++ xs ++ ys.
Proof.
  tauto.
Defined.

Lemma back_app{A:Type}: forall (x y:A),
    [x; y] = [x] ++ [y].
Proof.
  tauto.
Defined.

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
Defined.

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
Defined.

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

  (*
  induction e; intros.
  -
    ff.
    econstructor; eauto.
  -
    ff.
    econstructor; eauto.
  -
    ff.
    econstructor.
    ff.
    invc IHe.
    eauto.
  -
    destruct f.
    +
      ff.
      econstructor. ff.
    +
      ff.
      econstructor. ff.
    +
      ff.
      econstructor.
      ff.
      
      
    ff.
    
    *)
    
    
    
  
  induction e; intros;
    dd;
    try (econstructor; tauto);
    try (repeat inv_wfec;
         econstructor;
         dd;
         try (erewrite app_length);
         jkjke).
Defined.


(* TODO:  this lemma does not hold for (Some eec ... = Some mtc) case

(** * Recontstructing an EvC value computed by encoding it and computing its type is the same as the original. *)
Lemma recon_same: forall e,
    Some e = reconstruct_ev (evc (encodeEv e) (et_fun e)).
Proof.
  intros.
  induction e; intros;
    dd;
    try (try jkjke'; tauto);
    try ( (* ss and pp cases *)
        assert (wf_ec (evc (encodeEv e1) (et_fun e1))) by
          (eapply wfec_encodeEv_etfun);
        ff;
        try (unfold OptMonad_Coq.bind);
        ff;
      try do_wfec_firstn;
      try do_wfec_skipn;
      repeat find_rewrite;
      try solve_by_inversion;
      try (repeat find_inversion; tauto)).
  Locate encodeEv.
  Locate reconstruct_ev.
Defined.
*)



(** * Axiom:  assume parallel CVM threads preserve well-formedness of EvC bundles *)
Axiom wf_ec_preserved_par: forall e l t2 p,
    wf_ec e ->
    wf_ec (parallel_vm_thread l t2 p e).

(** * Lemma:  CVM execution preserves well-formedness of EvC bundles 
      (Evidence Type of sufficient length for raw evidence). *)
Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' p p' i i',
    wf_ec e ->
        build_cvmP t1
                    {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |}
                    (Some tt)
                    {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
    wf_ec (e').
Proof.
  intros.
  generalizeEverythingElse t1.
  induction t1; intros.
  -
    rewrite <- ccp_iff_cc in *.
    destruct a; (* asp *)
      try destruct a; (* asp params *)
      ff;
      inv_wfec;
      try (
          econstructor;
          ff;
          try tauto;
          try congruence).
    +
      destruct f.
      ++
        ff.
        econstructor.
        ff.
      ++
        ff.
        econstructor.
        ff.
      ++
        ff.
        econstructor.
        ff.        
        congruence.
      ++
        ff.
        econstructor.
        ff.
      ++
        ff.
        econstructor.
        ff.
        
        
  -
    wrap_ccp.

    eapply wf_ec_preserved_remote; eauto.

  -
    wrap_ccp.
    eauto.
  -
    wrap_ccp.

    (*

    do_wfec_split. *)

    find_apply_hyp_hyp.
    find_apply_hyp_hyp.
    econstructor.
    dd.
    inv_wfec.
    repeat jkjke'.
    eapply app_length.

  -
    wrap_ccp.

    (*
    
    do_wfec_split. *)

    find_apply_hyp_hyp.

      inv_wfec;
      ff;
      econstructor;
      dd;
      repeat jkjke'.

    erewrite app_length.

    assert (wf_ec (evc r0 e1)).
    {
      rewrite <- Heqe1.
      eapply wf_ec_preserved_par.
      econstructor; eassumption.
    }

    solve_by_inversion.
Qed.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [(*H: well_formed_r ?t, *)
          H2: wf_ec ?stev,
              H3: build_cvmP ?t
                                   {| st_ev := ?stev; st_trace := _; st_pl := _; st_evid := _ |}
                                   (Some tt)
                                   {| st_ev := ?stev'; st_trace := _; st_pl := _; st_evid := _ |}
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [(*apply H |*) apply H2 | apply H3])
                                 
    end.

Ltac dest_evc :=
  repeat
    match goal with
    | [H: EvC |-  _ ] => destruct H
    end.


(** * If a raw evidence sequence is non-empty, we can grab a first element. *)
Lemma some_recons' : forall e x,
    length e = S x ->
    exists bs ls', peel_bs e = Some (bs, ls').
Proof.
  intros.
  destruct e;
    ff; eauto.
Defined.

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
      ltac:(eapply H with (r:=e'); (* TODO:  make r less one-off *)
            try (eapply peel_fact; eauto; tauto);
            try (econstructor; first [eapply firstn_long | eapply skipn_long]; try eauto; try lia))      
  end.


(**  * Event ID spans same for a term and its corresponding core term. *)
Lemma event_id_spans_same : forall t,
    event_id_span' t = event_id_span (copland_compile t).
Proof.
  intros.
  induction t; ff.
  -
    destruct a; ff; try tauto.
    +
      destruct s; ff.
  -
    jkjke'.
  -
    destruct s0; ff; lia.
  -
    destruct s0; ff; lia.
Qed.

(** * Lemma:  CVM increases event IDs according to event_id_span' denotation. *)
Lemma cvm_spans: forall t pt e tr p i e' tr' p' i',
    term_to_coreP t pt ->
    build_cvmP
      pt
      {| st_ev := e;
         st_trace := tr;
         st_pl := p;
         st_evid := i |}
      (Some tt)
      {|
        st_ev := e';
        st_trace := tr';
        st_pl := p';
        st_evid := i'
      |} ->
    i' = i + event_id_span' t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    wrap_ccp_anno.

  
 (*   (* This is more automated, but slower *)
    try (
        destruct a;
        try destruct a;
        ff; tauto);
    try (
        repeat find_apply_hyp_hyp;
        lia).
Defined.
  *)
   
  -
    destruct a;
      try destruct a;
      ff; try tauto.
    +
      wrap_ccp_anno; ff.
    +
      wrap_ccp_anno; ff.
    +
      destruct s.
      ++
        wrap_ccp_anno; ff.
      ++
        wrap_ccp_anno; ff.
    +
      wrap_ccp_anno; ff.
    +
      wrap_ccp_anno; ff.
    +
      wrap_ccp_anno; ff.
      
  
  -
    lia.
  -
    wrap_ccp_anno.
    assert (st_evid0 = i + event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (i' = st_evid0 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    lia.
  -
    destruct s0; destruct s1.
    +
      wrap_ccp_anno.

      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
    +
      wrap_ccp_anno.
      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
    +
      wrap_ccp_anno.
      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
    +
      wrap_ccp_anno.
      assert (st_evid1 = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (st_evid = st_evid1 + event_id_span' t2).
    eapply IHt2.
    2: { eassumption. }
    econstructor; eauto.
    subst.
    lia.
  - (* bpar case *)
    destruct s0; destruct s1.
    +
      wrap_ccp_anno.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    lia.
    +
      wrap_ccp_anno.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    lia.
    +
            wrap_ccp_anno.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    lia.
    +
      wrap_ccp_anno.

      assert (st_evid = (i + 1) +  event_id_span' t1).
    eapply IHt1.
    2: { eassumption. }
    econstructor; eauto.

    assert (event_id_span' t2 = event_id_span (copland_compile t2)).
    {
      eapply event_id_spans_same.
    }
    
    lia.
Qed.
  
(** * CVM event ID span same as annotated term range *)
Lemma span_cvm: forall atp t annt i j e e' tr tr' p p' i',
    build_cvmP
      atp
      {| st_ev := e;
         st_trace := tr;
         st_pl := p;
         st_evid := i |} 
      (Some tt)
      {| st_ev := e';
         st_trace := tr';
         st_pl := p';
         st_evid := i' |} ->
    
    term_to_coreP t atp -> 
    anno t i = (j, annt) ->
    j = i'.
Proof.
  intros.
  assert (j = i + event_id_span' t).
  {
    assert (j - i = event_id_span' t).
    {
      symmetry.
      eapply span_range.
      eauto.
    }
    rewrite <- H2.
    assert (j > i).
    {
      eapply anno_mono; eauto.
    }
    lia.
  }
  subst.
  symmetry.
  eapply cvm_spans; eauto.
Defined.

(** * Propositional version of span_cvm *)
Lemma anno_span_cvm: forall t pt annt i i' e e' p p' tr tr' st_evid1,
    annoP_indexed annt t i i' ->
    term_to_coreP t pt ->
    build_cvmP pt
                     {|
                       st_ev := e ;
                       st_trace := tr ;
                       st_pl := p;
                       st_evid := i
                     |} (Some tt)
                     {|
                       st_ev := e';
                       st_trace := tr';
                       st_pl := p';
                       st_evid := st_evid1
                     |} ->
    i' = st_evid1.
Proof.
  intros.
  invc H.
  eapply span_cvm; eauto.
Qed.

Axiom events_cvm_to_core_mt : forall t p e,
    cvm_events_core (lseqc (aspc CLEAR) t) p e = cvm_events_core t p mt.


(** * Theorem:  Main Theorem stating that for an arbitrary Copland phrase, all of its execution traces 
      in the CVM are also captured in the LTS reference semantics. *)
Theorem cvm_refines_lts_events :
  forall t atp annt cvm_tr bits bits' et et' p p' i i',
    term_to_coreP t atp ->
    annoP_indexed annt t i i' ->
    build_cvmP atp
                     (mk_st (evc bits et) [] p i)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr p' i') ->
    lstar (conf annt p et) cvm_tr (stop p (aeval annt p et)).
Proof.
  intros t atp annt cvm_tr bits bits' et et' p p' i i' annoParPH annPH H'.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    wrap_ccp_anno.

    
    destruct a; invc annoParPH; ff;
    wrap_ccp_anno;
    
    try (econstructor; econstructor; reflexivity).
    destruct f.
    +
      ff.
      ++
        wrap_ccp_anno.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         try (econstructor; econstructor; reflexivity).
    +
      ff.
      ++
        wrap_ccp_anno.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         try (econstructor; econstructor; reflexivity).
    +
      ff.
      ++
        wrap_ccp_anno.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         try (econstructor; econstructor; reflexivity).
    +
      ff.
       ++
        wrap_ccp_anno.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         try (econstructor; econstructor; reflexivity).
    +
      ff.
      ++
         wrap_ccp_anno.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         try (econstructor; econstructor; reflexivity).
      
      
      
    
  - (* aatt case *)
    wrap_ccp_anno.

    assert (n = i + event_id_span' t + 1) by lia.
    subst.
    clear H2.
   
    assert (t = unanno a) as H3.
    {
      invc Heqp0.
      
      erewrite <- anno_unanno at 1.
      rewrite H.
      tauto.
    }
     
    assert (lstar (conf a p et) (cvm_events t p et) (stop p (aeval a p et))).
    {
      eapply remote_LTS.
      eassumption.
    }
    
    rewrite H3.

    eapply lstar_tran.
    econstructor.
    (*econstructor. *)
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    rewrite <- H3.
    cbn.
    eassumption.

    simpl.
    assert (et' = (aeval a p et)).
    {
      rewrite <- eval_aeval'.
      erewrite <- remote_Evidence_Type_Axiom.
      rewrite <- H3.
      rewrite H0.
      tauto.
    }
    rewrite <- H3.
    rewrite <- H1.

    rewrite H0.
    simpl.

    assert (((i + 1 + event_id_span' t)) = Nat.pred (S (i + event_id_span' t + 1))) by lia.
    
    
    rewrite H2 at 1.
    
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
    
    assert (n = H1).
    {
      eapply anno_span_cvm.
      econstructor.
      invc Heqp0.
      eassumption.
      2: { apply H2. }
      econstructor; tauto.
    }
    subst.

    destruct x.
    
    econstructor.
    econstructor.
    eapply lstar_transitive.
    eapply lstar_stls.
    
    eapply IHt1.
    2: { eassumption. }
    2: { apply H2. }
    econstructor; tauto.

    (*
      eassumption.
    eassumption.
    econstructor; jkjke.
    eassumption. *)

    eapply lstar_silent_tran.
    apply stlseqstop.

    assert (e = aeval a p et).

     {
      rewrite <- eval_aeval'.
      assert (t1 = unanno a).
    {
      symmetry.
      invc Heqp0.
      erewrite <- anno_unanno.
      rewrite H5.
      tauto.
    }
    eapply cvm_refines_lts_evidence.
    econstructor; eauto.
    rewrite <- H5.
    eassumption.
     }

     assert (p = H0).
    {
      invc H2.
      do_pl_immut.
      congruence.
    }

    rewrite H5 in *; clear H5.
    rewrite H6 in *; clear H6.


    

    eapply IHt2. (*with (e:= x). *)

    2: { eassumption. }



    2: {
      eassumption.
    }
    econstructor; tauto.

  - (* abseq case *)

    wrap_ccp_anno;
    ff;
    wrap_ccp_anno.
    +

    assert (n = st_evid1).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      eapply span_cvm.
      eassumption.
      econstructor; tauto.
      invc Heqp0.
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
        lstar (conf a st_pl1 et) blah' (stop st_pl1 (aeval a st_pl1 et))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eassumption.
    }

    assert (
      lstar (conf a0 st_pl1  et) blah (stop st_pl1 (aeval a0 st_pl1  et))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
      eapply IHt2.
      econstructor; tauto.
      eassumption.
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
    rewrite H5 at 2.

    
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
      invc Heqp0.
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
        lstar (conf a st_pl1 et) blah' (stop st_pl1 (aeval a st_pl1 et))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eassumption.
    }

    assert (
      lstar (conf a0 st_pl1  mt) blah (stop st_pl1 (aeval a0 st_pl1  mt))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
      eapply IHt2.
      econstructor; tauto.
      eassumption.
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
    rewrite H5 at 2.

    
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
      invc Heqp0.
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
        lstar (conf a st_pl1 mt) blah' (stop st_pl1 (aeval a st_pl1 mt))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eassumption.
    }

    assert (
      lstar (conf a0 st_pl1  et) blah (stop st_pl1 (aeval a0 st_pl1  et))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
      eapply IHt2.
      econstructor; tauto.
      eassumption.
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
    rewrite H5 at 2.

    
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
      invc Heqp0.
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
        lstar (conf a st_pl1 mt) blah' (stop st_pl1 (aeval a st_pl1 mt))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eassumption.
    }

    assert (
      lstar (conf a0 st_pl1  mt) blah (stop st_pl1 (aeval a0 st_pl1  mt))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
      eapply IHt2.
      econstructor; tauto.
      eassumption.
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
    rewrite H5 at 2.

    
    econstructor.

    eapply stbsrstop.
    econstructor.




    

  - (* abpar case *)

    wrap_ccp_anno;
    ff;
    wrap_ccp_anno.

    +

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H4.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a p et) blah (stop p (aeval a p et))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eassumption.

    }

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start 0 p (copland_compile t2) et]
                ++
                blah ++
                [cvm_thread_end 0] =
              shuffled_events blah (cvm_events_core  (copland_compile t2) p et)).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      jkjke.

      (*

      assert (
          (splitEv_T_r s et) =
          (get_et (splitEv_r s (evc bits et)))).
      {
        destruct s; destruct s; destruct s0; ff.
      }
      jkjke. *)
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      rewrite H3 at 2.

      eapply lstar_tran.

      

      apply stbpstop.
      econstructor.

    +

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H4.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a p et) blah (stop p (aeval a p et))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eassumption.

    }

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) et]
                ++
                blah ++
                [cvm_thread_end 0] =
              shuffled_events blah (cvm_events_core (lseqc (aspc CLEAR) (copland_compile t2)) p et)).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      rewrite H2.
   
      rewrite events_cvm_to_core_mt.
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      rewrite H3 at 2.

      eapply lstar_tran.

      

      apply stbpstop.
      econstructor.

    +

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H4.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a p mt) blah (stop p (aeval a p mt))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eassumption.

    }

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start 0 p ((copland_compile t2)) et]
                ++
                blah ++
                [cvm_thread_end 0] =
              shuffled_events blah (cvm_events_core (copland_compile t2) p et)).
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
      rewrite H3 at 2.

      eapply lstar_tran.

      

      apply stbpstop.
      econstructor.


          +

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H4.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a p mt) blah (stop p (aeval a p mt))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      eapply IHt1.
      econstructor; tauto.
      eassumption.
      eassumption.

    }

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) et]
                ++
                blah ++
                [cvm_thread_end 0] =
              shuffled_events blah (cvm_events_core (lseqc (aspc CLEAR) (copland_compile t2)) p et)).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      rewrite H2.
   
      rewrite events_cvm_to_core_mt.
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      rewrite H3 at 2.

      eapply lstar_tran.

      

      apply stbpstop.
      econstructor.
Qed.


(** * Slight reformulation of cvm_refines_events, in terms of st_trace. *)
Corollary cvm_refines_lts_event_ordering_corrolary :
  forall t annt atp cvm_tr bits et p i i',
    annoP_indexed annt t i i' ->
    term_to_coreP t atp ->
    st_trace (run_cvm atp
                      (mk_st (evc bits et) [] p i)) = cvm_tr ->
    lstar (conf annt p et) cvm_tr (stop p (aeval annt p et)).
Proof.
  intros.
  destruct (build_cvm atp {| st_ev := (evc bits et);
                                   st_trace := [];
                                   st_pl := p;
                                   st_evid := i |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  do_asome.
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
    eassumption.
  }
  subst.
  
  eapply cvm_refines_lts_events; eauto.
  econstructor; eauto.
Qed.


(** * Main correctness theorem about CVM events:  event orderings respect the 
      event system (partial order) reference semantics. *)
Theorem cvm_respects_event_system :
  forall atp annt t cvm_tr ev0 ev1 bits bits' et et' i i',
    annoP_indexed annt t i i' ->
    term_to_coreP t atp ->
    build_cvmP atp
                     (mk_st (evc bits et) [] 0 i)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr 0 i') ->
    prec (ev_sys annt 0 et) ev0 ev1 ->
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

Corollary cvm_respects_event_system_run :
  forall atp annt t cvm_tr ev0 ev1 bits et i i',
    annoP_indexed annt t i i' ->
    term_to_coreP t atp ->
    st_trace (run_cvm atp (mk_st (evc bits et) [] 0 i)) = cvm_tr ->
    
    prec (ev_sys annt 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  unfold run_cvm in *.
  ff.
  do_somett.
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

Corollary cvm_respects_event_system_run' : forall atp annt t cvm_tr ev0 ev1 bits et,
    annt = annotated t ->
    copland_compile t = atp ->
    st_trace (run_cvm atp (mk_st (evc bits et) [] 0 0)) = cvm_tr ->
    
    prec (ev_sys annt 0 et) ev0 ev1 ->
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
  

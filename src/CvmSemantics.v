(*
  Primary results/proofs about the Copland Virtual Machine implementation, 
    linking it to the Copland reference semantics.

  Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Defs Term_Defs Anno_Term_Defs ConcreteEvidence LTS Event_system Term_system Main Appraisal_Evidence AutoApp.
Require Import Term Cvm_Monad StructTactics Auto.
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
    et_size e0 = es.
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
*)


(** * Axiom:  assume parallel CVM threads preserve well-formedness of EvC bundles *)
Axiom wf_ec_preserved_par: forall e l t2 p,
    wf_ec e ->
    wf_ec (parallel_vm_thread l t2 p e).

(** * Lemma:  CVM execution preserves well-formedness of EvC bundles 
      (Evidence Type of sufficient length for raw evidence). *)
Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' p p' i i' ac ac',
    wf_ec e ->
        build_cvmP t1
                    {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |}
                    (resultC tt)
                    {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i'; st_AM_config := ac' |} ->
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
    repeat Auto.ff.
    unfold doRemote_session' in *; repeat Auto.ff.

    unfold do_remote in *; Auto.ff.

    eapply wf_ec_preserved_remote; eauto.

  -
    wrap_ccp.
    Auto.ff.
    eauto.
  -
    wrap_ccp.
    Auto.ff.

    (* do_wfec_split. *)

    find_apply_hyp_hyp.
    find_apply_hyp_hyp.
    econstructor.
    dd.
    inv_wfec.
    repeat jkjke'.
    eapply app_length.

  -
    wrap_ccp.
    Auto.ff.

    (* do_wfec_split. *)

    find_apply_hyp_hyp.

      inv_wfec;
      ff;
      econstructor;
      dd;
      repeat jkjke'.

    erewrite app_length.

    assert (wf_ec (evc r1 e1)).
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
                                   (resultC tt)
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
Lemma cvm_spans: forall t pt e tr p i e' tr' p' i' ac ac',
    term_to_coreP t pt ->
    build_cvmP
      pt
      {| st_ev := e;
         st_trace := tr;
         st_pl := p;
         st_evid := i;
         st_AM_config := ac |}
      (resultC tt)
      {|
        st_ev := e';
        st_trace := tr';
        st_pl := p';
        st_evid := i';
        st_AM_config := ac'
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
      Auto.ff; try tauto.
    +
      wrap_ccp_anno; ff.
    +
      wrap_ccp_anno; ff.
    +
      destruct s.
      ++
        wrap_ccp_anno; repeat Auto.ff.
      ++
        wrap_ccp_anno; repeat Auto.ff.
    +
      wrap_ccp_anno; repeat Auto.ff.
    +
      wrap_ccp_anno; repeat Auto.ff.
    +
      wrap_ccp_anno; repeat Auto.ff.
      
  
  -
    repeat Auto.ff.
    unfold doRemote_session' in *; repeat Auto.ff.
    lia.
  -
    wrap_ccp_anno.
    repeat Auto.ff.
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
      repeat Auto.ff.

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
      repeat Auto.ff.
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
      repeat Auto.ff.
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
      repeat Auto.ff.
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
      repeat Auto.ff.

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
      repeat Auto.ff.

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
      repeat Auto.ff.

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
      repeat Auto.ff.

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
Lemma span_cvm: forall atp t annt i j e e' tr tr' p p' i' ac ac',
    build_cvmP
      atp
      {| st_ev := e;
         st_trace := tr;
         st_pl := p;
         st_evid := i;
         st_AM_config := ac |} 
      (resultC tt)
      {| st_ev := e';
         st_trace := tr';
         st_pl := p';
         st_evid := i';
         st_AM_config := ac' |} ->
    
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
Lemma anno_span_cvm: forall t pt annt i i' e e' p p' tr tr' st_evid1 ac ac',
    annoP_indexed annt t i i' ->
    term_to_coreP t pt ->
    build_cvmP pt
                     {|
                       st_ev := e ;
                       st_trace := tr ;
                       st_pl := p;
                       st_evid := i;
                       st_AM_config := ac
                     |} (resultC tt)
                     {|
                       st_ev := e';
                       st_trace := tr';
                       st_pl := p';
                       st_evid := st_evid1; st_AM_config := ac'
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
  forall t atp annt cvm_tr bits bits' et et' p p' i i' ac ac',
    term_to_coreP t atp ->
    annoP_indexed annt t i i' ->
    build_cvmP atp
                     (mk_st (evc bits et) [] p i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') cvm_tr p' i' ac') ->
    lstar (conf annt p et) cvm_tr (stop p (aeval annt p et)).
Proof.
  intros t atp annt cvm_tr bits bits' et et' p p' i i' ac ac' annoParPH annPH H'.
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
        repeat Auto.ff.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         repeat Auto.ff.
         try (econstructor; econstructor; reflexivity).
    +
      ff.
      ++
        wrap_ccp_anno.
        repeat Auto.ff.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         repeat Auto.ff.
         try (econstructor; econstructor; reflexivity).
    +
      ff.
      ++
        wrap_ccp_anno.
        repeat Auto.ff.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         repeat Auto.ff.
         try (econstructor; econstructor; reflexivity).
    +
      ff.
       ++
        wrap_ccp_anno.
        repeat Auto.ff.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         repeat Auto.ff.
         try (econstructor; econstructor; reflexivity).
    +
      ff.
      ++
         wrap_ccp_anno.
         repeat Auto.ff.
        try (econstructor; econstructor; reflexivity).
      ++
         wrap_ccp_anno.
         repeat Auto.ff.
         try (econstructor; econstructor; reflexivity).
    +
         wrap_ccp_anno.
         repeat Auto.ff.
        try (econstructor; econstructor; reflexivity).
   +
    wrap_ccp_anno.
    repeat Auto.ff.
   try (econstructor; econstructor; reflexivity).
   +
   wrap_ccp_anno.
         repeat Auto.ff.
        try (econstructor; econstructor; reflexivity).
    
      
      
      
    
  - (* aatt case *)
    wrap_ccp_anno.
    unfold doRemote_session' in *;
    repeat ff.

    assert (n = i + event_id_span' t + 1) by lia.
    subst.
    (* clear H2. *)
   
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
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    rewrite <- H3.
    cbn.
    eassumption.

    simpl.
    assert (aeval a p et = eval (unanno a) p et).
    {
      rewrite <- eval_aeval'.
      tauto.
    }
    repeat find_rewrite.
    
    rewrite <- H3.
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
    
    assert (n = H1).
    {
      eapply anno_span_cvm.
      econstructor.
      invc Heqp0.
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

    assert (e = aeval a p et).

     {
      rewrite <- eval_aeval'.
      assert (t1 = unanno a).
    {
      symmetry.
      invc Heqp0.
      erewrite <- anno_unanno.
      rewrite H6.
      tauto.
    }
    eapply cvm_refines_lts_evidence.
    econstructor; eauto.
    rewrite <- H6.
    eassumption.
     }

     assert (p = H0).
    {
      invc H3.
      do_pl_immut.
      congruence.
    }
    subst.

    eapply IHt2; eauto. (*with (e:= x). *)

    econstructor; tauto.

  - (* abseq case *)

    wrap_ccp_anno;
    repeat Auto.ff;
    wrap_ccp_anno;
    repeat Auto.ff.
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
        lstar (conf a st_pl0 et) blah' (stop st_pl0 (aeval a st_pl0 et))
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
      lstar (conf a0 st_pl0  et) blah (stop st_pl0 (aeval a0 st_pl0  et))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
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
    rewrite H2 in *.

    
    econstructor; eauto; simpl in *.
    assert (Nat.pred (st_evid + 1) + 1 = st_evid + 1) by lia.
    rewrite H3 in *; eauto. 
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
        lstar (conf a st_pl0 et) blah' (stop st_pl0 (aeval a st_pl0 et))
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
      lstar (conf a0 st_pl0  mt) blah (stop st_pl0 (aeval a0 st_pl0 mt))
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
    rewrite H2 at 2.

    
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
        lstar (conf a st_pl0 mt) blah' (stop st_pl0 (aeval a st_pl0 mt))
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
      lstar (conf a0 st_pl0  et) blah (stop st_pl0 (aeval a0 st_pl0  et))
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
    rewrite H2 at 2.

    
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
        lstar (conf a st_pl0 mt) blah' (stop st_pl0 (aeval a st_pl0 mt))
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
      lstar (conf a0 st_pl0  mt) blah (stop st_pl0 (aeval a0 st_pl0  mt))
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
    rewrite H2 at 2.

    
    econstructor.

    eapply stbsrstop.
    econstructor.

  - (* abpar case *)

    wrap_ccp_anno;
    repeat Auto.ff;
    wrap_ccp_anno;
    repeat Auto.ff.

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
      eapply restl.
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
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      rewrite H2 at 2.

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
      eapply restl.
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
      rewrite H1.
   
      rewrite events_cvm_to_core_mt.
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      rewrite H2 at 2.

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
      eapply restl.
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
      rewrite H1.
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      rewrite H2 at 2.

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
      eapply restl.
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
      rewrite H1.
   
      rewrite events_cvm_to_core_mt.
      
      eapply lstar_transitive.

      unfold cvm_events in *.
      
      eapply bpar_shuffle.
      eassumption.
      eassumption.

      assert ((st_evid + event_id_span (copland_compile t2)) = Nat.pred ((st_evid + event_id_span (copland_compile t2)) + 1)) by lia.
      rewrite H2 at 2.

      eapply lstar_tran.

      

      apply stbpstop.
      econstructor.
Qed.



(** * Main correctness theorem about CVM events:  event orderings respect the 
      event system (partial order) reference semantics. *)
Theorem cvm_respects_event_system :
  forall atp annt t cvm_tr ev0 ev1 bits bits' et et' i i' plc_id ac ac',
    annoP_indexed annt t i i' ->
    term_to_coreP t atp ->
    build_cvmP atp
                     (mk_st (evc bits et) [] plc_id i ac)
                     (resultC tt)
                     (mk_st (evc bits' et') cvm_tr plc_id i' ac') ->
    prec (ev_sys annt plc_id et) ev0 ev1 ->
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
build_cvmP (copland_compile t1)
    {|
      st_ev := evc [] mt;
      st_trace := [Term_Defs.split cvmi p; cvm_thread_start 0 p ct e];
      st_pl := p;
      st_evid := S cvmi;
      st_AM_config := ac
    |} (resultC tt)
    {|
      st_ev := evc r0 e0;
      st_trace :=
        Term_Defs.split cvmi p :: (cvm_thread_start 0 p ct e) :: blah;
      st_pl := p;
      st_evid := st_evid;
      st_AM_config := ac'
    |}
    =
    build_cvmP (copland_compile t1)
    {|
      st_ev := evc [] mt;
      st_trace := [Term_Defs.split cvmi p; cvm_thread_start 0 p ct e];
      st_pl := p;
      st_evid := S cvmi;
      st_AM_config := ac
    |} (resultC tt)
    {|
      st_ev := evc r0 e0;
      st_trace :=
        ([Term_Defs.split cvmi p; cvm_thread_start 0 p ct e] ++ blah);
      st_pl := p;
      st_evid := st_evid;
      st_AM_config := ac'
    |}.
Proof.
  ff.
  eauto.
Qed.

Axiom cvm_thread_start_clear : forall t p e n,
(cvm_thread_start n p (lseqc (aspc CLEAR) (copland_compile t)) e) = 
(cvm_thread_start n p (copland_compile t)) mt.

Axiom cvm_thread_in_ev : forall n p ev t e blah,
In ev ([cvm_thread_start n p (copland_compile t) e] ++ blah ++ [cvm_thread_end 0]) -> 
(In ev (cvm_events_core (copland_compile t) p e) \/ 
In ev blah).

Axiom cvm_evidence_exists_remote : forall t p e,
  exists b et, 
  cvm_evidence_core t p e = evc b et.


Lemma cvm_implies_events: forall t annt e e' bits bits' p p' cvmi cvmi' cvm_tr ev ac ac',
    annoP_indexed annt t cvmi cvmi'->

    build_cvmP (copland_compile t)
         {| st_ev := evc bits e; st_trace := []; st_pl := p; st_evid := cvmi; st_AM_config := ac |} 
         (resultC tt) {| st_ev := evc bits' e'; st_trace := cvm_tr; st_pl := p'; st_evid := cvmi'; st_AM_config := ac' |} ->

    In ev cvm_tr ->

    events annt p e ev.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* asp case *)
    wrap_ccp_anno;
    repeat Auto.ff;
    destruct a; invc H; repeat Auto.ff;
      wrap_ccp_anno;
      repeat Auto.ff;
      try destruct s; wrap_ccp_anno;
      try destruct f;
      try destruct H1;
      subst;
      try solve_by_inversion;
    
      try (econstructor; econstructor; reflexivity).
  -
    wrap_ccp_anno.
    ff.
    unfold Cvm_Monad.doRemote_session' in *;
    repeat Auto.ff.

    assert (n = cvmi + event_id_span' t + 1) by lia.
    subst.
    clear H6.
   
    assert (t = unanno a) as H11.
    {
      invc Heqp1.
      
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
               ev = (rpy (cvmi + 1 + event_id_span' t) p' p (eval t p e)
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
      
      door.

      assert (
              build_cvm (copland_compile t)
                    {| st_ev := (evc bits e);
                       st_trace := [];
                       st_pl := p;
                       st_evid := (S cvmi); st_AM_config := ac' |} =
    (resultC tt,
     {| st_ev := cvm_evidence_core (copland_compile t) p (evc bits e);
        st_trace := cvm_events_core (copland_compile t) p (get_et (evc bits e));
        st_pl := p;
        st_evid := ( (S cvmi) + event_id_span (copland_compile t));
        st_AM_config := ac'
     |})).
      apply build_cvm_external.

      destruct (cvm_evidence_core (copland_compile t) p (evc bits e)).
      unfold cvm_events in *.


      
      econstructor.

      eapply IHt; [ | simpl in *; econstructor; eauto | eauto ].
      2: {
        subst; rewrite eval_aeval'; apply evtsattrpy;
        simpl; lia.
      }
      econstructor.

      invc Heqp1.
      repeat ff.
      rewrite <- event_id_spans_same.
      simpl in *.
      assert (S (cvmi + event_id_span' (unanno a)) =
              cvmi + event_id_span' (unanno a) + 1) by lia.
      rewrite H4.
      eassumption.
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
    
    assert (n = H4).
    {
      eapply anno_span_cvm; eauto;
      econstructor; eauto.
    }
    subst.

    
    destruct x.
     

    assert (In ev H \/ In ev H7).
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
      apply evtslseql.
      eapply IHt1.
      econstructor.
      eassumption.
      eassumption.
      eassumption.
    +

      

    assert (e0 = aeval a p e).
      {
      rewrite <- eval_aeval'.
      assert (t1 = unanno a).
    {
      symmetry.
      invc Heqp1.
      erewrite <- anno_unanno.
      rewrite Heqp2.
      tauto.
    }
    eapply cvm_refines_lts_evidence.
    econstructor; eauto.
    rewrite <- H9.
    eassumption.
      }
      rewrite H9 in H8.
      

      assert (p = H3).
      {
        invc H6.
        do_pl_immut.
        congruence.
      }
      

      
      invc Heqp3.
      apply evtslseqr.
      eapply IHt2.
      econstructor.
      eassumption.
      eassumption.
      eassumption.
  - (* abseq case *)
    wrap_ccp_anno;
    repeat Auto.ff;
    wrap_ccp_anno;
    repeat Auto.ff.
    +

    assert (n = st_evid1).
    {
      assert (cvmi+1 = S cvmi) by lia.
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

    assert (ev = Term_Defs.split cvmi st_pl0 \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid st_pl0).
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
    assert (Term_Defs.split cvmi st_pl0 :: blah' = 
    [Term_Defs.split cvmi st_pl0] ++ blah'). 
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

    assert (ev = Term_Defs.split cvmi st_pl0 \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid st_pl0).
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
    assert (Term_Defs.split cvmi st_pl0 :: blah' = 
    [Term_Defs.split cvmi st_pl0] ++ blah'). 
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

    assert (ev = Term_Defs.split cvmi st_pl0 \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid st_pl0).
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
    assert (Term_Defs.split cvmi st_pl0 :: blah' = 
    [Term_Defs.split cvmi st_pl0] ++ blah'). 
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

    assert (ev = Term_Defs.split cvmi st_pl0 \/
            (In ev blah') \/
            (In ev blah) \/
            ev = join st_evid st_pl0).
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
    assert (Term_Defs.split cvmi st_pl0 :: blah' = 
    [Term_Defs.split cvmi st_pl0] ++ blah'). 
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
    Auto.ff;
    wrap_ccp_anno;
    Auto.ff.

    +

    assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply span_cvm; eauto.
      
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H6.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi p \/
            In ev ([cvm_thread_start 0 p (copland_compile t2) e] ++
                   blah ++ [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) p).
    {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi p;
            cvm_thread_start 0 p (copland_compile t2) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi p] ++ 
              ([(cvm_thread_start 0 p (copland_compile t2) e)] ++ blah ++
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

    assert (In ev [Term_Defs.split cvmi p] \/ 
            In ev (cvm_events_core (copland_compile t2) p e) \/ 
            In ev blah \/ 
            In ev [join (st_evid + event_id_span (copland_compile t2)) p]).
    {

    invc H1.
    left; eauto.
    auto with *.

    assert (In ev ([cvm_thread_start 0 p (copland_compile t2) e] ++ blah ++ [cvm_thread_end 0]) \/ 
            In ev [join (st_evid + event_id_span (copland_compile t2)) p]).
            {
              auto with *.
            }

            invc H1.

            assert (In ev (cvm_events_core (copland_compile t2) p e) \/ 
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

    invc H3; try solve_by_inversion.

    door.

    eapply evtsbparr.

    pose (build_cvm_external (copland_compile t2) (evc bits e) p st_evid ac).

    assert (exists b et, cvm_evidence_core (copland_compile t2) p (evc bits e) = 
    evc b et).
    {
      eapply cvm_evidence_exists_remote.
    }
    destruct_conjs.
    rewrite H6 in *.

    eapply IHt2.
    eassumption.
    simpl.
    econstructor.
    eassumption.
    apply H3.

    door.

    apply evtsbparl.
    eapply IHt1.

    eassumption.
    simpl.
    assert (S cvmi =  cvmi + 1) by lia.
    rewrite H4.
    eapply restl.
    eassumption.
    eassumption.

    invc H3; try solve_by_inversion.

    eapply evtsbparjoin.
    simpl.
    lia.

    eauto.

    (*

    eapply evtsbparsplit.
    simpl; eauto.
    solve_by_inversion.

    admit. (* TODO: axiom? *)
    eauto.

    *)


    subst.

    apply evtsbparjoin.
    simpl.
    lia.


    +
      assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H6.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.


    assert (ev = Term_Defs.split cvmi p \/
            In ev ([cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah ++
                   [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) p
           ).
    {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi p;
            cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi p] ++ 
              ([(cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e)] ++ blah ++
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


    assert (In ev [Term_Defs.split cvmi p] \/ 
    In ev (cvm_events_core (copland_compile t2) p mt) \/ 
    In ev blah \/ 
    In ev [join (st_evid + event_id_span (copland_compile t2)) p]).
{

invc H1.
left; eauto.
auto with *.



Unset Printing Notations.

assert (In ev ([cvm_thread_start 0 p (copland_compile t2) mt] ++ blah ++ [cvm_thread_end 0]) \/ 
        In ev [join (st_evid + event_id_span (copland_compile t2)) p]).
        {
          assert (
            (cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e) = 
            (cvm_thread_start 0 p (copland_compile t2)) mt).
            {
              eapply cvm_thread_start_clear.
            }
            rewrite H1 in *; clear H1.

            auto with *.

        }

        invc H1.

        assert (In ev (cvm_events_core (copland_compile t2) p mt) \/ 
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

invc H3; try solve_by_inversion.

door.

eapply evtsbparr.

pose (build_cvm_external (copland_compile t2) (evc bits mt) p st_evid ac).

assert (exists b et, cvm_evidence_core (copland_compile t2) p (evc bits mt) = 
evc b et).
{
  eapply cvm_evidence_exists_remote.
}
destruct_conjs.
rewrite H6 in *.

eapply IHt2.
eassumption.
econstructor.
simpl.
eassumption.

apply H3.


door.

apply evtsbparl.
eapply IHt1.

eassumption.
simpl.
assert (S cvmi =  cvmi + 1) by lia.
rewrite H4.
eapply restl.
eassumption.
eassumption.

invc H3; try solve_by_inversion.

eapply evtsbparjoin.
simpl.
lia.



eauto.

(*

eapply evtsbparsplit.
simpl; eauto.
solve_by_inversion.

admit. (* TODO: axiom? *)
eauto.

*)



    subst.

    apply evtsbparjoin.
    simpl.
    lia.

    +
      assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H6.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi p \/
            In ev ([cvm_thread_start 0 p (copland_compile t2) e] ++
                   blah ++ [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) p).
        {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi p;
            cvm_thread_start 0 p (copland_compile t2) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi p] ++ 
              ([(cvm_thread_start 0 p (copland_compile t2) e)] ++ blah ++
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




    assert (In ev [Term_Defs.split cvmi p] \/ 
    In ev (cvm_events_core (copland_compile t2) p e) \/ 
    In ev blah \/ 
    In ev [join (st_evid + event_id_span (copland_compile t2)) p]).
{

invc H1.
left; eauto.
auto with *.

assert (In ev ([cvm_thread_start 0 p (copland_compile t2) e] ++ blah ++ [cvm_thread_end 0]) \/ 
        In ev [join (st_evid + event_id_span (copland_compile t2)) p]).
        {
          auto with *.
        }

        invc H1.

        assert (In ev (cvm_events_core (copland_compile t2) p e) \/ 
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

invc H3; try solve_by_inversion.

door.

eapply evtsbparr.



pose (build_cvm_external (copland_compile t2) (evc bits e) p st_evid ac).

assert (exists b et, cvm_evidence_core (copland_compile t2) p (evc bits e) = 
evc b et).
{
  eapply cvm_evidence_exists_remote.
}
destruct_conjs.
rewrite H6 in *.



eapply IHt2.
eassumption.

simpl.
econstructor.
eassumption.

apply H3.


door.

apply evtsbparl.
eapply IHt1.

eassumption.
simpl.
assert (S cvmi =  cvmi + 1) by lia.
rewrite H4.
eapply restl.
eassumption.
eassumption.

invc H3; try solve_by_inversion.

eapply evtsbparjoin.
simpl.
lia.



eauto.

(*

eapply evtsbparsplit.
simpl; eauto.
solve_by_inversion.

admit. (* TODO: axiom? *)
eauto.

*)


    subst.

    apply evtsbparjoin.
    simpl.
    lia.

    +
      assert (n = st_evid).
    {
      assert (cvmi+1 = S cvmi) by lia.
      find_rewrite.
      invc Heqp0.
      
      eapply span_cvm; eauto.
      econstructor; tauto.
    }
    subst.

    assert (n0 = st_evid + event_id_span (copland_compile t2)) by lia.
    
    subst. clear H6.
    
    
    
    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (ev = Term_Defs.split cvmi p \/
            In ev ([cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah ++
                   [cvm_thread_end 0]) \/
            ev = join (st_evid + event_id_span (copland_compile t2)) p
           ).
        {
      apply in_app_or in H1.
      door.
      +
      assert(
           (([Term_Defs.split cvmi p;
            cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e] ++ blah) ++
                                                                  [cvm_thread_end 0]) =
            ([Term_Defs.split cvmi p] ++ 
              ([(cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e)] ++ blah ++
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
      (cvm_thread_start 0 p (lseqc (aspc CLEAR) (copland_compile t2)) e) = 
      (cvm_thread_start 0 p (copland_compile t2)) mt).
      {
        eapply cvm_thread_start_clear.
      }
      rewrite H3 in *; clear H1.

    assert (
            In ev (cvm_events_core (copland_compile t2) p mt) \/ 
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
    rewrite <- H4 in *.


    eapply IHt1.
    eassumption.
    eapply restl.

    rewrite fufu in Heqp3.



(*
    ff.
    assert ((
      (Term_Defs.split cvmi p :: (cvm_thread_start 0 p <<core>{ (CLR -> (copland_compile t2)) }> e)) :: blah) = 
            [Term_Defs.split cvmi p :: (cvm_thread_start 0 p <<core>{ CLR -> (copland_compile t2) }> e)] ++ blah).
    eassumption.
    (* 
    assert ((Term_Defs.split cvmi p :: cvm_thread_start 0 p <<core>{ CLR -> (copland_compile t2) }> e :: blah) = 
    ([Term_Defs.split cvmi p :: cvm_thread_start 0 p <<core>{ CLR -> (copland_compile t2) }> e] ++ blah)).
    {
      intuition.
    }
    *)
    admit.

    *)
    eassumption.

    eassumption.

    }


    apply evtsbparr.



    pose (build_cvm_external (copland_compile t2) (evc bits mt) p st_evid ac).

assert (exists b et, cvm_evidence_core (copland_compile t2) p (evc bits mt) = 
evc b et).
{
  eapply cvm_evidence_exists_remote.
}
destruct_conjs.
rewrite H6 in *.





    simpl.

    eapply IHt2.
    eassumption.

    econstructor.
    eassumption.

    eauto.

    eauto.


    subst.

    apply evtsbparjoin.
    simpl.
    lia.
Qed.













































(*

NOTE:  this no longer holds with error results of CVM execution
TODO:  see if lemma can be generalized (i.e. to trace prefixes?)

(** * Slight reformulation of cvm_refines_events, in terms of st_trace. *)
Corollary cvm_refines_lts_event_ordering_corrolary :
  forall t annt atp cvm_tr bits et p i i' ac,
    annoP_indexed annt t i i' ->
    term_to_coreP t atp ->
    st_trace (run_cvm atp
                      (mk_st (evc bits et) [] p i ac)) = cvm_tr ->
    lstar (conf annt p et) cvm_tr (stop p (aeval annt p et)).
Proof.
  intros.
  destruct (build_cvm atp {| st_ev := (evc bits et);
                                   st_trace := [];
                                   st_pl := p;
                                   st_evid := i; st_AM_config := ac |}) eqn:hi.
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
    annoP_indexed annt t i i' ->
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
  

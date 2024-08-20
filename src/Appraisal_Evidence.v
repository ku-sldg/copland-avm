(* Definitions, properties, and associated automation related to 
    Appraisal and EvidenceT examination/reconstruction.

    Also included:  properties about CVM internal EvidenceT and Event handling.  
    TODO:  This file has become quite bloated.  May need to refactor/decompose.  *)

Require Import AutoApp Defs StructTactics OptMonad_Coq Cvm_Impl Cvm_St ResultT Axioms_Io Attestation_Session Helpers_CvmSemantics Cvm_Monad More_lists Auto Term_Defs.

Require Import List.
Import ListNotations OptNotation.

Require Import Lia Coq.Program.Tactics.

Lemma firstn_long: forall (e:list BS) x,
  length e >= x ->
  length (firstn x e) = x.
Proof.
  intros.
  eapply firstn_length_le.
  lia.
Qed.

Lemma skipn_long: forall (e:list BS) x y,
  length e = x + y ->
  length (skipn x e) = y.
Proof.
  intros.
  assert (length (skipn x e) = length e - x).
  { eapply skipn_length. }
  lia.
Qed.

Lemma peel_n_rawev_result_spec : forall n ls ls1 ls2 st st',
  (peel_n_rawev n ls) st = (resultC (ls1, ls2), st') ->
  ls = ls1 ++ ls2 /\ length ls1 = n.
Proof.
  induction n; intuition; repeat ff; subst;
  err_monad_unfold; ffa.
Qed.

Lemma peel_n_none_spec : forall n ls e st st',
  (peel_n_rawev n ls) st = (errC e, st') ->
  length ls < n.
Proof.
  induction n; intuition; repeat ff;
  err_monad_unfold; ffa; try lia.
Qed.

Lemma peel_n_rawev_state_immut : forall n r st res st',
  peel_n_rawev n r st = (res, st') ->
  st = st'.
Proof.
  induction n; simpl in *; intros; cvm_monad_unfold; ff.
Qed.

Lemma split_evidence_state_immut : forall r et1 et2 res st st',
  split_evidence r et1 et2 st = (res, st') ->
  st = st'.
Proof.
  intros.
  unfold split_evidence in *; cvm_monad_unfold; ff;
  repeat find_eapply_lem_hyp peel_n_rawev_state_immut; ff.
Qed.

Lemma invoke_APPR_spans : forall G et u c i st,
  invoke_APPR et st = (resultC u, c) ->
  appr_events_size G et = resultC i ->
  st_evid c = st_evid st + i.
Proof.
  induction et; simpl in *; intuition; cvm_monad_unfold;
  ff; result_monad_unfold; ff.
  eapply IHet1 in Heqp0; simpl in *; eauto;
  eapply IHet2 in Heqp1; simpl in *; eauto;
  repeat find_rewrite;
  find_eapply_lem_hyp split_evidence_state_immut; ff; lia.
Qed.

Require Import Maps.

Inductive et_same_asps : EvidenceT -> EvidenceT -> Prop :=
| et_same_asps_refl : forall e, et_same_asps e e
| et_same_asps_symm : forall e1 e2, et_same_asps e1 e2 -> et_same_asps e2 e1
| et_same_asps_mt : et_same_asps mt_evt mt_evt
| et_same_asps_nonce : forall n1 n2, et_same_asps (nonce_evt n1) (nonce_evt n2)
| et_same_asps_asp : forall p1 p2 args1 args2 targ_plc1 targ_plc2 targ1 targ2 e1 e2 asp_id,
    et_same_asps e1 e2 ->
    et_same_asps 
      (asp_evt p1 (asp_paramsC asp_id args1 targ_plc1 targ1) e1)
      (asp_evt p2 (asp_paramsC asp_id args2 targ_plc2 targ2) e2)
| et_same_asps_split : forall e1a e1b e2a e2b,
    et_same_asps e1a e2a ->
    et_same_asps e1b e2b ->
    et_same_asps (split_evt e1a e1b) (split_evt e2a e2b).

Lemma et_same_asps_impl_same_size : forall G e1 e2,
  et_same_asps e1 e2 ->
  et_size G e1 = et_size G e2.
Proof.
  intros.
  induction H; simpl in *; ffa using result_monad_unfold.
Qed.
Local Hint Resolve et_same_asps_impl_same_size : core.

Lemma et_same_asps_appr_procedure : forall G e1 e1' e2 e2' p1 p2,
  et_same_asps e1 e2 ->
  appr_procedure G p1 e1 = resultC e1' ->
  appr_procedure G p2 e2 = resultC e2' ->
  et_same_asps e1' e2'.
Proof.
  intros.
  generalizeEverythingElse H.
  induction H; simpl in *; intuition; repeat find_injection; eauto;
  try (econstructor; fail).
  - generalizeEverythingElse e;
    induction e; intros; simpl in *; ff; try (econstructor; fail);
    try (repeat eapply et_same_asps_asp; try econstructor; eauto);
    result_monad_unfold; ff;
    repeat match goal with
    | H1 : appr_procedure _ _ ?e1 = resultC ?e1',
      H2 : appr_procedure _ _ ?e2 = resultC ?e2',
      IH : context[appr_procedure _ _ ?e1 = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; 
      clear H2; eauto
    end; eapply et_same_asps_split; eauto.
  - eapply et_same_asps_symm; ffa.
  - eapply et_same_asps_asp; eapply et_same_asps_nonce.
  - ff; eapply et_same_asps_asp; eapply et_same_asps_asp; eauto. 
  - result_monad_unfold; ff;
    repeat match goal with
    | H1 : appr_procedure _ _ ?e1 = resultC ?e1',
      H2 : appr_procedure _ _ ?e2 = resultC ?e2',
      IH : context[appr_procedure _ _ ?e1 = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; 
      clear H2; eauto
    end; eapply et_same_asps_split; eauto.
Qed.
Local Hint Resolve et_same_asps_appr_procedure : core.

Lemma et_same_asps_eval_same_asps : forall G t p1 p2 e1 e1' e2 e2',
  et_same_asps e1 e2 ->
  eval G p1 e1 t = resultC e1' ->
  eval G p2 e2 t = resultC e2' ->
  et_same_asps e1' e2'.
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a; simpl in *; ff; eauto;
    try (econstructor; fail);
    try (eapply et_same_asps_asp; eauto);
    try (destruct s; simpl in *; eauto; try econstructor; fail);
    eapply et_same_asps_appr_procedure; eauto.
  - result_monad_unfold; ffa.
  - result_monad_unfold; ffa;
    destruct s, s, s0; simpl in *;
    repeat match goal with
    | H1 : eval _ ?p1 ?e1 ?t = resultC ?e1',
      H2 : eval _ ?p2 ?e2 ?t = resultC ?e2',
      IH : context[eval _ _ _ ?t = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; 
      clear H2; eauto;
      try (eapply et_same_asps_symm; eauto; fail);
      try (eapply et_same_asps_refl; fail)
    end;
    eapply et_same_asps_split; econstructor; eauto.
  - result_monad_unfold; ffa;
    destruct s, s, s0; simpl in *;
    repeat match goal with
    | H1 : eval _ ?p1 ?e1 ?t = resultC ?e1',
      H2 : eval _ ?p2 ?e2 ?t = resultC ?e2',
      IH : context[eval _ _ _ ?t = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; 
      clear H2; eauto;
      try (eapply et_same_asps_symm; eauto; fail);
      try (eapply et_same_asps_refl; fail)
    end;
    eapply et_same_asps_split; econstructor; eauto.
Qed.
Local Hint Resolve et_same_asps_eval_same_asps : core.

Lemma appr_procedure_et_size_plc_irrel : forall G e1 e1' e2 e2' p1 p2,
  et_same_asps e1 e2 ->
  appr_procedure G p1 e1 = resultC e1' ->
  appr_procedure G p2 e2 = resultC e2' ->
  et_size G e1' = et_size G e2'.
Proof.
  eauto.
Qed.

Lemma eval_et_size_plc_irrel : forall G t p1 p2 e1 e1' e2 e2',
  et_same_asps e1 e2 ->
  eval G p1 e1 t = resultC e1' ->
  eval G p2 e2 t = resultC e2' ->
  et_size G e1' = et_size G e2'.
Proof.
  intros.
  eauto.
Qed.

Lemma et_same_asps_impl_appr_events_size_same : forall G e1 e2 n1 n2,
  et_same_asps e1 e2 ->
  appr_events_size G e1 = resultC n1 ->
  appr_events_size G e2 = resultC n2 ->
  n1 = n2.
Proof.
  intros.
  generalizeEverythingElse H.
  induction H; try (simpl in *; ff; fail); intros;
  simpl in *; result_monad_unfold; ff;
  repeat match goal with
  | H1 : appr_events_size _ ?e1 = _,
    H2 : appr_events_size _ ?e2 = _,
    IH : context[appr_events_size _ ?e1 = _ -> _] |- _ =>
    eapply IH in H1; try eapply H2;
    clear H2; eauto; subst
  end.
Qed.

Lemma events_size_eval_res_irrel : forall G t p1 p2 et e1 e2 n1 n2,
  eval G p1 et t = resultC e1 ->
  eval G p2 et t = resultC e2 ->
  events_size G p1 e1 t = resultC n1 ->
  events_size G p2 e2 t = resultC n2 ->
  n1 = n2.
Proof.
  intros.
  assert (et_same_asps e1 e2) by (
    assert (et_same_asps et et) by econstructor;
    eauto
  );
  clear H H0 et.
  generalizeEverythingElse t.
  induction t; simpl in *; intuition; ffa using result_monad_unfold.
  - eapply et_same_asps_impl_appr_events_size_same; eauto.
  - destruct s, s, s0; simpl in *; ffa using result_monad_unfold;
    repeat match goal with
    | H1 : events_size _ ?p1 ?e1 ?t1 = _,
      H2 : events_size _ ?p2 ?e2 ?t1 = _,
      IH : context[events_size _ _ _ ?t1 = _ -> _] |- _ =>
      eapply IH in H1; try (eapply H2);
      try (eapply et_same_asps_symm; eauto; fail);
      try (eapply et_same_asps_refl; eauto; fail);
      clear H2; subst; eauto
    end.
  - destruct s, s, s0; simpl in *; ffa using result_monad_unfold;
    repeat match goal with
    | H1 : events_size _ ?p1 ?e1 ?t1 = _,
      H2 : events_size _ ?p2 ?e2 ?t1 = _,
      IH : context[events_size _ _ _ ?t1 = _ -> _] |- _ =>
      eapply IH in H1; try (eapply H2);
      try (eapply et_same_asps_symm; eauto; fail);
      try (eapply et_same_asps_refl; eauto; fail);
      clear H2; subst; eauto
    end.
Qed.

Lemma events_size_plc_irrel : forall G t et p1 p2 n1 n2,
  events_size G p1 et t = resultC n1 ->
  events_size G p2 et t = resultC n2 ->
  n1 = n2.
Proof.
  induction t; simpl in *; intuition; ffa using result_monad_unfold;
  repeat match goal with
  | H1 : events_size _ _ _ ?t = _,
    H2 : events_size _ _ _ ?t = _,
    IH : context[events_size _ _ _ ?t] |- _ =>
    eapply IH in H1; [ | eapply H2 ]; 
    clear H2; eauto; subst
  end.
  - repeat match goal with
    | H1 : events_size _ _ _ ?t = _,
      H2 : events_size _ _ _ ?t = _,
      IH : context[events_size _ _ _ ?t] |- _ =>
      eapply IH in H1; [ | eapply H2 ]; 
      clear H2; eauto; subst
    end.
    admit.
  -  
    Search eval.

(* Axiom the_remote_axiom : forall sc q ev t rawEv st u st',
  do_remote sc q ev t = resultC rawEv ->
  build_cvm t st = (resultC u, st') /\ get_bits (st_ev st') = rawEv. *)

(* : forall plc_map p uuid sc my_plc e t resp_js ev req success st u st',
  map_get plc_map p = Some uuid ->
  req = (mkPRReq sc my_plc e t) ->
  make_JSON_Network_Request uuid (to_JSON req) = resultC resp_js ->
  from_JSON resp_js = resultC (mkPRResp success ev) ->
  build_cvm t st = (resultC u, st') /\ get_bits (st_ev st') = ev. *)

(** * Lemma:  CVM increases event IDs according to event_id_span' denotation. *)
Lemma cvm_spans: forall t st u st' sc i,
  st_config st = sc ->
  build_cvm t st = (resultC u, st') ->
  events_size (session_context sc) (session_plc sc) (get_et (st_ev st)) t = resultC i ->
  st_evid st' = st_evid st + i.
Proof.
  induction t; simpl in *; intuition.
  - cvm_monad_unfold; ff;
    find_eapply_lem_hyp invoke_APPR_spans; ff. 
  - cvm_monad_unfold; ff; result_monad_unfold; 
    ff. 
    find_eapply_lem_hyp the_remote_axiom; intuition.
    eapply IHt in H; eauto.
    unfold do_remote in *; ff; simpl in *.
    eapply the_remote_axiom in Heqo.
    find_eapply_lem_hyp the_remote_axiom; eauto; try lia.
    eapply the_remote_axiom in Heqr0.
    unfold do_remote in *; simpl in *.
    Search invoke_APPR.


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
Qed.
  *)
   
  - (* asp case *)
    destruct a;
      try destruct a;
      ffa; try tauto;
      try (wrap_ccp_anno; ff).
  
  - (* at case *)
    ffa using (cvm_monad_unfold; try lia).

  - (* lseq case *)
    wrap_ccp_anno.

    destruct r; ffa.
    destruct u; ffa.



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
      try destruct r; ff; 
      try destruct r3; ff;
      try destruct r0; ff;
      try destruct u; ff;
      try destruct u0; ff.


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
      try destruct r; ff; 
      try destruct r3; ff;
      try destruct r0; ff;
      try destruct u; ff;
      try destruct u0; ff.

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
      try destruct r; ff; 
      try destruct r3; ff;
      try destruct r0; ff;
      try destruct u; ff;
      try destruct u0; ff.

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
      try destruct r; ff; 
      try destruct r3; ff;
      try destruct r0; ff;
      try destruct u; ff;
      try destruct u0; ff.

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
      try destruct r; ff;
      try destruct r3; ff;
      try destruct u; ff;
      try destruct u0; ff.

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
      try destruct r; ff;
      try destruct r3; ff;
      try destruct u; ff;
      try destruct u0; ff.

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
      try destruct r; ff;
      try destruct r3; ff;
      try destruct u; ff;
      try destruct u0; ff.

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
      try destruct r; ff;
      try destruct r3; ff;
      try destruct u; ff;
      try destruct u0; ff.

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
                       st_evid := st_evid1;
                       st_config := ac'
                     |} ->
    i' = st_evid1.
Proof.
  intros.
  invc H.
  eapply span_cvm; eauto.
Qed.


Lemma wfec_firstn: forall e0 e1 e2,
    wf_ec (evc e0 e1) ->
    firstn (et_size e1) (e0 ++ e2) = e0.
Proof.
  intros.
  inv_wfec.
  jkjke'.
  eapply firstn_append.
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


(** * Axiom:  assume parallel CVM threads preserve well-formednesplit_evt of Evidence bundles *)
Axiom wf_ec_preserved_par: forall e l t2 p,
    wf_ec e ->
    wf_ec (parallel_vm_thread l t2 p e).

Axiom wf_ec_preserved_remote: forall t ev1,
    wf_ec ev1 -> 
    forall p rawEv ac,
      do_remote t p ev1 ac = resultC rawEv ->
      wf_ec (evc rawEv (eval t p (get_et ev1))).

(** * Lemma:  CVM execution preserves well-formednesplit_evt of Evidence bundles 
      (EvidenceT Type of sufficient length for raw EvidenceT). *)
Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' i i' ac ac' res,
    wf_ec e ->
    build_cvmP t1
                {| st_ev := e; st_trace := tr; st_evid := i;
                    st_config := ac |}
                (res)
                {| st_ev := e'; st_trace := tr'; st_evid := i';
                    st_config := ac' |} ->
    wf_ec (e').
Proof.
  intros.
  generalizeEverythingElse t1.
  induction t1; intros.
  - (* asp case *)
    rewrite <- ccp_iff_cc in *;
    simpl in *; cvm_monad_unfold; simpl in *.
    ff; try (econstructor; simpl in *; eauto; fail).
    econstructor.
    rewrite app_length;
    rewrite EqClass.nat_eqb_eq in *; subst;
    ff.
    
  - (* at case *)
    invc H0; repeat cvm_monad_unfold; ffa;
    eapply wf_ec_preserved_remote; eauto.
  - (* lseq case *)
    wrap_ccp.
    ff; eauto.
  - (* bseq case *)
    wrap_ccp; ffa.
    inv_wfec; econstructor;
    rewrite app_length; ffa.

  - (* bpar case *)
    wrap_ccp; ffa; cbn; ffa.
    assert (wf_ec (evc r0 e1)).
    {
      rewrite <- Heqe1.
      eapply wf_ec_preserved_par; ffa.
    }
    econstructor; inv_wfec; 
    rewrite app_length; ffa.
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
                          ltac:(eapply wf_ec_preserved_by_cvm; [(*apply H |*) apply H2 | apply H3])
                                 
    end.


Axiom ev_cvm_mtc: forall ct p e loc,
    parallel_vm_thread loc ct p mt_evc = parallel_vm_thread loc (lseqc (aspc CLEAR) ct) p e.


(** * Lemma:  EvidenceT Type denotation respects EvidenceT reference semantics  *)
Lemma cvm_ev_denote_evtype: forall annt p e,
    (*(exists n n', anno t n = (n',annt)) -> *)
    et_fun (cvm_EvidenceT_denote annt p e) = (aeval annt p (et_fun e)).
Proof.
  intros.
  generalizeEverythingElse annt.
  induction annt; intros.
  -
    dd.
    destruct a; simpl in *; eauto; repeat ff; subst; simpl in *;
    try rewrite do_asp_EXTD_nofail_length_spec; simpl in *; eauto;
    unfold spc_ev, sp_ev; repeat ff.
  -
    dd.
    eauto.
  -
    dd.
    assert (et_fun (cvm_EvidenceT_denote annt1 p e) = aeval annt1 p (et_fun e)) by eauto.
    repeat jkjke.
  - dd.
    jkjke.
    jkjke.
    destruct s; destruct s; destruct s0; eauto.
  - dd.
    jkjke.
    jkjke.
    destruct s; destruct s; destruct s0; eauto.
Qed.


(** * Lemma:  CVM execution always succeeds *)
Lemma exists_some_cc: forall t st,
    exists st' res,
      build_cvm t st = (res, st').
Proof.
  intros.
  destruct (build_cvm t st) eqn:ee.
  subst.
  eauto.
Qed.

Ltac do_exists_some_cc t st :=
    assert_new_proof_by
      (exists st' res, build_cvm t st = (res, st') )
      ltac:(eapply exists_some_cc);
    destruct_conjs.

(** * Helper Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. *)
Lemma st_trace_cumul'' : forall t m k e v_full v_suffix res i ac,
    build_cvmP t
      {| st_ev := e; st_trace := m ++ k; st_evid := i; st_config := ac |}
      (res) v_full ->
    
    build_cvmP t
      {| st_ev := e; st_trace := k; st_evid := i; st_config := ac |}
      res v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  induction t; intros.
  - (* asp case *)
    (* NOTE: This got really ugly, unfortunately it is quite complex *)
    wrap_ccp.
    match goal with
    | A : ASP_Core |- _ => destruct A
    end; simpl in *; eauto.
    * unfold nullEv in *; cvm_monad_unfold; ff; rewrite app_assoc; eauto.
    * ff. 
    * ff; rewrite app_assoc; eauto. 
    * simpl in *; 
      destruct (aspCb ac a (get_bits e)); simpl in *; eauto;
      repeat find_injection; try rewrite app_assoc; eauto;
      destruct e;
      repeat (match goal with
      | F : FWD |- _ => destruct f
      | R : ResultT _ _ |- _ => destruct R
      | R' : RawEv |- _ => destruct R'
      end; simpl in *; eauto;
        repeat find_injection;
        try rewrite app_assoc; eauto;
        try congruence);
      try (destruct r1; simpl in *; repeat find_injection; eauto;
        try congruence; rewrite app_assoc; eauto);
      try (destruct n; simpl in *; repeat find_injection; 
        try congruence; try rewrite app_assoc; eauto;
        destruct (Nat.eqb (length r1) n); simpl in *;
        repeat find_injection; eauto;
        try congruence; try rewrite app_assoc; eauto
        ).
  - (* at case *)
    invc H; invc H0;
    repeat cvm_monad_unfold; ffa using (try rewrite app_assoc; eauto).

  - (* alseq case *)
    repeat ff.
    wrap_ccp_dohi.
    ff.
    +
    repeat ff; eauto.
    ff. eauto.
    cumul_ih.
    dd.
    repeat do_st_trace.
    repeat find_rw_in_goal.
    eauto.
    +
    wrap_ccp_dohi.
    repeat ff; eauto.
    ff. eauto.
    assert (resultC tt = errC c). 
    {
      rewrite <- ccp_iff_cc in *.
      eapply cvm_errors_deterministic; eauto.
    }
    solve_by_inversion.
    +
    wrap_ccp_dohi.
    repeat ff; eauto.
    ff. eauto.
    assert (resultC tt = errC c). 
    {
      symmetry.
      rewrite <- ccp_iff_cc in *.
      eapply cvm_errors_deterministic.
      apply Heqp1.
      eassumption.
    }
    solve_by_inversion.

    +
    wrap_ccp_dohi.
    ff.

    cumul_ih.
    dd.
    repeat do_st_trace.
    repeat find_rw_in_goal.
    eauto.

  - (* bseq case *)
    wrap_ccp_dohi.
    ff.

    +
    repeat rewrite <- app_assoc in *.
    cumul_ih.
    dd.
    cumul_ih.
    dd.
    intuition.
    +
      assert (errC c0 = resultC u).
      {
        wrap_ccp_dohi; ff. 
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic.
        eapply Heqp5.
        eassumption.
      }
    solve_by_inversion.
    +
    assert (errC c = resultC u).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic; eauto.
      }
    solve_by_inversion.
    +
    assert (errC c0 = resultC u).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic;
        ffa.
      }
    solve_by_inversion.
    +
    repeat rewrite <- app_assoc in *.
    cumul_ih.
    dd.
    cumul_ih.
    dd.
    intuition.
    +
    assert (errC c = resultC u0).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic; eauto.
      }
    solve_by_inversion.
    +
    assert (errC c = resultC u).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic.
        eapply Heqp8. eauto.
      }
    solve_by_inversion.
    +
    assert (errC c = resultC tt).
      {
        wrap_ccp_dohi. ff.
        rewrite <- ccp_iff_cc in *.
        eapply cvm_errors_deterministic.
        eapply Heqp8. eauto.
      }
    solve_by_inversion.
    +
    repeat rewrite <- app_assoc in *.
    wrap_ccp_dohi.
    cumul_ih.
    dd.
    cumul_ih.
    dd.
    intuition.
    +
    repeat rewrite <- app_assoc in *.
    wrap_ccp_dohi.
    cumul_ih.
    dd.
    cumul_ih.
    dd.
    auto with *.

  - (* bpar base *)
  wrap_ccp_dohi.
  ff.

  +
  repeat rewrite <- app_assoc in *.
  cumul_ih.
  dd.
  cumul_ih.
  dd.
  intuition.
  +
  wrap_ccp_dohi.
  repeat rewrite <- app_assoc in *.
  cumul_ih.
  dd.
  cumul_ih.
  dd.
  auto with *.
Qed.

(** * Instance of st_trace_cumul'' where k=[] *)
Lemma st_trace_cumul' : forall t m e v_full v_suffix res i ac,
    build_cvmP t
      {| st_ev := e; st_trace := m; st_evid := i; st_config := ac |}
      (res) v_full ->
    
    build_cvmP t
      {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}
      res v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  intros.
  eapply st_trace_cumul''; eauto.
  repeat rewrite app_nil_r.
  eauto.
Qed.


(** * Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. 
      TODO:  rename to st_trace_cumul 
*) 
Lemma suffix_prop : forall t e e' tr tr' i i' ac ac' res,
    build_cvmP t
           {| st_ev := e;
              st_trace := tr;
              st_evid := i; st_config := ac |}
           (res)
           {|
             st_ev := e';
             st_trace := tr';
             st_evid := i'; st_config := ac' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.

  do_exists_some_cc t {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}.
  wrap_ccp.
  (*

  rewrite ccp_iff_cc in *. *)

  repeat do_st_trace_assumps.
  repeat find_rw_in_goal.
  eexists.

  erewrite st_trace_cumul''.
  3: {
    eassumption.
  }
  simpl.
  tauto.
  rewrite app_nil_r.
  ff.
  destruct H1; destruct res; ff.
  +
    assert (c = c0).
    {
      edestruct cvm_errors_deterministic; ffa.
      invc H2; ffa.
      invc H; ffa.
      simpl in *; ffa.
    }
    subst.
    eassumption.
  +
  assert (errC c = resultC tt).
  {
    wrap_ccp_dohi. ff.
    invc H2. invc H.
    edestruct cvm_errors_deterministic.
    apply H0.
    apply H1.
    ff.
  }
solve_by_inversion.
  +
  assert (errC c = resultC tt).
  {
    wrap_ccp_dohi. ff.
    invc H2. invc H.
    edestruct cvm_errors_deterministic.
    apply H0.
    apply H1.
    ff.
  }
solve_by_inversion.
  +
    wrap_ccp_dohi.
    eassumption.
Qed.

Ltac do_suffix name :=
  match goal with
  | [H': build_cvmP ?t
         {| st_ev := _; st_trace := ?tr; st_evid := _; st_config := _ |}
         (_)
         {| st_ev := _; st_trace := ?tr'; st_evid := _; st_config := _ |}
         (*H2: well_formed_r ?t*) |- _] =>
    fail_if_in_hyps_type (exists l, tr' = tr ++ l);
    assert (exists l, tr' = tr ++ l) as name by (eapply suffix_prop; [apply H'])
  end.

(** * Structural Lemma:   Decomposes the CVM trace for the lseq phrase into the appending of the two traces
      computed by its subterms, where each subterm starts from the empty trace.

      Useful for leveraging induction hypotheses in the lseq case of induction that require empty traces in the 
      initial CVM state. *)
Lemma alseq_decomp : forall t1' t2' e e'' tr i i'' ac ac'',
    build_cvmP
      (lseqc t1' t2')
      {| st_ev := e;
         st_trace := [];
         st_evid := i; st_config := ac |}
      (resultC tt)
      {| st_ev := e'';
         st_trace := tr;
         st_evid := i''; st_config := ac'' |} ->

    exists e' tr' i' ac',
      build_cvmP
        t1'
        {| st_ev := e;
           st_trace := [];
           st_evid := i; st_config := ac |}
        (resultC  tt)
        {| st_ev := e';
           st_trace := tr';
           st_evid := i'; st_config := ac' |} /\
      exists tr'',
        build_cvmP
          t2'
          {| st_ev := e';
             st_trace := [];
             st_evid := i'; st_config := ac' |}
          (resultC tt)
          {| st_ev := e'';
             st_trace := tr'';
             st_evid := i''; st_config := ac'' |} /\
        tr = tr' ++ tr''.     
Proof.
  intros.
  wrap_ccp_dohi.
  repeat ff.
  wrap_ccp_dohi.
  
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.

  split.
  - rewrite <- ccp_iff_cc in *.
    eassumption.
  -
    do_exists_some_cc t2' {| st_ev := st_ev0; st_trace := []; st_evid := st_evid0; st_config := st_config0 |}.
    vmsts.
    repeat ff.
    destruct H0; ff.
    +
    assert (errC c = resultC tt).
    {
      wrap_ccp_dohi. ff.
      rewrite <- ccp_iff_cc in *.
      eapply cvm_errors_deterministic; eauto.
    }
  solve_by_inversion.
    +
    ff.

    eexists.

    wrap_ccp_dohi.

    split.
    ++
      eassumption.
    ++
      repeat do_st_trace.
      repeat find_rw_in_goal.
      eapply st_trace_cumul'; 
        eassumption.
Qed.


(** Structural convenience lemma:  reconfigures CVM execution to use an empty initial trace *)
Lemma restl : forall t e e' x tr i i' ac ac' res,
    build_cvmP t
      {| st_ev := e; st_trace := x; st_evid := i; st_config := ac|}
      (res)
      {| st_ev := e'; st_trace := x ++ tr; st_evid := i'; st_config := ac' |} ->

    build_cvmP t
      {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}
      (res)
      {| st_ev := e'; st_trace := tr; st_evid := i'; st_config := ac' |}.
Proof.
  intros.

  do_exists_some_cc t  {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}.
  wrap_ccp_dohi.

  assert (res = H1).
  {
    wrap_ccp_dohi.
    eapply cvm_errors_deterministic.
    invc H.
    apply H0.
    invc H2.
    eassumption.
  }
  subst.

  assert (st_trace = tr).
  {
    do_st_trace.
    rewrite H0; clear H0.
    assert (tr = st_trace).
    {
      assert (Cvm_St.st_trace {| st_ev := st_ev; st_trace := x ++ tr; st_evid := st_evid; st_config := st_config|} =
              x ++ Cvm_St.st_trace {| st_ev := st_ev; st_trace := st_trace; st_evid := st_evid; st_config := st_config |}).
      {
        eapply st_trace_cumul'; eauto.
        wrap_ccp_dohi.
        eassumption.
      }
      simpl in *.
      eapply app_inv_head; eauto.
    }
    jkjke.
  }

  wrap_ccp_dohi.
  congruence.
Qed.

Ltac do_restl :=
  match goal with
  | [H: build_cvmP ?t
        {| st_ev := ?e; st_trace := ?tr; st_evid := ?i; st_config := ?ac |}
        ?res
        {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_evid := ?i'; st_config := ?ac' |}
        (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_by
      (build_cvmP t
        {| st_ev := e; st_trace := []; st_evid := i; st_config := ac|}
        ?res
        {| st_ev := e'; st_trace := x; st_evid := i'; st_config := ac' |})
      ltac:(eapply restl; [apply H])
  end.

(** * Lemma:  EvidenceT semantics same for annotated and un-annotated terms *)
Lemma eval_aeval': forall t1 p et,
    eval (unanno t1) p et = aeval t1 p et.
Proof.
  induction t1; intros;
    repeat ff;
    repeat jkjke.
Qed.

Axiom cvm_EvidenceT_correct_type : forall t p e e',
  cvm_EvidenceT t p e = e' -> 
  get_et e' = eval t p (get_et e).


(** * Lemma:  parallel CVM threads preserve the reference EvidenceT Type semantics (eval). *)
Lemma par_EvidenceT_r: forall l p bits bits' et et' t2,
    parallel_vm_thread l (copland_compile t2) p (evc bits et) = evc bits' et' ->
    et' = eval t2 p et.
Proof.
  intros.
  rewrite par_EvidenceT in H.
  assert (get_et (evc bits' et') = eval t2 p (get_et (evc bits et))).
  {
    eapply cvm_EvidenceT_correct_type; eauto.
  }
  ff.
Qed.
         
(** * Axiom about "simulated" parallel semantics of CVM execution:
      Executing a "CLEAR" before a term is the same as executing that term with mt_evtinitial EvidenceT.
      TODO:  can we use existing axioms to prove this? *)
Axiom par_EvidenceT_clear: forall l p bits et t2,
    parallel_vm_thread l (lseqc (aspc CLEAR) t2) p (evc bits et) =
    parallel_vm_thread l t2 p mt_evc.

Lemma doRemote_session'_sc_immut : forall t st st' res p ev,
    doRemote_session' t p ev st = (res, st') ->
    st_config st = st_config st'.
Proof.
  unfold doRemote_session'.
  intuition.
  cvm_monad_unfold.
  ff.
Qed.

Lemma build_cvm_sc_immut : forall t st st' res,
    build_cvm t st = (res, st') ->
    st_config st = st_config st'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using cvm_monad_unfold.
Qed.

Lemma build_cvmP_sc_immut : forall t st st' res,
    build_cvmP t st res st' ->
    st_config st = st_config st'.
Proof.
  setoid_rewrite <- ccp_iff_cc.
  eapply build_cvm_sc_immut.
Qed.

(** * Main Lemma:  CVM execution maintains the EvidenceT Type reference semantics (eval) for 
      its internal EvidenceT bundle. *)
Lemma cvm_refines_lts_EvidenceT' : forall t tr tr' bits bits' et et' i i' ac ac',
    build_cvmP (copland_compile t)
        (mk_st (evc bits et) tr i ac)
        (resultC tt)
        (mk_st (evc bits' et') tr' i' ac') ->
    et' = (Term_Defs.eval t (session_plc ac) et).
Proof.
  intuition.
  eapply build_cvmP_sc_immut in H as H'.
  simpl in *; subst.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.
    ffa.  
    destruct a; (try dd; eauto); ffa using cvm_monad_unfold.
      

  - (* at case *)
    rewrite <- ccp_iff_cc in *.
    dd.
    repeat ffa.

  - (* alseq case *)
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eapply restl.
    eassumption.
    fold copland_compile in *.
    destruct_conjs.
    repeat match goal with
    | x : Evidence |- _ =>
      destruct x
    | H : build_cvmP (copland_compile t1) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt1 in H as Ho;
      simpl in *; subst; clear H
    | H2 : build_cvmP (copland_compile t2) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H2 as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt2 in H2 as Ho;
      simpl in *; subst; clear H2
    end; eauto.
    
  - (* abseq case *)
    simpl in *; repeat ff; subst;
    wrap_ccp; cbn in *; repeat ff; cbn in *;
    repeat match goal with
    | x : Evidence |- _ =>
      destruct x
    | u : unit |- _ =>
      destruct u
    | H : build_cvmP (copland_compile t1) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt1 in H as Ho;
      simpl in *; subst; clear H
    | H2 : build_cvmP (copland_compile t2) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H2 as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt2 in H2 as Ho;
      simpl in *; subst; clear H2
    end; eauto.

   - (* abpar case *)

    destruct s; repeat ffa;
    wrap_ccp; cbn in *; repeat ff; cbn in *;
    repeat (ffa; match goal with
    | u : unit |- _ =>
      destruct u
    end).
    +
      assert (e0 = eval t2 (session_plc ac') et).
      {
        eapply par_EvidenceT_r; eauto.
      }
      ffa.
      
    +
      find_apply_hyp_hyp.

      assert (e0 = eval t2 (session_plc ac') mt_evt).
      {
        rewrite par_EvidenceT_clear in *.
        eapply par_EvidenceT_r; eauto.
      }
      congruence.
    +
      wrap_ccp.
      ffa.
      assert (e0 = eval t2 (session_plc ac') et).
      {
        eapply par_EvidenceT_r; eauto.
      }
      congruence.
    +
      wrap_ccp.
      ffa.
      assert (e0 = eval t2 (session_plc ac') mt_evt).
      {
        rewrite par_EvidenceT_clear in *.

        eapply par_EvidenceT_r; eauto.
      }
      congruence.
Qed.

(** * Propositional version of CVM EvidenceT Type preservation. *)
Lemma cvm_refines_lts_EvidenceT :
  forall t t' tr tr' bits bits' et et' i i' ac ac',
    term_to_coreP t t' ->
    build_cvmP t'
      (mk_st (evc bits et) tr i ac)
      (resultC tt)
      (mk_st (evc bits' et') tr' i' ac') ->
    et' = (Term_Defs.eval t (session_plc ac) et).
Proof.
  intros.
  invc H.
  eapply cvm_refines_lts_EvidenceT'.
  eauto.
Qed.


(** BEGIN Deprecated parallel annotated term stuff *)

(*
Lemma anno_parP_redo: forall t pt loc loc',
    anno_par_list' t loc = Some (loc', pt) ->
    anno_parP pt t.
Proof.
  intros.
  econstructor.
  eexists.
  jkjke.
Qed.

(*
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par t loc = (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Qed.
 *)
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par_list' t loc = Some (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Qed.

 *)

(*

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac do_annopar_loc_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parPloc_redo in H
  end.
 *)


(*

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par_list' ?t ?loc = Some (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac do_annopar_loc_redo :=
  match goal with
  | [H: anno_par_list' ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parPloc_redo in H
  end.



Ltac inv_annoparP :=
  match goal with
  | [H: anno_parP _ _ (* ?t (?c _) *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Ltac inv_annoparPloc :=
  match goal with
  | [H: anno_parPloc _ _ _(*?t (?c _) _ *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.
 *)


(*
Ltac wrap_annopar :=
  inv_annoparP;
  dd;
  repeat do_annopar_redo.

Ltac wrap_annoparloc :=
  inv_annoparPloc;
  dd;
  repeat do_annopar_loc_redo.
 *)


(** END Deprecated parallel annotated term stuff *)

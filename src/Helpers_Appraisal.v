Require Import ConcreteEvidence Appraisal_Defs StVM Impl_vm Impl_appraisal Auto AutoApp External_Facts MonadVM Helpers_VmSemantics Appraisal_Evidence VmSemantics.

Require Import Axioms_Io.

Require Import Coq.Program.Tactics Lia.

Require Import OptMonad.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.


Ltac evsub_ih :=
  match goal with
  | [H: EvSub _ ?e,
        IH: context[EvSub _ ?e -> _] |- _] =>
    edestruct IH; [eauto | eauto ]
  end.

Ltac do_ggsub :=
  unfold gg_sub in *;
  destruct_conjs;
  subst.

Lemma uuc_app: forall e' e'' params p n,
    EvSub (uuc params p n e'') e' ->
    exists e'', EvSub (uuc params p (checkASPF params n) e'')
                 (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff;
    try evSubFacts; eauto;
      try evsub_ih.
Defined.

Lemma hhc_app: forall e' p bs et,
    EvSub (hhc p bs et) e' ->
    EvSub (hhc p (fromSome default_bs (checkHash et p bs)) et)
          (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff;
    try evSubFacts;
    eauto.
Defined.

Ltac find_wfec :=
  repeat 
    match goal with
    | [H: context [(*well_formed_r ?t*)_ -> _],
          (*H2: well_formed_r ?t, *)
              H3: wf_ec ?e,
                  H4: copland_compileP ?t
                                       {| st_ev := ?e; st_trace := _; st_pl := _ |}
                                       (_)
                                       {| st_ev := ?e'; st_trace := _; st_pl := _ |}
       |- _ ] => 
      assert_new_proof_by
        (wf_ec e')
        
        ltac:(eapply H; [(*apply H2 |*) apply H3 | apply H4])
    end.

Lemma wfec_split: forall e s,
    wf_ec e ->
    wf_ec (splitEv_l s e) /\ wf_ec (splitEv_r s e).
Proof.
  intros.
  split;
    destruct s; ff; try unfold mt_evc; ff;
      econstructor; ff.
Defined.

Ltac do_wfec_split :=
  match goal with
  | [H: context[splitEv_l ?s ?e],
        H2: context[splitEv_r ?s ?e],
            H3: wf_ec ?e
     |- _] =>
    
    assert_new_proof_by
      (wf_ec (splitEv_l s e) /\ wf_ec (splitEv_r s e))
      ltac: (eapply wfec_split; apply H3)
  end; destruct_conjs.

Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' p p' i i',
    (*well_formed_r t1 -> *)
    wf_ec e ->
        copland_compileP t1
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
  -
    wrap_ccp.

    eapply wf_ec_preserved_remote; eauto.

  -
    wrap_ccp.
    eauto.
  -
    wrap_ccp.

    do_wfec_split.

    find_apply_hyp_hyp.
    find_apply_hyp_hyp.
    econstructor.
    dd.
    inv_wfec.
    repeat jkjke'.
    eapply app_length.

  -
    wrap_ccp.
    
    do_wfec_split.

    find_apply_hyp_hyp.

      inv_wfec;
      ff;
      econstructor;
      dd;
      repeat jkjke'.

    erewrite app_length.

    assert (wf_ec (evc r0 e1)).
    {
      rewrite par_evidence in Heqe1.
      rewrite <- at_evidence in Heqe1.
      rewrite <- Heqe1.
      eapply wf_ec_preserved_remote.
      econstructor.
      eassumption.
    }

    solve_by_inversion.
Defined.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [(*H: well_formed_r ?t, *)
          H2: wf_ec ?stev,
              H3: copland_compileP ?t
                                   {| st_ev := ?stev; st_trace := _; st_pl := _; st_evid := _ |}
                                   (Some tt)
                                   {| st_ev := ?stev'; st_trace := _; st_pl := _; st_evid := _ |}
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [(*apply H |*) apply H2 | apply H3])
                                 
    end.



Ltac do_evsub_ih :=
  match goal with
  | [H: copland_compileP ?t1
                         {| st_ev := _; st_trace := _; st_pl := _; st_evid := _ |}
                         (Some tt)
                         {| st_ev := ?stev; st_trace := _; st_pl := _; st_evid := _ |},
            H3: reconstruct_evP ?stev ?v

     |- context[EvSub ?e'' _ \/ _]] =>
    
    assert_new_proof_by
      (EvSub e'' v \/
       (exists (ett : Evidence) p'0 bs,
           EvSub (hhc p'0 bs ett) v /\ EvSubT (et_fun e'') ett))
      eauto
  end.

Ltac do_evsubh_ih :=
  match goal with
  | [H: EvSub (hhc ?H2 ?H3 ?H4) _

     |- context[EvSub _ ?e' \/ _]] =>
    
    assert_new_proof_by
      (EvSub (hhc H2 H3 H4) e' \/
       (exists (ett : Evidence) p'0 bs,
           EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun (hhc H2 H3 H4)) ett))
      eauto
  end.

Ltac do_hh_sub :=
  match goal with
  | [H: context[(hh ?H2 ?H3)]

     |- context[EvSubT ?e'' _]] =>
    
    assert_new_proof_by
      (EvSubT e'' (hh H2 H3))
      ltac: (eapply evsubT_transitive; eauto)
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

Lemma not_none_alseq_pieces: forall t1 t2,
    not_none_none (lseq t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_none_abseq_pieces: forall s t1 t2,
    not_none_none (bseq s t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_none_abpar_pieces: forall s t1 t2,
    not_none_none (bpar s t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_none_aatt_pieces: forall q t1,
    not_none_none (att q t1) ->
    not_none_none t1.
Proof.
  intros;
    unfold not_none_none in *;
    unfold not in *.
  eauto.
Defined.

Lemma not_hshsig_alseq_pieces: forall t1 t2,
    not_hash_sig_term (lseq t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  intros;
    unfold not_hash_sig_term in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_hshsig_abseq_pieces: forall s t1 t2,
    not_hash_sig_term (bseq s t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  intros;
    unfold not_hash_sig_term in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_hshsig_abpar_pieces: forall s t1 t2,
    not_hash_sig_term (bpar s t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  intros;
    unfold not_hash_sig_term in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_hshsig_aatt_pieces: forall q t1,
    not_hash_sig_term (att q t1) ->
    not_hash_sig_term t1.
Proof.
  intros;
    unfold not_hash_sig_term in *;
    unfold not in *.
  eauto.
Defined.

Ltac do_not_none_alseq_pieces :=
  match goal with
  | [H: not_none_none (lseq ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_alseq_pieces; apply H)
  end.

Ltac do_not_none_abseq_pieces :=
  match goal with
  | [H: not_none_none (bseq _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_abseq_pieces; apply H)
  end.

Ltac do_not_none_abpar_pieces :=
  match goal with
  | [H: not_none_none (bpar _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_abpar_pieces; apply H)
  end.

Ltac do_not_none_aatt_pieces :=
  match goal with
  | [H: not_none_none (att _ ?t1)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1)
      ltac:(eapply not_none_aatt_pieces; apply H)
  end.

Ltac do_not_none :=
  try do_not_none_aatt_pieces;
  try do_not_none_alseq_pieces;
  try do_not_none_abseq_pieces;
  try do_not_none_abpar_pieces;
  destruct_conjs.

Ltac do_not_hshsig_alseq_pieces :=
  match goal with
  | [H: not_hash_sig_term (lseq ?t1 ?t2)
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_alseq_pieces; apply H)
  end.

Ltac do_not_hshsig_abseq_pieces :=
  match goal with
  | [H: not_hash_sig_term (bseq _ ?t1 ?t2)
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_abseq_pieces; apply H)
  end.

Ltac do_not_hshsig_abpar_pieces :=
  match goal with
  | [H: not_hash_sig_term (bpar _ ?t1 ?t2)
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_abpar_pieces; apply H)
  end.

Ltac do_not_hshsig_aatt_pieces :=
  match goal with
  | [H: not_hash_sig_term (att _ ?t1)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1)
      ltac:(eapply not_hshsig_aatt_pieces; apply H)
  end.

Ltac do_not_hshsig :=
  try do_not_hshsig_aatt_pieces;
  try do_not_hshsig_alseq_pieces;
  try do_not_hshsig_abseq_pieces;
  try do_not_hshsig_abpar_pieces;
  destruct_conjs.

Lemma not_none_none_contra_bseq: forall t1 t2 (P:Prop),
    not_none_none (bseq (NONE, NONE) t1 t2) ->
    P.
Proof.
  intros.
  cbv in H.
  exfalso.
  eapply H.
  left.
  repeat eexists.
  eauto.
Defined.

Lemma not_none_none_contra_bpar: forall t1 t2 (P:Prop),
    not_none_none (bpar (NONE, NONE) t1 t2) ->
    P.
Proof.
  intros.
  cbv in H.
  exfalso.
  eapply H.
  right.
  repeat eexists.
  eauto.
Defined.

Ltac do_none_none_contra_bseq :=
  match goal with
  | [H: not_none_none (bseq (NONE,NONE) _ _)

     |- _] =>
    (eapply not_none_none_contra_bseq; apply H)
  end.

Ltac do_none_none_contra_bpar :=
  match goal with
  | [H: not_none_none (bpar (NONE,NONE) _ _)

     |- _] =>
    (eapply not_none_none_contra_bpar; apply H)
  end.

Ltac do_none_none_contra :=
  try do_none_none_contra_bseq;
  try do_none_none_contra_bpar.

Lemma evsubt_preserved_eval: forall t et ett p,
    not_none_none t ->
    EvSubT ett et ->
    EvSubT ett (eval t p et).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ff;
  try (destruct a; ff; eauto; tauto); (* aasp case *)
    do_not_none;
    try eauto; (* aatt, alseq cases *)
    try (destruct s; destruct s; destruct s0; ff;
         do_none_none_contra). (* abseq, abpar cases  *)
Defined.

Lemma evsubt_preserved: forall t pt e e' et et' tr tr' p p' ett i i',
    (*well_formed_r_annt t -> *)
    not_none_none t ->
    anno_parP pt t 0 ->
    (*annoP annt t 0 -> *)
    copland_compileP pt
                     {| st_ev := evc e et; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := evc e' et'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
    EvSubT ett et ->
    EvSubT ett et'.
Proof.
  intros.

  (*
  destruct (anno_par t 0) eqn:hi.
  
  assert (t = (unannoPar pt)).
  {
    inversion H1.
    erewrite anno_unanno_par.
    reflexivity.
    rewrite hi in *.
    simpl in H4.
    subst.
    tauto.3
  }
   *)
  

  assert (et' = eval t p et).
  {
    (*
    rewrite H4. *)
    eapply cvm_refines_lts_evidence; eauto.
  }
  subst.


  (*
  assert (unannoPar pt = unanno annt).
  {
    destruct (anno_par t 0) eqn: hi.
    invc H0.
    invc H1.
    rewrite anno_unanno.
    erewrite anno_unanno_par.
    reflexivity.

    rewrite hi.
    simpl.
    reflexivity.
  }
  rewrite H4.
   *)

    eapply evsubt_preserved_eval; eauto.
Defined.

Lemma not_ev: forall t e,
    not_hash_sig_term_ev t e ->
    not_hash_sig_ev e.
Proof.
  intros; cbv in *.
  destruct_conjs.
  eauto.
Defined.

Lemma etfun_exists: forall y,
    exists y', y = et_fun y'.
Proof.
  intros.
  induction y; intros.
  -
    exists mtc.
    eauto.
  -
    destruct_conjs.
    exists (uuc a n default_bs IHy).
    ff.
  -
    destruct_conjs.
    exists (ggc n default_bs IHy).
    ff.
  -
    destruct_conjs.
    exists (hhc n default_bs y).
    ff.
  -
    exists (nnc n default_bs).
    ff.
  -
    destruct_conjs.
    exists (ssc IHy1 IHy2).
    ff.
  -
    destruct_conjs.
    exists (ppc IHy1 IHy2).
    ff.
Defined.

Lemma not_hshsig_uuc: forall e' params p x,
    not_hash_sig_ev e' ->
    not_hash_sig_ev (uuc params p x e').
Proof.
  cbv in *; intros.
  evSubFacts;
    try (destruct_conjs; solve_by_inversion);
    eauto.
Defined.

Lemma not_hshsig_ggc: forall e' n bs,
    not_hash_sig_ev e' ->
    not_hash_sig_ev (ggc n bs e').
Proof.
    cbv in *; intros.
  evSubFacts;
    try (destruct_conjs; solve_by_inversion);
    eauto.
Defined.

Lemma gg_recons: forall e ecc x y,
    reconstruct_evP ecc e ->
    not_hash_sig_ev e ->
    EvSubT (gg x y) (get_et ecc) ->
    gg_sub e.
Proof.
  intros e ecc x y H H0 H1.
  generalizeEverythingElse e.
  induction e; intros;
    destruct ecc; ff;
    do_inv_recon;
      try solve_by_inversion;
      do_nhse;
      do_recon_inv.
      
  - (* uuc case *)
    evSubTFacts.
    assert (gg_sub e) by eauto.
    do_ggsub. 
    repeat eexists.
    eauto.
    
  - (* ggc case *)
    econstructor.
    repeat eexists.
    eauto.
    
  - (* ssc case *)
    evSubTFacts.
    +
      assert (gg_sub e1) by eauto.
      do_ggsub.
      repeat eexists.
      eauto.
    +
      assert (gg_sub e2) by eauto.
      do_ggsub.
      repeat eexists.
      eauto.

  - (* ppc case *)
    evSubTFacts.
    +
      assert (gg_sub e1) by eauto.    
      do_ggsub.
      repeat eexists.
      eauto.
    +
      assert (gg_sub e2) by eauto.
      do_ggsub.
      repeat eexists.
      eauto.
Defined.

Lemma annopar_fst_snd: forall t l,
    anno_par t l = (fst (anno_par t l), snd (anno_par t l)).
Proof.
  intros.
  destruct (anno_par t l).
  simpl.
  tauto.
Defined.

Ltac do_t_at_zero t x :=
  let y := fresh in
  assert (exists l' t', anno_par t 0 = (l',t')) as y by
        (destruct (anno_par t 0); repeat eexists);
  destruct y;
  destruct y as [x].

Ltac do_assert_remote t e p i :=
  assert (
      copland_compile t
                      {| st_ev := e; st_trace := []; st_pl := p; st_evid := i|} =
      (Some tt,
       {| st_ev := doRemote_session (unannoPar t) p e;
                   st_trace := cvm_events (unannoPar t) p (get_et e);
                               st_pl := p; st_evid :=  (i + event_id_span (unannoPar t))
       |})
    ) by
    (eapply copland_compile_at(*;
     eapply wfr_annt_implies_wfr_par;
     [eassumption | econstructor; jkjke]*)).

Ltac do_assert_unannoPar t x :=
  assert (t = unannoPar x) by
    (erewrite anno_unanno_par;
     [reflexivity | eassumption]).

Ltac do_assume_remote t e p i x :=
  do_t_at_zero t x;
  do_assert_remote x e p i;
  do_assert_unannoPar t x.

Lemma wfec_encodeEv_etfun:
  forall e,
    wf_ec (evc (encodeEv e) (et_fun e)).
Proof.
Admitted.

Lemma recon_same: forall e,
    Some e = reconstruct_ev (evc (encodeEv e) (et_fun e)).
Proof.
  intros.
  induction e; intros;
    try (dd; tauto).
  -
    dd.
    rewrite <- IHe.
    tauto.
  -
    dd.
    rewrite <- IHe.
    tauto.
  -
    dd.
    assert (wf_ec (evc (encodeEv e1) (et_fun e1))).
    {
      eapply wfec_encodeEv_etfun.
      }
    assert ((firstn (et_size (et_fun e1)) (encodeEv e1 ++ encodeEv e2)) =
            encodeEv e1).
    {

      eapply wfec_firstn.
      eassumption.
    }
    assert ((skipn (et_size (et_fun e1)) (encodeEv e1 ++ encodeEv e2)) =
            encodeEv e2).
    {

      eapply wfec_skipn.
      eassumption.
    }
    rewrite H0; clear H0.
    rewrite H1; clear H1.
    
    
    
    rewrite <- IHe1.
    rewrite <- IHe2.
    tauto.
  -
    dd.
    assert (wf_ec (evc (encodeEv e1) (et_fun e1))).
    {
      eapply wfec_encodeEv_etfun.
    }
    assert ((firstn (et_size (et_fun e1)) (encodeEv e1 ++ encodeEv e2)) =
            encodeEv e1).
    {
     eapply wfec_firstn.
     eassumption.
    }
    assert ((skipn (et_size (et_fun e1)) (encodeEv e1 ++ encodeEv e2)) =
            encodeEv e2).
    {
      eapply wfec_skipn.
      eassumption.
    }
    rewrite H0; clear H0.
    rewrite H1; clear H1.
    
    
    
    rewrite <- IHe1.
    rewrite <- IHe2.
    tauto.
Defined.

Lemma recon_evdenote_decomp: forall a p e,
    (*reconstruct_evP ecc'
                    (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)) ->
     *)
    
    exists ecc,
      reconstruct_evP ecc (cvm_evidence_denote a p e).
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    exists (evc (encodeEv (cvm_evidence_denote (aasp r a) p e)) (et_fun (cvm_evidence_denote (aasp r a) p e))).
    econstructor.
    eapply recon_same.
  -
    edestruct IHa.
    invc H.
    exists x.
    econstructor.
    dd.
    eassumption.
  -
    dd.
    edestruct IHa1 with (p:=p) (e:=e).
    edestruct IHa2 with (p:=p) (e:= (cvm_evidence_denote a1 p e)).
    eexists.
    eassumption.
  -
    dd.
    edestruct IHa1 with (p:=p) (e:= (splitEvl s e)).
    edestruct IHa2 with (p:=p) (e:= (splitEvr s e)).
    eexists.
    econstructor.
    eapply recon_same.
  -
    dd.
    edestruct IHa1 with (p:=p) (e:= (splitEvl s e)).
    edestruct IHa2 with (p:=p) (e:= (splitEvr s e)).
    eexists.
    econstructor.
    eapply recon_same.
Defined.
      
        

(*
  intros.
  generalizeEverythingElse a.
  (*
  generalize dependent H.
  generalize dependent ecc'.
  generalize dependent a0.
  generalize dependent p.
  generalize dependent e. 
  induction (cvm_evidence_denote a p e) eqn: hi; intros.
   *)
  induction a; intros.
  -
    destruct a; dd.


    
    exists mt_evc.
    econstructor. tauto.
  -
    exists (evc [b] (nn n)).
    econstructor. tauto.
  -
    assert (exists ecc, reconstruct_evP ecc 
    edestruct IHe0.
 *)  
      
Lemma recon_evP_ssc_decomp: forall ecc' a p e e' a0,
    reconstruct_evP ecc'
                    (ssc (cvm_evidence_denote a p e)
                         (cvm_evidence_denote a0 p e')) ->
    (exists ecc, reconstruct_evP ecc (cvm_evidence_denote a p e)) /\
    (exists ecc, reconstruct_evP ecc (cvm_evidence_denote a0 p e')).
Proof.
  intros.
  destruct ecc'; try solve_by_inversion.
  do_inv_recon_ss.
  invc H.
  dd.
  ff.
  rewrite fold_recev in *.
  split.
  eexists.
  econstructor.
  symmetry.
  eassumption.
  eexists.
  econstructor.
  symmetry.
  eassumption.
Defined.

Lemma recon_evP_ppc_decomp: forall ecc' a p e e' a0,
    reconstruct_evP ecc'
                    (ppc (cvm_evidence_denote a p e)
                         (cvm_evidence_denote a0 p e')) ->
    (exists ecc, reconstruct_evP ecc (cvm_evidence_denote a p e)) /\
    (exists ecc, reconstruct_evP ecc (cvm_evidence_denote a0 p e')).
Proof.
    intros.
  destruct ecc'; try solve_by_inversion.
  do_inv_recon_pp.
  invc H.
  dd.
  ff.
  rewrite fold_recev in *.
  split.
  eexists.
  econstructor.
  symmetry.
  eassumption.
  eexists.
  econstructor.
  symmetry.
  eassumption.
Defined.

(*
Lemma evsub_cvm_denote: forall e'' p e a0,
    EvSub e'' e ->
    EvSub e'' (cvm_evidence_denote a0 p e).
Proof.
  intros.
  generalizeEverythingElse a0.
  induction a0; intros.
  -
    destruct a.
    +
      dd.
      eassumption.
    +
      dd.
      econstructor.
      eauto.
    +
      dd.
      econstructor.
      eauto.
    +
      dd.
      (*
      econstructor. *)
Admitted.
*)

Lemma reconp_wfec: forall ecc e,
    reconstruct_evP ecc e ->
    wf_ec ecc.
Proof.
Admitted.

Lemma evAccum: forall t annt p (e e' e'':EvidenceC) (*tr tr' p'*) (* (ecc ecc':EvC) *) (*loc*) i (*i'*),

    (*anno_parP pt t loc -> *)
    annoP annt t i -> 
    (*well_formed_r pt -> *)
    not_none_none t ->
    (*wf_ec ecc ->

    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' -> *)

    cvm_evidence_denote annt p e = e' ->
    
    EvSub e'' e ->
    (*
    copland_compileP (pt)
                     {| st_ev := ecc; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
*)

    (
      (EvSub e'' e') \/
      (exists ett p' bs,
          EvSub (hhc p' bs ett) e' /\
          EvSubT (et_fun e'') ett
      )
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    dd.
    invc H.
    dd.
    destruct a; dd; eauto.
    right.
    repeat eexists.
    econstructor.
    Search et_fun.
    eapply evsub_etfun.
    eassumption.
  - (* aatt case *)
    dd.
    invc H.
    dd.
    do_not_none.
    edestruct IHt.
    econstructor.
    jkjke.
    eassumption.
    dd. reflexivity.
    eassumption.
    eauto.
    eauto.
  - (* alseq case *)
    dd.
    invc H.
    dd.
    repeat do_anno_redo.

    do_not_none.

    Check recon_evdenote_decomp.



    edestruct recon_evdenote_decomp with (a:=a) (p:=p) (e:=e).
    destruct x.




    Ltac do_evsub_ih'' :=
  match goal with
  | [(*H: copland_compileP ?t1
                         {| st_ev := _; st_trace := _; st_pl := _; st_evid := _ |}
                         (Some tt)
                         {| st_ev := ?stev; st_trace := _; st_pl := _; st_evid := _ |}, *)
            H3: reconstruct_evP ?stev ?v

            |- context[EvSub ?e'' _ \/ _]] =>

     assert
      (EvSub e'' v \/
       (exists (ett : Evidence) p'0 bs,
           EvSub (hhc p'0 bs ett) v /\ EvSubT (et_fun e'') ett))
      (*
    
    assert_new_proof_by
      (EvSub e'' v \/
       (exists (ett : Evidence) p'0 bs,
           EvSub (hhc p'0 bs ett) v /\ EvSubT (et_fun e'') ett))
      eauto *)
  end.


    (*
    do_evsub_ih. (* IHt1 *)
    
    door.
    +
      eapply IHt2 with (ecc:=st_ev0);
        eassumption.
    +
      do_evsubh_ih. (* IHt2 *)
      
      door.
      ++
        right.
        repeat (eexists; eauto).
      ++
        
        right.
        repeat (eexists; eauto).
        simpl in *.
        do_hh_sub.
        eapply evsubT_transitive; eauto.
     *)
    
    do_evsub_ih''. (* IHt1 *)
    (*
     assert
      (EvSub e'' (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)) \/
       (exists (ett : Evidence) p'0 bs,
           EvSub (hhc p'0 bs ett) (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)) /\ EvSubT (et_fun e'') ett)). *)
      
    {
      eapply IHt1; eauto.

      (*
    eassumption.
    eassumption.
    reflexivity.
    eassumption.
    4: { reflexivity. }
    3: { eassumption. }
    2: { eassumption. }
    eassumption.
    eassumption. *)
    }
    
    door.

    ++

      eapply IHt2; eauto.
      (*
    eassumption.
    eassumption.
    
    4: { reflexivity. }
    3: { eassumption. }
    2: { eassumption. }
    eapply reconp_wfec; eauto.
    eassumption. *)

    ++
          
     assert
      (EvSub (hhc H5 H6 H4) (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)) \/
       (exists (ett : Evidence) p'0 bs,
           EvSub (hhc p'0 bs ett) (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)) /\ EvSubT (et_fun (hhc H5 H6 H4)) ett)).
     {
       eapply IHt2.
       eassumption.
       eassumption.
       reflexivity.
       eassumption.

       (*
       4: { reflexivity. }
       3: { eassumption. }
       2: { eassumption. }
       eapply reconp_wfec; eauto.
       eassumption. *)
     }

     door.
      +++
        right.
        repeat (eexists; eauto).
      +++
        
        right.
        repeat (eexists; eauto).
        simpl in *.
        do_hh_sub.
        eapply evsubT_transitive; eauto.
        
  - (* abseq case *)
    dd.
    invc H.
    dd.
    repeat do_anno_redo.

    do_not_none.



    (*
      edestruct recon_evP_ssc_decomp.
      eassumption.
      destruct_conjs.
     *)
    


    destruct s; destruct s; destruct s0;
      dd.

    +
    

    edestruct IHt1.
    eassumption.
    eassumption.
    reflexivity.
    eauto.
    eauto.

    (*
    4: { reflexivity. }
    3: { eassumption. }
    2: {
      eassumption. }
    eassumption.
    eassumption.
    eauto. *)
    destruct_conjs.
    right.
    repeat eexists; eauto.

    +
      edestruct IHt1.
      eassumption.
      eassumption.
      reflexivity.
      eauto.
      eauto.
      (*
    4: { reflexivity. }
    3: { eassumption. }
    2: {
      eassumption. }
    eassumption.
    eassumption.
    eauto. *)
    destruct_conjs.
    right.
    repeat eexists; eauto.
    +
      edestruct IHt2.
    eassumption.
    eassumption.
    reflexivity.
    eauto.
    eauto.
    (*
    4: { reflexivity. }
    3: { eassumption. }
    2: { eassumption. }
    eassumption.
    eassumption.
    eauto. *)
    destruct_conjs.
    right.
    repeat eexists; eauto.
    +
      do_none_none_contra.
  - (* abpar case *)

        dd.
    invc H.
    dd.
    repeat do_anno_redo.

    do_not_none.



    (*
      edestruct recon_evP_ppc_decomp.
      eassumption.
     
    

      (*

    

    assert (exists ecc,
               reconstruct_evP ecc (cvm_evidence_denote a p (splitEvl s e))).
    {
      admit.
    }
    destruct_conjs.

    assert (exists ecc,
               reconstruct_evP ecc (cvm_evidence_denote a0 p (splitEvr s e))).
    {
      admit.
    }
    destruct_conjs.
       *)



      destruct_conjs.

     *)
    


    destruct s; destruct s; destruct s0;
      dd.

    +
    

    edestruct IHt1.
    eassumption.
    eassumption.
    reflexivity.
    eauto.
    eauto.
    (*
    4: { reflexivity. }
    3: { eassumption. }
    2: {
      eassumption. }
    eassumption.
    eassumption.
    eauto. *)
    destruct_conjs.
    right.
    repeat eexists; eauto.

    +
      edestruct IHt1.
      eassumption.
      eassumption.
      reflexivity.
      eauto.
      eauto.
      (*
    4: { reflexivity. }
    3: { eassumption. }
    2: {
      eassumption. }
    eassumption.
    eassumption.
    eauto.  *)
    destruct_conjs.
    right.
    repeat eexists; eauto.
    +
      edestruct IHt2; eauto.
      (*
    eassumption.
    eassumption.
    reflexivity.
    4: { reflexivity. }
    3: { eassumption. }
    2: { eassumption. }
    eassumption.
    eassumption.
    eauto. *)
    destruct_conjs.
    right.
    repeat eexists; eauto.
    +
      do_none_none_contra.
Defined.



(*
Lemma evAccum: forall t annt pt p (e e' e'':EvidenceC)  (ecc ecc':EvC) loc,

    anno_parP pt t loc ->
    (*annoP annt t i ->  *)
    (*well_formed_r pt -> *)
    not_none_none t ->
    wf_ec ecc ->

    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' ->
    
    EvSub e'' e ->
    cvm_evidence_denote annt p e = e' ->
    (*
    copland_compileP (pt)
                     {| st_ev := ecc; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
     *)
    

    (
      (EvSub e'' e') \/
      (exists ett p' bs,
          EvSub (hhc p' bs ett) e' /\
          EvSubT (et_fun e'') ett
      )
    ).
Proof.
  intros.
  assert (exists annt, annoP annt t 0).
  {
    destruct (anno t 0) eqn: hi.
    eexists.
    econstructor.
    rewrite hi.
    tauto.
  }
  destruct_conjs.
  
  destruct ecc; destruct ecc'.
  eapply evAccum'; eauto.
  assert (annt = H6).
  {
    inversion H7.
    inversion H.
    subst.
    invc H7.
    invc H.
    admit.
  }
  
  eapply cvm_raw_evidence_denote_fact; eauto.
Defined.
*)



  

(*
Lemma evAccum: forall t pt p (e e' e'':EvidenceC) tr tr' p' (ecc ecc':EvC) loc i i',

    anno_parP pt t loc ->
    (*annoP annt t i -> *)
    (*well_formed_r pt -> *)
    not_none_none t ->
    wf_ec ecc ->

    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' ->
    
    EvSub e'' e ->
    copland_compileP (pt)
                     {| st_ev := ecc; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->

    (
      (EvSub e'' e') \/
      (exists ett p' bs,
          EvSub (hhc p' bs ett) e' /\
          EvSubT (et_fun e'') ett
      )
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    invc H.
    rewrite <- ccp_iff_cc in *.
    destruct a;
      repeat ff;
      try unfold cons_uu in *;
      try unfold cons_gg in *;
      try unfold cons_hh in *;
      (repeat ff; try eauto).
    +
      do_reconP_determ.
      eauto.
    +
      destruct ecc;
        ff.
      do_rewrap_reconP.
      do_reconP_determ.
      eauto.
    +
      destruct ecc;
        ff.
      do_rewrap_reconP.
      do_reconP_determ.
      eauto.
    +
      destruct ecc; ff.
      do_rewrap_reconP.

      assert (e0 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.
      right.
      repeat eexists.
      econstructor.
      apply evsub_etfun; eauto.
      
      
  - (* aatt case *)

    wrap_ccp.
    do_not_none.

    do_assume_remote t ecc n loc HHH.
    
    eapply IHt.

    7: {
      econstructor.
      eassumption.   
    }
    (*
    econstructor. rewrite H8. tauto.
    eapply wfr_annt_implies_wfr_par.
    eassumption. *)
    do_annopar_redo. eassumption.
    
    eassumption.
    eassumption.
    eassumption.
    rewrite <- H8.
    eassumption.
    eassumption.

  - (* alseq case *)

    wrap_ccp.
    
    do_wfec_preserved.

    do_somerecons.

    do_not_none.

    do_reconP_determ.

    do_evsub_ih. (* IHt1 *)
    
    door.
    +
      eapply IHt2 with (ecc:=st_ev0);
        eassumption.
    +
      do_evsubh_ih. (* IHt2 *)
      
      door.
      ++
        right.
        repeat (eexists; eauto).
      ++
        
        right.
        repeat (eexists; eauto).
        simpl in *.
        do_hh_sub.
        eapply evsubT_transitive; eauto.
        
  - (* abseq case *)

    wrap_ccp.

    do_rewrap_reconP.
    
    do_wfec_split.
    
    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.
    
    clear_skipn_firstn.

    do_somerecons.

    do_not_none.

    do_reconP_determ.
    
    destruct s; destruct s; destruct s0.
    +
      do_evsub_ih.

      door;
        [destruct_conjs;
         left; eauto | right; repeat eexists; eauto].
    +  
      do_evsub_ih.

      door;
        [destruct_conjs;
         left; eauto | right; repeat eexists; eauto].
    +
      do_evsub_ih.

      door;
        [destruct_conjs;
         left; eauto | right; repeat eexists; eauto].
    +
      do_none_none_contra.


  - (* NEW abpar case *)

    wrap_ccp.

    do_rewrap_reconP.
    
    do_wfec_split.
    
    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.
    
    clear_skipn_firstn.

    do_somerecons.

    do_not_none.

    do_reconP_determ.

    destruct s; destruct s; destruct s0.
    +
      do_evsub_ih.

      door;
        [destruct_conjs;
         left; eauto | right; repeat eexists; eauto].
    +
      do_evsub_ih.

      door;
        [destruct_conjs;
         left; eauto | right; repeat eexists; eauto].
    +
      do_assume_remote t2 ecc p loc HHH.

      edestruct IHt2.
      7: {
        econstructor.
        eassumption. }

      econstructor. rewrite H11. tauto.

      (*
      
      eapply wfr_annt_implies_wfr_par.
      eassumption.
      econstructor. rewrite H14. tauto.
       *)
      
     
      eassumption.
      eassumption.
     
      eassumption.

      rewrite <- Heqe1 in *.
      rewrite par_evidence in *.
      rewrite at_evidence in *.
      rewrite <- H17.
      dd.
      eassumption.
      do_reconP_determ.
      eassumption.

      eauto.
      destruct_conjs.
      right; repeat (eexists; eauto).

    +
      do_none_none_contra.
Defined.
 *)

Check evAccum.
(*
evAccum
evAccum
     : forall (t : Term) (annt : AnnoTerm) (p : nat) 
         (e e' e'' : EvidenceC) (i : nat),
       annoP annt t i ->
       not_none_none t ->
       cvm_evidence_denote annt p e = e' ->
       EvSub e'' e ->
       EvSub e'' e' \/
       (exists (ett : Evidence) (p' : nat) (bs : BS),
          EvSub (hhc p' bs ett) e' /\ EvSubT (et_fun e'') ett)
 *)


Ltac do_evaccum :=
  repeat 
    match goal with
    | [ (*H: well_formed_r ?pt, *)
      (*
           H2: wf_ec ?ecc,
               H3: reconstruct_evP ?ecc ?e,
                   H4: reconstruct_evP ?ecc' ?e', *)
                       H5: EvSub ?e'' ?e,
                           H6: cvm_evidence_denote ?annt _ ?e = ?e',
                               H7: not_none_none ?t,
                                   H8: annoP ?annt ?t _

        |- _] =>
      
      assert_new_proof_by
        (EvSub e'' e' \/
         (exists (ett : Evidence) p'0 bs,
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett))
        ltac: (eapply evAccum; [apply H8 (*| apply H *) | apply H7 (*| apply H2 | apply H3 | apply H4*) | apply H6 | apply H5])
    end.



Lemma sig_term_ev_lseq: forall t1 t2 e,
    not_hash_sig_term_ev (lseq t1 t2) e ->  
    not_hash_sig_term_ev t1 e.
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in *.
  split.
  -
    cbv.
    intros.
    destruct_conjs.
    subst.
    unfold not_hash_sig_term in *.
    unfold not in *.
    eapply H.
    
    repeat eexists.
    eauto.
    eassumption.
    eauto.
  -  
    split; eauto.
Defined.


Lemma sig_is: forall t annt (*ecc ecc'*) e e' p i,

    (*anno_parP pt t loc -> *)
    (*well_formed_r pt -> *)
    annoP annt t i ->
    (*
    wf_ec ecc -> *)
    (*
    copland_compileP pt
                     {| st_ev := ecc; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
     *)
    

    cvm_evidence_denote annt p e = e' ->
    (*
    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' -> *)

    gg_sub e' ->

    gg_sub e \/
    term_sub (asp SIG) t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ff.
  -
    dd.
    
    destruct a; invc H; dd; eauto; try tauto.

    (*
    +
      do_reconP_determ.
      eauto.
     *)


    +
      do_ggsub.
      evSubFacts.
      left.
      econstructor.
      eauto.
    +
      do_ggsub.
      evSubFacts.
      
  - (* aatt case *)
    dd.
    invc H.
    dd.
    
    edestruct IHt.
    econstructor.
    reflexivity.
    (*
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    econstructor.
    tauto. *)
    reflexivity.
    jkjke.
    eauto.
    eauto.


    (*
    
    eassumption.

    rewrite <- ccp_iff_cc.

    apply copland_compile_at.
    (*
    eapply wfr_annt_implies_wfr_par.
    eassumption. 
    econstructor. tauto. *)
    eassumption.

    erewrite anno_unanno_par.
    eassumption.
    eapply annopar_fst_snd.
    
    eassumption.
    
    left. eauto.
    destruct_conjs.
    eauto.
     *)
    
  -
    dd.
    invc H.
    dd.

    assert (gg_sub (cvm_evidence_denote a p e) \/ term_sub (asp SIG) t2).
    {
      eapply IHt2.
      econstructor.
      reflexivity.
      reflexivity.
      simpl.
      jkjke.
    }

    door.
    +
      edestruct IHt1.
      econstructor. reflexivity.
      reflexivity.
      jkjke.
      eauto.
      eauto.
    +
      eauto.

  - (* abseq case *)
    dd.
    invc H.
    dd.

    do_ggsub.
    evSubFacts.
    +


    edestruct IHt1.
    econstructor.
    reflexivity.
    reflexivity.
    jkjke.
    simpl.
    repeat eexists.
    eassumption.
    destruct_conjs.
    subst.
    left.
    repeat eexists.
    destruct s; destruct s; destruct s0;
      dd;
      try solve_by_inversion;
      eauto.
    right.
    eauto.
    +
      edestruct IHt2.
    econstructor.
    reflexivity.
    reflexivity.
    jkjke.
    simpl.
    repeat eexists.
    eassumption.
    destruct_conjs.
    subst.
    left.
    repeat eexists.
    destruct s; destruct s; destruct s0;
      dd;
      try solve_by_inversion;
      eauto.
    right.
    eauto.
    - (* abseq case *)
    dd.
    invc H.
    dd.

    do_ggsub.
    evSubFacts.
    +


    edestruct IHt1.
    econstructor.
    reflexivity.
    reflexivity.
    jkjke.
    simpl.
    repeat eexists.
    eassumption.
    destruct_conjs.
    subst.
    left.
    repeat eexists.
    destruct s; destruct s; destruct s0;
      dd;
      try solve_by_inversion;
      eauto.
    right.
    eauto.
    +
      edestruct IHt2.
    econstructor.
    reflexivity.
    reflexivity.
    jkjke.
    simpl.
    repeat eexists.
    eassumption.
    destruct_conjs.
    subst.
    left.
    repeat eexists.
    destruct s; destruct s; destruct s0;
      dd;
      try solve_by_inversion;
      eauto.
    right.
    eauto.
Defined.

(*
Lemma sig_is: forall t pt ecc ecc' e e' tr tr' p p' loc i i',

    anno_parP pt t loc ->
    (*well_formed_r pt -> *)
    wf_ec ecc ->
    copland_compileP pt
                     {| st_ev := ecc; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->

    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' ->

    gg_sub e' ->

    gg_sub e \/
    term_sub (asp SIG) t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ff.
  -
    wrap_ccp.
    
    destruct a; dd.
    +
      do_reconP_determ.
      eauto.

    +
      unfold cons_uu in *.
      repeat ff.

      do_rewrap_reconP.

      do_reconP_determ.

      do_ggsub.
      evSubFacts.
      
      left.
      econstructor.
      eauto.
    +
      do_ggsub.
      right.
      eauto.
    +
      unfold cons_hh in *.
      repeat ff.
      do_rewrap_reconP.
      do_ggsub.
      evSubFacts.
  - (* aatt case *)
    wrap_ccp.
    
    edestruct IHt.
    econstructor.
    reflexivity.
    (*
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    econstructor.
    tauto. *)
    
    eassumption.

    rewrite <- ccp_iff_cc.

    apply copland_compile_at.
    (*
    eapply wfr_annt_implies_wfr_par.
    eassumption. 
    econstructor. tauto. *)
    eassumption.

    erewrite anno_unanno_par.
    eassumption.
    eapply annopar_fst_snd.
    
    eassumption.
    
    left. eauto.
    destruct_conjs.
    eauto.
  -

    wrap_ccp.
    
    do_wfec_preserved.
    do_somerecons.

    do_reconP_determ.

    specialize IHt1 with (loc:=loc).

    specialize IHt2 with (loc:=l).

    assert (gg_sub H7 \/ (term_sub (asp SIG) t2)).
    {
      eapply IHt2.
      eassumption.
      2: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      eassumption.
    }
    door.

    assert (gg_sub H8 \/ (term_sub (asp SIG) t1)).
    {
      eapply IHt1.
      eassumption.
      2: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      eassumption.
    }

    door; eauto.
    eauto.

  - (* abseq case *)

    wrap_ccp.

    do_rewrap_reconP.

    do_reconP_determ.

    do_wfec_split.
    
    do_wfec_preserved.
 
    do_wfec_firstn.

    do_somerecons.
    
    do_wfec_skipn.
    clear_skipn_firstn.

    do_reconP_determ.

    do_ggsub.

    evSubFacts.

    +
          
      assert (gg_sub H12 \/ term_sub (asp SIG) t1).
      {
        destruct s.
        destruct s; destruct s0;
          dd.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eauto.

          repeat eexists.
          eauto.

        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          eauto.

          repeat eexists.
          eauto.

        ++
          assert (gg_sub mtc \/ (term_sub (asp SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: { eassumption. }
            econstructor.
            eauto.
            econstructor. tauto.
            
            eauto.
           
            repeat eexists.
            eauto.
          }
          door.
          +++
            do_ggsub.
            solve_by_inversion.
          +++
            eauto.
        ++
          assert (gg_sub mtc \/ (term_sub (asp SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.
            
            eauto.
           
            repeat eexists.
            eauto.
          }
          door.
          +++
            do_ggsub.
            solve_by_inversion.
          +++
            eauto.
      }
      door; eauto.

    +
         
      assert (gg_sub H12 \/ term_sub (asp SIG) t2).
      {
        destruct s.
        destruct s; destruct s0;
          dd.
        ++
          eapply IHt2.
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          eauto.

          repeat eexists.
          eauto.
        ++
          
          assert (gg_sub mtc \/ (term_sub (asp SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.
            eauto.
           
            repeat eexists.
            eauto.
          }
          door.
          +++
            do_ggsub.
            solve_by_inversion.
          +++
            eauto.

        ++
          
          eapply IHt2.
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          eauto.
          
          repeat eexists.
          eauto.
        ++
         
          assert (gg_sub mtc \/ (term_sub (asp SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.
            eauto.

            repeat eexists.
            eauto.
          }
          door.
          +++
            do_ggsub.
            solve_by_inversion.
          +++
            eauto.
      }
      door; eauto.

  - (* NEW abpar case *)

    wrap_ccp.
    do_rewrap_reconP.

    do_wfec_split.
    
    do_wfec_preserved.

    
    do_wfec_firstn.

    do_somerecons.

    do_wfec_skipn.
    clear_skipn_firstn.

    do_reconP_determ.
    do_ggsub.

    evSubFacts.

    +
    
      assert (gg_sub H10 \/ term_sub (asp SIG) t1).
      {
        destruct s.
        destruct s; destruct s0;
          dd; do_reconP_determ.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          eauto.

          repeat eexists.
          eauto.


        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          eauto.

          repeat eexists.
          eauto.

        ++
         
          assert (gg_sub mtc \/ (term_sub (asp SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.       
            eauto.
            
            repeat eexists.
            eauto.
          }
          door.
          +++
            do_ggsub.
            solve_by_inversion.
          +++
            eauto.
        ++
         
          assert (gg_sub mtc \/ (term_sub (asp SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.        
            eauto.
           
            repeat eexists.
            eauto.
          }
          door.
          +++
            do_ggsub.
            solve_by_inversion.
          +++
            eauto.
      }
      door; eauto.

    +
      wrap_ccp.

       assert (exists l' t', anno_par t2 0 = (l',t')).
       {
         destruct (anno_par t2 0).
         repeat eexists.
       }     
       destruct_conjs.
       
       specialize IHt2 with (loc:=0).
       (*
       assert (well_formed_r H21).
       {
         eapply wfr_annt_implies_wfr_par.
         2: {
           econstructor.
           jkjke. }
         eassumption.
       } *)

       do_annopar_redo.
 
      assert (gg_sub H10 \/ term_sub (asp SIG) t2).
      {
        destruct s.
        destruct s; destruct s0;
          dd.
        ++
         
          eapply IHt2.
          eassumption.
          
          2: {
            rewrite <- ccp_iff_cc.
            eapply copland_compile_at.
          }
          3: {
          
          rewrite at_evidence.
          erewrite <- par_evidence.
          erewrite anno_unanno_par.
          rewrite Heqe1.
          eassumption.
          invc H16.
          eapply annopar_fst_snd.
          }

          eassumption.
          eassumption.
          repeat eexists.
          eauto.

        ++
          
          assert (gg_sub mtc \/ (term_sub (asp SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: {
              rewrite <- ccp_iff_cc.
              eapply copland_compile_at.
            }
            3: {
          
          rewrite at_evidence.
          erewrite <- par_evidence.
          erewrite anno_unanno_par.
          rewrite Heqe1.
          eassumption.
            invc H16.
            eapply annopar_fst_snd.
            }
            econstructor.
            tauto.
            econstructor.
            tauto.
            repeat eexists.
            eauto.
          }
          door.
          +++
            do_ggsub.
            solve_by_inversion.
          +++
            eauto.
        ++
          eapply IHt2.
          eassumption.
          

          2: {
            rewrite <- ccp_iff_cc.
            eapply copland_compile_at.
          }
          3: {
          
          rewrite at_evidence.
          erewrite <- par_evidence.
          erewrite anno_unanno_par.
          rewrite Heqe1.
          eassumption.
            invc H16.
            eapply annopar_fst_snd.
          }

          eassumption.
          
          eassumption.
          repeat eexists.
          eauto.

        ++

          assert (gg_sub mtc \/ (term_sub (asp SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: {
              rewrite <- ccp_iff_cc.
              eapply copland_compile_at.
            }
            3: {
          
          rewrite at_evidence.
          erewrite <- par_evidence.
          erewrite anno_unanno_par.
          rewrite Heqe1.
          eassumption.
            invc H16.
            eapply annopar_fst_snd.  }

            econstructor.
            tauto.
            econstructor.
            tauto.
            repeat eexists.
            eauto.
          }
          door.
          +++
            do_ggsub.
            solve_by_inversion.
          +++
            eauto.
      }

      door; eauto.
      
      Unshelve.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
Defined.
 *)

Check sig_is.
(*
sig_is
     : forall (t : Term) (annt : AnnoTerm) (e e' : EvidenceC) (p i : nat),
       annoP annt t i ->
       cvm_evidence_denote annt p e = e' ->
       gg_sub e' -> gg_sub e \/ term_sub (asp SIG) t
*)


Ltac do_sig_is :=
  repeat 
  match goal with
  | [(*H: well_formed_r ?pt, *)
        (*H2: wf_ec ?ecc, *)
            H': annoP ?annt ?t _,
                H6: gg_sub ?e',
                           He: EvidenceC
                    
                    (*H3: cvm_evidence_denote ?annt _ ?e = ?e' *)
                (*H4: reconstruct_evP ?ecc ?e,
                    H5: reconstruct_evP ?ecc' ?e', 
                        H3: copland_compileP ?pt
                                             {| st_ev := ?ecc; st_trace := _; st_pl := _; st_evid := _ |}
                                             (Some tt)
                                             {| st_ev := ?ecc'; st_trace := _; st_pl := _; st_evid := _ |} *)

     |- _] =>
    
    assert_new_proof_by
      (gg_sub He \/ (term_sub (asp SIG) t))
      ltac:(eapply sig_is; [apply H' | (*apply H |*) (*apply H2 |*) try reflexivity; try eassumption (*apply H3*) | (*apply H4 | apply H5 |*) apply H6])
  end.

Ltac do_hsh_subt :=
  unfold hsh_subt in *;
  destruct_conjs;
  subst.

Lemma sig_term_ev_bseql: forall s (t1 t2 : Term)
                           (e : EvidenceC),
    not_hash_sig_term_ev (bseq s t1 t2) e ->
    
    not_hash_sig_term_ev t1 (splitEvl s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in *.
  destruct_conjs.
  unfold not in *.
  
  split.
  -
    cbv.
    intros.
    destruct_conjs.
    subst.
    cbv in H.
    eapply H.
    repeat eexists.
    eauto.
    eauto.
    eauto.

  -
    destruct s.
    destruct s; destruct s0; ff;
      try (
          split; eauto;
          unfold not; intros;
          do_hsh_subt;
          forwards; eauto;
          tauto);
      try (
          split;
          cbv; intros;
          try evSubFacts;
          destruct_conjs;
          try do_ggsub;
          solve_by_inversion).
Defined.

Lemma sig_term_ev_bseqr: forall s (t1 t2 : Term)
                           (e : EvidenceC),
    
    not_hash_sig_term_ev (bseq s t1 t2) e ->   
    not_hash_sig_term_ev t2 (splitEvr s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in *.
  
  split.
  -
    cbv.
    intros.
    destruct_conjs.
    subst.
    cbv in H.
    eapply H.
    repeat eexists.
    eauto.
    eauto.
    eauto.
  -
    destruct s.
    destruct s; destruct s0; ff;
      try (
          split; eauto;
          unfold not; intros;
          do_hsh_subt;
          forwards; eauto;
          tauto);
      try (
          split;
          cbv; intros;
          try evSubFacts;
          destruct_conjs;
          try do_ggsub;
          solve_by_inversion).
Defined.

Lemma sig_term_ev_bparl: forall s (t1 t2 : Term)
                           (e : EvidenceC),
    
    not_hash_sig_term_ev (bpar s t1 t2) e ->
    not_hash_sig_term_ev t1 (splitEvl s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in *.
  
  split.
  -
    cbv.
    intros.
    destruct_conjs.
    subst.
    cbv in H.
    eapply H.
    repeat eexists.
    eauto.
    eauto.
    eauto.
  -
    destruct s.
    destruct s; destruct s0; ff;
      try (
          split; eauto;
          unfold not; intros;
          do_hsh_subt;
          forwards; eauto;
          tauto);
      try (
          split;
          cbv; intros;
          try evSubFacts;
          destruct_conjs;
          try do_ggsub;
          solve_by_inversion).
Defined.

Lemma sig_term_ev_bparr: forall s (t1 t2 : Term)
                           (e : EvidenceC),
    
    not_hash_sig_term_ev (bpar s t1 t2) e ->
    not_hash_sig_term_ev t2 (splitEvr s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in *.
  
  split.
  -
    cbv.
    intros.
    destruct_conjs.
    subst.
    cbv in H.
    eapply H.
    repeat eexists.
    eauto.
    eauto.
    eauto.
  -
    destruct s.
    destruct s; destruct s0; ff;
      try (
          split; eauto;
          unfold not; intros;
          do_hsh_subt;
          forwards; eauto;
          tauto);
      try (
          split;
          cbv; intros;
          try evSubFacts;
          destruct_conjs;
          try do_ggsub;
          solve_by_inversion).
Defined.

Lemma not_hste_att: forall t e n,
    not_hash_sig_term_ev (att n t) e ->
    not_hash_sig_term_ev t e.
Proof.
  intros.
  invc H.
  destruct_conjs.
  econstructor.
  
  cbv.
  intros.
  destruct_conjs.
  subst.
  unfold not_hash_sig_term in *.
  unfold not in *.
  eapply H0. (*with (t':=(alseq (n2, n3) H4 H2)). *)
  econstructor.
  repeat eexists.
  eassumption.
  eassumption.
  eapply termsub_transitive.
  eassumption.
  econstructor.
  econstructor.
  split.
  eassumption.
  unfold not in *.
  intros.
  destruct_conjs.
  eapply H1.
  eassumption.
  econstructor.
  eauto.
Defined.

Ltac do_nhste_att :=
  match goal with
  | [H: not_hash_sig_term_ev (att _ ?t) ?e

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t e)
      ltac:(eapply not_hste_att; apply H)
  end.

Ltac do_nhste_lseql :=
  match goal with
  | [H: not_hash_sig_term_ev (lseq ?t1 _) ?e
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 e)
      ltac:(eapply sig_term_ev_lseq; [apply H (* | apply H2 | apply H3 *) ])
  end.

Lemma nhst_lseq_r: forall t1 t2 e,
    not_hash_sig_term_ev (lseq t1 t2) e ->
    not_hash_sig_term t2.
Proof.
  intros.
  unfold not_hash_sig_term_ev in *.
  destruct_conjs.
  unfold not_hash_sig_term in *.
  cbv.
  unfold not in *.
  intros.
  destruct_conjs.
  eapply H. (*with (t':= (alseq (n, n0) H4 H2)). *)
  econstructor.
  repeat eexists.
  eassumption.
  eassumption.
  subst.
  eauto.
Defined.

Ltac do_nhst_lseqr :=
  match goal with
  | [H: not_hash_sig_term_ev (lseq _ ?t2) _

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t2)
      ltac:(eapply nhst_lseq_r; [apply H ])
  end.

Ltac do_nhste_bseql :=
  match goal with
  | [H: not_hash_sig_term_ev (bseq ?s ?t1 _) ?e
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 (splitEvl s e))
      ltac:(eapply sig_term_ev_bseql; [apply H (* | apply H2 | apply H3 *) ])
  end.

Ltac do_nhste_bseqr :=
  match goal with
  | [H: not_hash_sig_term_ev (bseq ?s _ ?t2) ?e 
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 (splitEvr s e))
      ltac:(eapply sig_term_ev_bseqr; [apply H (*| apply H2 | apply H3 *)])
  end.

Ltac do_nhste_bparl :=
  match goal with
  | [H: not_hash_sig_term_ev (bpar ?s ?t1 _) ?e
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 (splitEvl s e))
      ltac:(eapply sig_term_ev_bparl; [apply H (* | apply H2 | apply H3 *)])
  end.

Ltac do_nhste_bparr :=
  match goal with
  | [H: not_hash_sig_term_ev (bpar ?s _ ?t2) ?e
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 (splitEvr s e))
      ltac:(eapply sig_term_ev_bparr; [apply H (* | apply H2 | apply H3 *) ])
  end.

      Lemma gg_recons'': forall e (*ecc*) x y,
          (*reconstruct_evP ecc e -> *)
          not_hash_sig_ev e ->
          EvSubT (gg x y) (et_fun e) ->
          gg_sub e.
      Proof.
        intros.
        generalizeEverythingElse e.
        induction e; intros; ff.
        -
          invc H0.
          do_nhse.
          
          assert (gg_sub e).
          eapply IHe.
          eassumption.
          eassumption.
          
          
          do_ggsub.
          repeat eexists.
          eauto.
        -
          do_ggsub.
          repeat eexists.
          eauto.
        -
          invc H0.
          unfold not_hash_sig_ev in *.
          unfold not in *.
          exfalso.
          eapply H.
          econstructor.
          repeat eexists.
          eassumption.
          econstructor.
        -
          invc H0.
          +
            do_nhse.
            assert (gg_sub e1) by eauto.
            
            do_ggsub.
            repeat eexists.
            eauto.
          +
            do_nhse.
            assert (gg_sub e2) by eauto.
            
            do_ggsub.
            repeat eexists.
            eauto.
                -
          invc H0.
          +
            do_nhse.
            assert (gg_sub e1) by eauto.
            
            do_ggsub.
            repeat eexists.
            eauto.
          +
            do_nhse.
            assert (gg_sub e2) by eauto.
            
            do_ggsub.
            repeat eexists.
            eauto.
      Defined.

Lemma hshsig_ev_term_contra: forall t annt p (e e' :EvidenceC) i,

    (*anno_parP pt t loc -> *)
    annoP annt t i ->
    (*well_formed_r pt -> *)
    (*wf_ec ecc -> *)
    not_hash_sig_term_ev t e ->

    (*
    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' ->
     
    

    copland_compileP pt
                     {| st_ev := ecc; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
     *)
    cvm_evidence_denote annt p e = e' ->

    not_hash_sig_ev e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    dd.
    invc H.
    dd.
    destruct a; dd.
    +
    unfold not_hash_sig_term_ev in *.
    destruct_conjs.
    eassumption.
    +
    unfold cons_uu in *.
    repeat ff.
    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    (*
    do_rewrap_reconP.
    do_reconP_determ. *)
    eapply not_hshsig_uuc; eauto.
    +
    repeat ff.
    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    unfold cons_sig in *.
    ff.
    (*
    do_rewrap_reconP.
    do_reconP_determ. *)
      
    eapply not_hshsig_ggc; eauto.
    +
      assert (~ (gg_sub e)).
      {
        unfold not_hash_sig_term_ev in *.
        destruct_conjs.
        unfold not in *; intros.
        apply H1.
        eassumption.
        eauto.
      }
      unfold not_hash_sig_term_ev in *.
      destruct_conjs.
      
      unfold not_hash_sig_ev.
      intros.
      unfold not in *; intros.
      invc H4.
      unfold hash_sig_ev in *.
      destruct_conjs.
      invc H8.
      apply H.
      Locate gg_recons.
      Check gg_recons.



      (*
  intros e ecc x y H H0 H1.
  generalizeEverythingElse e.
  induction e; intros;
    destruct ecc; ff;
    do_inv_recon;
      try solve_by_inversion;
      do_nhse;
      do_recon_inv.
      
  - (* uuc case *)
    evSubTFacts.
    assert (gg_sub e) by eauto.
    do_ggsub. 
    repeat eexists.
    eauto.
    
  - (* ggc case *)
    econstructor.
    repeat eexists.
    eauto.
    
  - (* ssc case *)
    evSubTFacts.
    +
      assert (gg_sub e1) by eauto.
      do_ggsub.
      repeat eexists.
      eauto.
    +
      assert (gg_sub e2) by eauto.
      do_ggsub.
      repeat eexists.
      eauto.

  - (* ppc case *)
    evSubTFacts.
    +
      assert (gg_sub e1) by eauto.    
      do_ggsub.
      repeat eexists.
      eauto.
    +
      assert (gg_sub e2) by eauto.
      do_ggsub.
      repeat eexists.
      eauto.
Defined.
       *)

      eapply gg_recons''; eauto.

      (*
      
      
      cbv in *.
      destruct_conjs.
      unfold not; intros.
      do_ggsub.
      
      eapply H2.
      repeat eexists.
      eassumption.
      repeat eexists.
      econstructor. 
    }




      
      invc H0.
      destruct_conjs.
      unfold not in *.
      unfold not_hash_sig_ev.
      intros.
      unfold not.
      intros.
      eapply H1.
      







      
    assert (not_hash_sig_ev e).
    {
      eapply not_ev; eauto.
    }
    unfold cons_hh in *.
    repeat ff.
    (*
    do_rewrap_reconP. *)

    assert (~ (gg_sub e)).
    {
      cbv in *.
      destruct_conjs.
      unfold not; intros.
      do_ggsub.
      
      eapply H2.
      repeat eexists.
      eassumption.
      repeat eexists.
      econstructor.
    }
    unfold not in *.

    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
    eapply H1.
    invc H3.
    invc H2.
    destruct_conjs.
    invc H6.
    unfold not_hash_sig_ev in *.
    unfold not in *.
    exfalso.
    eapply H.
    
    eapply H.
   
    invc H3.
    invc H10.
    

    eapply gg_recons; eauto.
*)

  - (* aatt case *)

    dd.
    invc H.
    dd.
    
    do_nhste_att.

    (*

    do_assume_remote t ecc n loc HHH.

    specialize IHt with (loc:=0). *)
     
    eapply IHt.
    econstructor. tauto.
    eassumption.
    jkjke.

    (*
    reflexivity.
    (*
    eapply wfr_annt_implies_wfr_par;
      [eassumption | econstructor; jkjke]. *)

    2: { eassumption. }
    2: { eassumption. }
    
    eassumption.
    eassumption.
    simpl.
    econstructor.

    subst.
    jkjke.
     *)
    
    
  - (* alseq case *)

    dd.
    invc H.
    dd.
    repeat do_anno_redo.
    (*
    wrap_ccp.
    
    
    specialize IHt1 with (loc:=loc).
    specialize IHt2 with (loc:=l).
    
    do_wfec_preserved.
    do_somerecons.
    do_reconP_determ.
     *)
    
    
    do_nhste_lseql.
    
    assert (not_hash_sig_ev (cvm_evidence_denote a p e)) by eauto.

    do_nhst_lseqr.





    eapply IHt2.
    eassumption.
      
    2: { reflexivity. }
    Print do_sig_is.
    split.
    eassumption.
    split.
    eassumption.
    intros.
    unfold not.
    intros.
    Print do_sig_is.
    (*
Ltac do_sig_is :=
  match goal with
  | H':annoP ?annt ?t _,
    H6:gg_sub ?e',
    H3:cvm_evidence_denote ?annt _ ?e = ?e'
    |- _ =>
        assert_new_proof_by (gg_sub e \/ term_sub (asp SIG) t)
         ltac:(eapply sig_is; [ apply H' | apply H3 | apply H6 ])
  end
     *)

    do_sig_is.


    (*

 

    assert (gg_sub e \/ term_sub (asp SIG) t1).
    {
      eapply sig_is; eauto.
    }
     *)
    
    door.
    ++


      unfold not_hash_sig_term_ev in H0.
      destruct_conjs.
      unfold not in H7.
      eapply H7.
      eassumption.
      eauto.
    ++
      unfold not_hash_sig_term_ev in *.
        destruct_conjs.
        unfold not_hash_sig_term in *.
        unfold not in *.
        eapply H0. (*with (t':= (alseq r t1 t2)). *)
                
        econstructor.
        repeat eexists.
        eassumption.
        
        eassumption.
        eauto.
    
  - (* abseq case *)


    dd.
    invc H.
    dd.
    repeat do_anno_redo.

    (*
    wrap_ccp.
    
    do_rewrap_reconP.
    specialize IHt1 with (loc:=loc).
    specialize IHt2 with (loc:=l).
   

    do_wfec_split.
    do_wfec_preserved.

    do_somerecons.

    do_wfec_firstn.
    do_wfec_skipn.
    clear_skipn_firstn.

    do_reconP_determ.
     *)
    
    
    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
        
    do_nhste_bseql.
    do_nhste_bseqr.
    

    evSubFacts.

    +
      invc H.
      

      destruct_conjs.
      solve_by_inversion.
    +
      assert (not_hash_sig_ev (cvm_evidence_denote a p (splitEvl s e))).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        reflexivity.
      }


      eapply H1; eassumption.

    +
      assert (not_hash_sig_ev (cvm_evidence_denote a0 p (splitEvr s e))) by eauto.
      eapply H1; eassumption.
  -
    
    dd.
    invc H.
    dd.
    repeat do_anno_redo.

    (*
    wrap_ccp.
    
    do_rewrap_reconP.
    specialize IHt1 with (loc:=loc).
    specialize IHt2 with (loc:=l).
   

    do_wfec_split.
    do_wfec_preserved.

    do_somerecons.

    do_wfec_firstn.
    do_wfec_skipn.
    clear_skipn_firstn.

    do_reconP_determ.
     *)
    
    
    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
        
    do_nhste_bparl.
    do_nhste_bparr.
    

    evSubFacts.

    +
      invc H.
      

      destruct_conjs.
      solve_by_inversion.
    +
      assert (not_hash_sig_ev (cvm_evidence_denote a p (splitEvl s e))).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        reflexivity.
      }


      eapply H1; eassumption.

    +
      assert (not_hash_sig_ev (cvm_evidence_denote a0 p (splitEvr s e))) by eauto.
      eapply H1; eassumption.
Defined.

Check hshsig_ev_term_contra.
(*
hshsig_ev_term_contra
     : forall (t : Term) (annt : AnnoTerm) (p : nat) 
         (e e' : EvidenceC) (i : nat),
       annoP annt t i ->
       not_hash_sig_term_ev t e ->
       cvm_evidence_denote annt p e = e' -> not_hash_sig_ev e'
*)

Ltac do_hste_contra :=
  repeat 
  match goal with
  | [(*H: well_formed_r ?pt, *)
        H': annoP ?annt ?t _,
        (*H2: wf_ec ?ecc, *)
            H3: not_hash_sig_term_ev ?t ?e,
                He: EvidenceC
                (*H4: reconstruct_evP ?ecc ?e,
                    H5: reconstruct_evP ?ecc' ?e',
                        H6: copland_compileP ?pt
                                             {| st_ev := ?ecc; st_trace := _; st_pl := _; st_evid := _ |}
                                             (Some tt)
                                             {| st_ev := ?ecc'; st_trace := _; st_pl := _; st_evid := _ |} *)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev He)
      ltac:(eapply hshsig_ev_term_contra; [apply H' | (*apply H |*) (*apply H2 |*) apply H3 | (*apply H4 | apply H5 | apply H6*)try reflexivity; try eassumption])
  end.

Lemma sig_term_ev_lseqr: forall t1 t2 annt e e' p loc,
    annoP annt t1 loc ->
    (*well_formed_r pt -> *)
    (*wf_ec (evc e0 e1) -> *)
    not_hash_sig_term_ev (lseq t1 t2) e ->
    cvm_evidence_denote annt p e = e' ->
    (*
    copland_compileP pt
                     {| st_ev := evc e0 e1; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := evc e2 e3; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
    reconstruct_evP (evc e0 e1) e ->
    reconstruct_evP (evc e2 e3) H5 ->
     *)
    
    not_hash_sig_term_ev t2 e'.
Proof.
  intros.
  
  do_nhste_lseql.
  do_nhst_lseqr.

  split; try eassumption.

  do_hste_contra.

  -
    split; try eassumption.
    +

      intros.
      unfold not; intros.
      Check sig_is.

      edestruct sig_is.
      eassumption.
      eassumption.
      eassumption.




      ++
        unfold not_hash_sig_term_ev in H0.
        destruct_conjs.
        concludes.
        unfold not in *.
        do_hsh_subt.
        forwards;
          eauto.
      ++
        unfold not_hash_sig_term_ev in H0.
        destruct_conjs.
        unfold not_hash_sig_term in H0.
        unfold not in *.
        do_hsh_subt.
        eapply H0; eauto.
        econstructor.
        repeat eexists.
        eauto.
        eauto.
Defined.

Ltac do_evsub_ihhh' :=
  match goal with
  | [H: copland_compileP ?pt
                         {| st_ev := ?ee; st_trace := _; st_pl := _; st_evid := _ |}
                         (Some tt)
                         {| st_ev := ?stev; st_trace := _; st_pl := _; st_evid := _ |},
        H': anno_parP ?pt ?t1 _,
            H'': annoP ?annt ?t1 _,
        H3: reconstruct_evP ?ee _,
            H4: reconstruct_evP ?stev ?v',
                IH: forall _, _ -> _ ,(*context[forall _, well_formed_r ?t1 -> _], *)
       (*Hf: well_formed_r ?pt, *)
       Hnn: not_none_none ?t1,
       Hwf: wf_ec ?ee,
       Hev: events ?annt _ _ _
                   

       |-  (exists e'' : EvidenceC, EvSub (uuc ?params ?p0 ?n e'') _) \/
          (exists (ett : Evidence) p'0 bs (et' : Evidence),
              EvSub (hhc p'0 bs ett) _ /\ EvSubT (uu ?params ?p0 et') ett)
            (*context[EvSub _(*(uuc ?i ?args ?tpl ?tid ?n _)*) _ \/ _]*)
    ] => 

    

    assert_new_proof_by 
      (
        (exists e'' : EvidenceC, EvSub (uuc params p0 n e'') v') \/
        (exists (ett : Evidence) p'0 bs (et' : Evidence),
            EvSub (hhc p'0 bs ett) v' /\ EvSubT (uu params p0 et') ett)
      )

      (*
          assert_new_proof_by
            (exists ee, EvSub (uuc i args tpl tid n ee) v \/
             (exists (ett : Evidence) (p'0 bs : nat) (et':Evidence),
                 EvSub (hhc p'0 bs ett) v /\ EvSubT (uu i args tpl tid et') ett)) 
       *)
      ltac: (eapply IH; [apply H' | apply H'' | (*apply Hf |*) apply Hnn| apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
              (*ltac:(ff; repeat jkjke'; eauto)*)
              
              
  end.

Lemma uu_preserved': forall t annt pt p et n p0 i args tpl tid
                       e tr e' tr' p' ecc ecc' loc l l',

    anno_parP pt t loc ->
    (*well_formed_r pt -> *)
    annoP annt t l ->
    not_none_none t ->
    wf_ec ecc ->
    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' ->
    events annt p et (umeas n p0 i args tpl tid) ->
    copland_compileP pt
                     {| st_ev := ecc; st_trace := tr; st_pl := p; st_evid := l |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := l' |} ->

    (
      (exists e'', EvSub (uuc (asp_paramsC i args tpl tid) p0 (do_asp (asp_paramsC i args tpl tid) p0 n) e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu (asp_paramsC i args tpl tid) p0 et') ett)
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    wrap_ccp.
    invc H0.
    invc H.
    
    destruct a; ff.
    +
      invEvents.

      unfold cons_uu in *.
      repeat ff.
      
      do_rewrap_reconP.
      left.
      eexists.
      econstructor.
  -
    wrap_ccp.
    inversion H0.
    subst.
    inversion H.
    subst.
    cbn in *.
    repeat break_let.
    simpl in *.
    clear H6.
    
    inv_events.

    (*
    invEvents. *)
    do_not_none.

    do_assume_remote t ecc n (S l) H9.
    
      specialize IHt with (loc:=0).

      eapply IHt.
      econstructor.
      reflexivity.
      (*
      eapply wfr_annt_implies_wfr_par.
      eassumption. *)
      econstructor. tauto.
      eassumption.
      eassumption.
      eassumption.
      eassumption.

      rewrite Heqp.
      simpl.
      eassumption.
      rewrite H10.
      erewrite anno_unanno_par.
      rewrite H7.
      simpl.
      rewrite H10 in *.
      econstructor.
      eassumption.
      eassumption.
    
  -
    wrap_ccp.
    
    inversion H; inversion H0.
    
    dd.
    assert (st_evid0 = n1).
    {
      symmetry.
      eapply span_cvm.
      eassumption.
      eassumption.
      eassumption.
    }
    assert (l' = n2).
    {
      subst.
      symmetry.
      eapply span_cvm.
      apply Heqp3.
      eassumption.
      eassumption.
    }
    dd.
    
    
    repeat do_annopar_redo.
    repeat do_anno_redo.
    repeat clear_dups.
    clear Heqp7; clear l2.
  
    do_not_none.

    invEvents.
    + (* t1 case *)
      
      do_wfec_preserved.
      do_somerecons.
      do_reconP_determ.





      
      Print do_evsub_ihhh'.
      (*
Ltac do_evsub_ihhh' :=
  match goal with
  | H:copland_compileP ?pt
        {| st_ev := ?ee; st_trace := _; st_pl := _; st_evid := _ |} 
        (Some tt)
        {| st_ev := ?stev; st_trace := _; st_pl := _; st_evid := _ |},
    H':anno_parP ?pt ?t1 _,
    H3:reconstruct_evP ?ee _,
    H4:reconstruct_evP ?stev ?v',
    IH:_ -> _ -> _,
    Hnn:not_none_none ?t1,
    Hwf:wf_ec ?ee,
    Hev:events ?t1 _ _ _
    |-
    (exists e'' : EvidenceC, EvSub (uuc ?params ?p0 ?n e'') _) \/
    (exists (ett : Evidence) p'0 bs (et' : Evidence),
       EvSub (hhc p'0 bs ett) _ /\ EvSubT (uu ?params ?p0 et') ett) =>
        assert_new_proof_by
         ((exists e'' : EvidenceC, EvSub (uuc params p0 n e'') v') \/
          (exists (ett : Evidence) p'0 bs (et' : Evidence),
             EvSub (hhc p'0 bs ett) v' /\ EvSubT (uu params p0 et') ett))
         ltac:(eapply IH;
                [ apply H'
                | apply Hnn
                | apply Hwf
                | apply H3
                | apply H4
                | apply Hev
                | apply H ])
  end
*)

      repeat do_evsub_ihhh'.

      door.
      ++

        do_evaccum.

        door.
        +++
          left.
          eauto.
        +++
          
          right.
          repeat (eexists; eauto).
           
      ++
        do_evaccum.

        door.
        +++
          right.
          repeat (eexists; eauto).
        +++
          
          right.
          repeat eexists.
          eauto.

          eapply evsubT_transitive.
          eapply hhSubT.
          eassumption.
          eassumption.
          
    + (* t2 case *)

      do_wfec_preserved.
      do_somerecons.

      do_reconP_determ.

      (*


      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      4 : { eassumption. }
      4: { eassumption. *)



      
      
      do_evsub_ihhh'.

      door.
      ++
        eauto.
      ++
        destruct_conjs;
          right;
          repeat (eexists; eauto).

  - (* abseq case *)

    wrap_ccp.
    
    inversion H; inversion H0.
    
    dd.
    assert (st_evid1 = n1).
    {
      symmetry.
      eapply span_cvm.
      eassumption.
      eassumption.
      assert (l + 1 = S l) by lia.
      jkjke.
    }
    assert (st_evid = n2).
    {
      subst.
      symmetry.
      eapply span_cvm.
      apply Heqp7.
      eassumption.
      eassumption.
    }
    dd.
    
    
    repeat do_annopar_redo.
    repeat do_anno_redo.
    repeat clear_dups.
    clear Heqp6; clear l2.
  
    do_not_none.

    do_rewrap_reconP.

    assert (l + 1 = S l) by lia.
    rewrite H4 in *; clear H4.


    (*
    invEvents.
    +
      do_wfec_split.
      do_wfec_preserved.
      do_wfec_firstn.
      do_wfec_skipn.
      clear_skipn_firstn.
      do_wfec_preserved.
      try do_somerecons.
      do_reconP_determ. *)
      




    (*
    wrap_ccp.
    do_not_none.

    do_rewrap_reconP.
     *)
    
    
    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
        try do_somerecons;
        do_reconP_determ;
        do_evsub_ihhh';

        door;
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).

  - (* abpar case *)

        wrap_ccp.
    
    inversion H; inversion H0.
    
    dd.
    assert (st_evid = n1).
    {
      assert (l + 1 = S l) by lia.
      symmetry.
      eapply span_cvm.
      eassumption.
      eassumption.
      jkjke.
    }
    (*
    assert (st_evid = n2).
    {
      admit.
    } *)
    dd.
    
    
    repeat do_annopar_redo.
    repeat do_anno_redo.
    repeat clear_dups.
    (*
    clear Heqp6; clear l2. *)
  
    do_not_none.

    do_rewrap_reconP.

    assert (l + 1 = S l) by lia.
    rewrite H4 in *; clear H4.


    (*
    wrap_ccp.
    do_not_none.

    do_rewrap_reconP.
     *)
    

    invEvents;

      try (
      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
        
      try do_somerecons;
      do_reconP_determ;
        do_evsub_ihhh';

        door;
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto));
          tauto).
    +
      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved.


      do_somerecons.
      do_reconP_determ.

      do_assume_remote t2 (splitEv_r s ecc) p n1 HHH.

      edestruct IHt2.
      econstructor.
      reflexivity.

      (*
      eapply wfr_annt_implies_wfr_par.
      eassumption.
      econstructor.
      tauto. *)
      eassumption.
      eassumption.
      4: {
        eassumption.
        (*
        econstructor.
        rewrite H15.
        simpl.
        eassumption. *)
      }
      4: {
        econstructor.
        rewrite H13.
        simpl.
        eassumption.
      }
      3 : {
        rewrite par_evidence in *.
        rewrite at_evidence in *.
        
        rewrite <- H18.
        rewrite Heqe1.
        eassumption.
      }
      eassumption.
      eassumption.

      destruct_conjs.
      left.
      eauto.

      destruct_conjs.
      right.
      repeat (eexists; eauto).  
Defined.

(*
    anno_parP pt t loc ->
    (*well_formed_r pt -> *)
    annoP annt t l ->
    not_none_none t ->
*)
Lemma uu_preserved: forall t1 t2 annt pt1 pt2 loc1 loc2 p et n p0 i args tpl tid
                      e tr st_ev st_trace p'
                      e' tr' p'' ecc l l' l'',
    anno_parP pt1 t1 loc1 ->
    anno_parP pt2 t2 loc2 ->
    (*well_formed_r pt1 ->
    well_formed_r pt2 -> *)
    annoP annt t1 l ->
    not_none_none t1 ->
    not_none_none t2 ->
    wf_ec e ->
    reconstruct_evP ecc e' ->
    events annt p et (umeas n p0 i args tpl tid) ->
    copland_compileP pt1
                     {| st_ev := e; st_trace := tr; st_pl := p; st_evid := l |}
                     (Some tt)
                     {| st_ev := st_ev; st_trace := st_trace; st_pl := p'; st_evid := l' |} ->
    
    copland_compileP pt2
                     {| st_ev := st_ev; st_trace := st_trace; st_pl := p'; st_evid := l' |}
                     (Some tt)
                     {| st_ev := ecc; st_trace := tr'; st_pl := p''; st_evid := l'' |} ->

    (
      (exists e'', EvSub (uuc (asp_paramsC i args tpl tid) p0 (do_asp (asp_paramsC i args tpl tid) p0 n) e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu (asp_paramsC i args tpl tid) p0 et') ett)
    ).
Proof.
  intros.

  wrap_ccp.
  
  do_wfec_preserved.
  do_somerecons.
  
  assert (
      (exists e'', EvSub (uuc (asp_paramsC i args tpl tid) p0 (do_asp (asp_paramsC i args tpl tid) p0 n) e'') H12) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) H12 /\
          EvSubT (uu (asp_paramsC i args tpl tid) p0 et') ett)
    ).
  {
    eapply uu_preserved'.
    apply H.
    eassumption.
    eassumption.
    4: { eassumption. }
    4: { eassumption. }
    eassumption.
    eassumption.
    eassumption.
  }
  door;
    do_evaccum.
  +
    
    clear H19.
    door; eauto.

    right;
      (repeat eexists; eauto).
  +
    clear H23.
    door; ff.
    ++
      right;
        repeat (eexists; eauto).

    ++
      assert (EvSubT (uu (asp_paramsC i args tpl tid) p0 H20) H23).
      {
        eapply evsubT_transitive.
        apply hhSubT.
        eassumption.
        eassumption.
      }
      
      right; 
        repeat (eexists; eauto).
Defined.

Ltac do_nhste_lseqr :=
  match goal with
  | [(*H: well_formed_r ?pt, *)
        H': anno_parP ?pt ?t1 _,
        H2: wf_ec ?ecc,
            H3: not_hash_sig_term_ev (alseq _ ?t1 ?t2) ?e,
                H5: reconstruct_evP ?ecc ?e,
                    H6: reconstruct_evP ?ecc' ?e',
                        H4: copland_compileP ?pt
                                             {| st_ev := ?ecc; st_trace := _; st_pl := _; st_evid := _ |}
                                             (Some tt)
                                             {| st_ev := ?ecc'; st_trace := _; st_pl := _; st_evid := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 e')
      ltac:(eapply sig_term_ev_lseqr; [apply H' | (*apply H |*) apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
  end.

Ltac do_ste :=
  try do_nhste_att;
  try do_nhste_lseql;
  try do_nhst_lseqr;
  try do_nhste_lseqr;
  try do_nhste_bseql;
  try do_nhste_bseqr;
  try do_nhste_bparl;
  try do_nhste_bparr;
  try do_hste_contra.

Ltac sigEventFacts :=
  match goal with
  | [H: sigEvent _ _ _ _ |- _] => invc H
  end.

Ltac sigEventPFacts :=
  match goal with
  | [H: sigEventP _ |- _] => invc H
  end.

Lemma nhse_bseql_nosplit: forall t1 t2 pt loc ecc ecc' s tr tr' p p' e e' H19 i i',
    anno_parP pt t1 loc ->
    (*well_formed_r pt -> *)
    wf_ec ecc ->
    wf_ec (splitEv_l s ecc) -> 
    not_hash_sig_term_ev (bseq s t1 t2) H19 ->
    copland_compileP pt
                     {|
                      st_ev := splitEv_l s ecc;
                      st_trace := tr;
                      st_pl := p;
                      st_evid := i|}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->

    
    reconstruct_evP ecc H19 ->
    reconstruct_evP (splitEv_l s ecc) e ->
    reconstruct_evP ecc' e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  eassumption.
  5: { eassumption. }
  eassumption.
  eapply sig_term_ev_bseql.
  eassumption.

  
  destruct s; destruct s; destruct s0; ff.
  
  econstructor; tauto.
  econstructor; tauto.
  eassumption.
Defined.

Ltac do_nhse_bseql_nosplit :=
  match goal with
  | [(*H: well_formed_r ?pt, *)
        H': anno_parP ?pt ?t1 _,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_l ?s ?ecc),
                H4: not_hash_sig_term_ev (bseq ?s ?t1 _) ?H19,
                    H6: reconstruct_evP ?ecc ?H19,
                        H7: reconstruct_evP (splitEv_l ?s ?ecc) ?e,
                            H8: reconstruct_evP ?ecc' ?e',
                                H5: copland_compileP ?pt
                                                     {| st_ev := splitEv_l ?s ?ecc; st_trace := _; st_pl := _; st_evid := _ |}
                                                     (Some tt)
                                                     {| st_ev := ?ecc'; st_trace := _; st_pl := _; st_evid := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseql_nosplit; [apply H' | (*apply H |*) apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.

Lemma nhse_bseqr_nosplit: forall t1 t2 pt loc ecc ecc' s tr tr' p p' e e' H19 i i',
    anno_parP pt t2 loc ->
    (*well_formed_r pt -> *)
    wf_ec ecc ->
    wf_ec (splitEv_r s ecc) -> 
    not_hash_sig_term_ev (bseq s t1 t2) H19 ->
    copland_compileP pt
                     {|
                      st_ev := splitEv_r s ecc;
                      st_trace := tr;
                      st_pl := p;
                      st_evid := i|}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->

    
    reconstruct_evP ecc H19 ->
    reconstruct_evP (splitEv_r s ecc) e ->
    reconstruct_evP ecc' e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  eassumption.
  5: { eassumption. }
  eassumption.
  eapply sig_term_ev_bseqr.
  eassumption.
  
  destruct s; destruct s; destruct s0; ff.
  econstructor; tauto.
  econstructor; tauto.
  eassumption.
Defined.

Ltac do_nhse_bseqr_nosplit :=
  match goal with
  | [(*H: well_formed_r ?pt, *)
        H': anno_parP ?pt ?t2 _,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_r ?s ?ecc),
                H4: not_hash_sig_term_ev (bseq ?s _ ?t2) ?H19,
                    H6: reconstruct_evP ?ecc ?H19,
                        H7: reconstruct_evP (splitEv_r ?s ?ecc) ?e,
                            H8: reconstruct_evP ?ecc' ?e',
                                H5: copland_compileP ?pt
                                                     {| st_ev := splitEv_r ?s ?ecc; st_trace := _; st_pl := _; st_evid := _ |}
                                                     (Some tt)
                                                     {| st_ev := ?ecc'; st_trace := _; st_pl := _; st_evid := _|}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseqr_nosplit; [(*apply H |*)apply H' | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.

Lemma nhse_bparl_nosplit: forall t1 t2 pt loc ecc ecc' s tr tr' p p' e e' H19 i i',
    anno_parP pt t1 loc ->
    (*well_formed_r pt -> *)
    wf_ec ecc ->
    wf_ec (splitEv_l s ecc) -> 
    not_hash_sig_term_ev (bpar s t1 t2) H19 ->
    copland_compileP pt
                    {|
                      st_ev := splitEv_l s ecc;
                      st_trace := tr;
                      st_pl := p;
                      st_evid := i|}
                    (Some tt)
                    {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->

    
    reconstruct_evP ecc H19 ->
    reconstruct_evP (splitEv_l s ecc) e ->
    reconstruct_evP ecc' e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  eassumption.
  5: { eassumption. }
  eassumption.
  eapply sig_term_ev_bparl.
  eassumption.
  
  destruct s; destruct s; destruct s0; ff.
  econstructor; tauto.
  econstructor; tauto.
  eassumption.
Defined.

Ltac do_nhse_bparl_nosplit :=
  match goal with
  | [(*H: well_formed_r ?t1, *)
        H': anno_par ?pt ?t1 _,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_l ?s ?ecc),
                H4: not_hash_sig_term_ev (bpar ?s ?t1 _) ?H19,
                    H6: reconstruct_evP ?ecc ?H19,
                        H7: reconstruct_evP (splitEv_l ?s ?ecc) ?e,
                            H8: reconstruct_evP ?ecc' ?e',
                                H5: copland_compileP ?pt
                                                     {| st_ev := splitEv_l ?s ?ecc; st_trace := _; st_pl := _; st_evid := _ |}
                                                     (Some tt)
                                                     {| st_ev := ?ecc'; st_trace := _; st_pl := _; st_evid := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bparl_nosplit; [apply H' | (*apply H |*) apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.

Lemma nhse_bparr_nosplit: forall t1 t2 pt loc ecc ecc' s tr tr' p p' e e' H19 i i',
    anno_parP pt t2 loc ->
    (*well_formed_r pt -> *)
    wf_ec ecc ->
    wf_ec (splitEv_r s ecc) -> 
    not_hash_sig_term_ev (bpar s t1 t2) H19 ->
    copland_compileP pt
                    {|
                      st_ev := splitEv_r s ecc;
                      st_trace := tr;
                      st_pl := p;
                      st_evid := i|}
                    (Some tt)
                    {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->

    
    reconstruct_evP ecc H19 ->
    reconstruct_evP (splitEv_r s ecc) e ->
    reconstruct_evP ecc' e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  eassumption.
  5: { eassumption. }
  eassumption.
  eapply sig_term_ev_bparr.
  eassumption.
  
  destruct s; destruct s; destruct s0; ff.
  econstructor; tauto.
  econstructor; tauto.
  eassumption.
Defined.

Ltac do_nhse_bparr_nosplit :=
  match goal with
  | [(*H: well_formed_r ?pt, *)
        H': anno_parP ?pt ?t2 _,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_r ?s ?ecc),
                H4: not_hash_sig_term_ev (bpar ?s _ ?t2) ?H19,
                    H6: reconstruct_evP ?ecc ?H19,
                        H7: reconstruct_evP (splitEv_r ?s ?ecc) ?e,
                            H8: reconstruct_evP ?ecc' ?e',
                                H5: copland_compileP ?pt
                                                     {| st_ev := splitEv_r ?s ?ecc; st_trace := _; st_pl := _; st_evid := _|}
                                                     (Some tt)
                                                     {| st_ev := ?ecc'; st_trace := _; st_pl := _; st_evid := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bparr_nosplit; [apply H' | (*apply H |*) apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.


Ltac do_nhse_nosplit :=
  try do_nhse_bseql_nosplit;
  try do_nhse_bseqr_nosplit;
  try do_nhse_bparl_nosplit;
  try do_nhse_bparr_nosplit.

Lemma gg_preserved': forall t annt pt loc p et n p0 et'
                       tr e e' tr' p' bits ecc' l l',

    anno_parP pt t loc ->
    (*well_formed_r pt -> *)
    annoP annt t l ->
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    wf_ec (evc bits et) ->
    reconstruct_evP (evc bits et) e ->
    reconstruct_evP ecc' e' ->
    events annt p et (sign n p0 et') ->
    copland_compileP pt
                     {| st_ev := (evc bits et); st_trace := tr; st_pl := p; st_evid := l |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p'; st_evid := l' |} ->

    (
      (exists bits e'', EvSub (ggc p0 (do_sig (MonadVM.encodeEvBits (evc bits et')) p0 n) e'') e' /\
                   et_fun e'' = et' /\
                   bits = encodeEv e''
      )
    ).
Proof.

  intros.
  generalizeEverythingElse t.
  
  induction t; intros.
  -
    wrap_ccp.
    invc H; invc H0.
    subst.
    destruct a; try (ff; tauto).
    +
      ff.
      invEvents.
      ff.
      do_rewrap_reconP.
      do_reconP_determ.
      assert (bits = encodeEv e0).
      {
        eapply recon_encodeEv.
        eassumption.
        eassumption.
      }
      subst.
      
       

      repeat eexists.
      econstructor.
      symmetry.
      
      
      eapply etfun_reconstruct; eauto.

  - (* aatt case *)

    wrap_ccp.
    invEvents.
    do_not_none.

    

    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    do_not_hshsig.

    do_assume_remote t (evc bits et) n HHH.

    eapply IHt.
    econstructor.
    reflexivity.
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    econstructor. tauto.
    eassumption.
    split.
    eassumption.
    split.
    eassumption.
    
    intros.
    unfold not in *; intros.
    do_hsh_subt.
    do_ggsub.
    (*
    invc H11. *)
    
    eapply H9.
    repeat eexists.
    eassumption.
    econstructor.
    eauto.

    2: { eassumption. }
    eassumption.
    eassumption.
    eassumption.
    econstructor.
    rewrite H11.
    simpl.
    rewrite H13.
    
    eapply copland_compile_at.
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    econstructor.
    rewrite H11.
    tauto.
    
  - (* alseq case *)

    wrap_ccp.
    do_not_none.
    
    assert (not_hash_sig_term t1 /\ not_hash_sig_term t2).
    {
      eapply not_hshsig_alseq_pieces.
      invc H2.
      eassumption.
    }
    destruct_conjs.
    
    invEvents.
    + (* t1 case *)
      
      do_wfec_preserved.
      do_somerecons.

      do_reconP_determ.
      
      destruct ecc'; destruct st_ev0.
      
      repeat do_ste.
      
      edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      5: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      2: { eassumption. }
      eassumption.

      destruct_conjs.

      do_evaccum.

      door.
      +++
        eauto.
      +++
        dd.
        
        unfold not_hash_sig_ev in H22.
        
        unfold not in *.
        exfalso.
        eapply H22.
        econstructor.
        repeat eexists.
        eassumption.
        eassumption.       
        
    + (* t2 case *)

      wrap_ccp.

      do_wfec_preserved.
      do_somerecons.
      do_reconP_determ.
      destruct st_ev0;
        destruct ecc'.

      assert (e = (aeval t1 p et)).
      {
        rewrite <- eval_aeval.
        inversion Heqp4.
        assert (t1 = unannoPar a1).
        {
          erewrite anno_unanno_par.
          reflexivity.
          rewrite H20.
          eapply annopar_fst_snd.
        }
        rewrite H25.

        eapply cvm_refines_lts_evidence.
        eassumption.
        eassumption.
      }
      subst.
      
      repeat do_ste.

      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      5: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      2: { eassumption. }
      eassumption.
      eauto.
      
  - (* abseq case *)
    wrap_ccp.
    inversion H2.
    destruct_conjs.

    do_not_none.
    
    do_not_hshsig.

    do_rewrap_reconP.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      do_somerecons;
      (*
      do_reconP_determ;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons; *)
      try do_evsub_ihhh'.

    +

      do_reconP_determ.
      
      do_nhse_nosplit.  
      
      destruct s; destruct s; destruct s0; ff.

      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        4: { eassumption. }
        eassumption.
        simpl.
        eauto.
        2: { eassumption. }
        eassumption.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        4: { eassumption. }
        eassumption.
        simpl.
        eauto.
        2: { eassumption. }
        eassumption.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        
        econstructor. tauto.
        simpl.
        econstructor. tauto.
        eassumption.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        
        econstructor. tauto.
        simpl.
        econstructor. tauto.
        eassumption.
        destruct_conjs.
        esplit; eauto.

    +
      do_reconP_determ.

      do_nhse_nosplit.

      destruct s; destruct s; destruct s0; ff.

      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        4: { eassumption. }
        eassumption.
        simpl.
        eauto.
        2: { eassumption. }
        eassumption.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        4: { eassumption. }
        4: {
          eassumption.
        }
        econstructor. tauto.
        
        simpl. econstructor. tauto.
        eassumption.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        4: { eassumption. }
        eassumption.
        simpl.
        eauto.
        
        2: { eassumption. }
        eassumption.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        4: { eassumption. }
        4: {
          eassumption.
        }
        econstructor. tauto.
        
        simpl. econstructor. tauto.
        eassumption.
        destruct_conjs.
        esplit; eauto.

  - (* abseq case *)
    wrap_ccp.
    ff.
    inversion H2.
    destruct_conjs.
    do_not_none.
    do_reconP_determ.
    
    do_not_hshsig.

    do_rewrap_reconP.

    do_reconP_determ.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      do_somerecons;
      do_reconP_determ;
      try do_evsub_ihhh'.

    +

      do_reconP_determ.
      
      assert (not_hash_sig_ev H17).
      {
        eapply nhse_bparl_nosplit.
        apply Heqp1.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        eassumption.
        eassumption.
        eassumption.
        eassumption.
        eassumption.
      }
      
      destruct s; destruct s; destruct s0; ff.
      do_reconP_determ.

      ++
        do_nhse_nosplit.
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        4: { eassumption. }
        eassumption.
        simpl.
        ff.
        2: { eassumption. }
        eassumption.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        4: { eassumption. }
        eassumption.
        simpl.
        ff.
        2: { eassumption. }
        eassumption.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        econstructor. tauto.
        eassumption.

        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        4: { eassumption. }
        4: { eassumption. }
        econstructor. tauto.
        econstructor. tauto.
        eassumption.

        destruct_conjs.
        esplit; eauto.

    +
      do_reconP_determ.
      
      destruct s; destruct s; destruct s0; ff.
      do_reconP_determ.

      ++
        do_assume_remote t2 (evc bits et) p HHH.
        edestruct IHt2.
        econstructor.
        reflexivity.
        eapply wfr_annt_implies_wfr_par.
        eassumption.
        econstructor.
        tauto.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        5: {
          rewrite H18.
          simpl.
          econstructor.
          eassumption.
        }
        eassumption.
        eassumption.
        2: { eassumption. }
        rewrite at_evidence.
        rewrite par_evidence in *.
        rewrite <- H21.
        rewrite Heqe1.
        eassumption.
        
        destruct_conjs.
        esplit; eauto.
      ++
        do_assume_remote t2 mt_evc p HHH.
        edestruct IHt2.
        econstructor.
        reflexivity.
        eapply wfr_annt_implies_wfr_par.
        eassumption.
        econstructor.
        tauto.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        5: {
          rewrite H21.
          simpl.
          econstructor.
          eassumption.
        }
        ff.
        econstructor. tauto.

        2: { eassumption. }
        rewrite at_evidence.
        rewrite par_evidence in *.
        rewrite <- H26.
        rewrite Heqe1.
        eassumption.

        destruct_conjs.
        esplit; eauto.
      ++
        do_assume_remote t2 (evc bits et) p HHH.
        edestruct IHt2.
        econstructor.
        reflexivity.
        eapply wfr_annt_implies_wfr_par.
        eassumption.
        econstructor.
        tauto.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        5: {
          rewrite H21.
          simpl.
          econstructor.
          eassumption.
        }
        eassumption.
        eassumption.
        2: { eassumption. }
        rewrite at_evidence.
        rewrite par_evidence in *.
        rewrite <- H26.
        rewrite Heqe1.
        eassumption.
        
        destruct_conjs.
        esplit; eauto.
      ++
        do_assume_remote t2 mt_evc p HHH.
        edestruct IHt2.
        econstructor.
        reflexivity.
        eapply wfr_annt_implies_wfr_par.
        eassumption.
        econstructor.
        tauto.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        5: {
          rewrite H21.
          simpl.
          econstructor.
          eassumption.
        }
        ff.
        econstructor. tauto.

        2: { eassumption. }
        rewrite at_evidence.
        rewrite par_evidence in *.
        rewrite <- H26.
        rewrite Heqe1.
        eassumption.

        destruct_conjs.
        esplit; eauto.
Defined.

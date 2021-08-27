Require Import ConcreteEvidence Appraisal_Defs StVM Impl_vm Impl_appraisal Auto AutoApp External_Facts MonadVM Helpers_VmSemantics VmSemantics.

Require Import Coq.Program.Tactics Lia.

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

Lemma uuc_app: forall e' e'' i args tpl tid n,
    EvSub (uuc i args tpl tid n e'') e' ->
    exists e'', EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e'')
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
    EvSub (hhc p (checkHash et p bs) et)
          (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff;
    try evSubFacts;
    eauto.
Defined.

Lemma etfun_reconstruct: forall e e0 e1,
    Some e = reconstruct_ev' e0 e1 ->
    e1 = et_fun e.
Proof.
  intros.
  generalizeEverythingElse e1.
  induction e1; intros;
    repeat ff;
    repeat jkjke.
Defined.

Ltac dest_evc :=
  repeat
    match goal with
    | [H: EvC |-  _ ] => destruct H
    end.

Ltac find_wfec :=
  repeat 
    match goal with
    | [H: context [well_formed_r ?t -> _](*
                   wf_ec _ ->
                   copland_compile _ _ _ = _ ->
                   wf_ec _]*),
          H2: well_formed_r ?t,
              H3: wf_ec ?e,
                  H4: copland_compile ?t
                                      {| st_ev := ?e; st_trace := _; st_pl := _ |} =
                      (_, {| st_ev := ?e'; st_trace := _; st_pl := _ |})
       |- _ ] => 
      assert_new_proof_by
        (wf_ec e')
        
        ltac:(eapply H; [apply H2 | apply H3 | apply H4])
    end.

Ltac inv_wfec :=
  repeat
    match goal with
    | [H: wf_ec _ |-  _ ] => invc H
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

Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' p p',
    well_formed_r t1 ->
    wf_ec e ->
    copland_compile t1
                    {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt,
     {| st_ev := e'; st_trace := tr'; st_pl := p' |}) ->
    wf_ec (e').
Proof.
  intros.
  generalizeEverythingElse t1.
  induction t1; intros.
  -
    destruct a; ff;
      invc H0;
      try (
          econstructor;
          ff;
          try tauto;
          try congruence).  
  -
    ff.
    do_wf_pieces.

    eapply IHt1;
      try eassumption.

    apply copland_compile_at;
      try eassumption.
  -
    repeat ff.
    vmsts.
    do_wf_pieces.
  -
    repeat ff; vmsts; subst.
    do_wf_pieces.

    do_wfec_split.

    find_wfec;
      inv_wfec;
      ff;
      econstructor;
      ff; repeat jkjke';
        eapply app_length.

  -
    repeat ff; vmsts; subst.
    do_wf_pieces.

    do_wfec_split.

    find_wfec;
      inv_wfec;
      ff;
      econstructor;
      ff; repeat jkjke';
        eapply app_length.   
Defined.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [H: well_formed_r ?t,
          H2: wf_ec ?stev,
              H3: copland_compile ?t
                                  {| st_ev := ?stev; st_trace := _; st_pl := _ |} =
                  (Some tt,
                   {| st_ev := ?stev'; st_trace := _; st_pl := _ |})
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [apply H | apply H2 | apply H3])
                                 
    end.

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
      ltac:(eapply H with (e:=e');
            try (eapply peel_fact; eauto; tauto);
            try (econstructor; first [eapply firstn_long | eapply skipn_long]; try eauto; try lia))      
  end.

Lemma some_recons : forall e,
    wf_ec e ->
    exists ee, Some ee = reconstruct_ev e.
Proof.
  intros.
  destruct e.
  generalizeEverythingElse e0.
  induction e0; intros;
    try (ff; eauto; tauto);
    try
      ( inv_wfec; ff;
        do_some_recons');
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke');
    try ( inv_wfec; ff;
          repeat do_rcih;
          destruct_conjs;
          repeat jkjke').
  assert (e = []).
  { destruct e; try solve_by_inversion. }
  ff.
  eauto.
  destruct e; try solve_by_inversion.
  ff.
  destruct e; try solve_by_inversion.
  ff.
Defined.

Ltac do_somerecons :=
  repeat
    match goal with
    | [H: wf_ec ?e
       |- _ ] =>
      assert_new_proof_by
        (exists x, Some x = reconstruct_ev e)
        ltac:(eapply some_recons; apply H)     
    end; destruct_conjs.

Ltac do_evsub_ih :=
  match goal with
  | [H: copland_compile ?t1 {| st_ev := _; st_trace := _; st_pl := _ |} =
        (Some tt, {| st_ev := ?stev; st_trace := _; st_pl := _ |}),
        
        H2: copland_compile ?t2 {| st_ev := ?stev'; st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?v = reconstruct_ev ?stev

     |- context[EvSub ?e'' _ \/ _]] =>
    
    assert_new_proof_by
      (EvSub e'' v \/
       (exists (ett : Evidence) (p'0 bs : nat),
           EvSub (hhc p'0 bs ett) v /\ EvSubT (et_fun e'') ett))
      eauto
  end.

Ltac do_evsubh_ih :=
  match goal with
  | [H: EvSub (hhc ?H2 ?H3 ?H4) _

     |- context[EvSub _ ?e' \/ _]] =>
    
    assert_new_proof_by
      (EvSub (hhc H2 H3 H4) e' \/
       (exists (ett : Evidence) (p'0 bs : nat),
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

Lemma fold_recev: forall e0 e1,
    reconstruct_ev' e0 e1 = reconstruct_ev (evc e0 e1).
Proof.
  ff.
  tauto.
Defined.

Ltac clear_skipn_firstn :=
  match goal with
  | [H: firstn _ _ = _,
        H2: skipn _ _ = _ |- _]
    => rewrite H in *; clear H;
      rewrite H2 in *; clear H2
  end.

Lemma not_none_alseq_pieces: forall r t1 t2,
    not_none_none (alseq r t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_none_abseq_pieces: forall r s t1 t2,
    not_none_none (abseq r s t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_none_abpar_pieces: forall r s t1 t2,
    not_none_none (abpar r s t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_none_aatt_pieces: forall r q t1,
    not_none_none (aatt r q t1) ->
    not_none_none t1.
Proof.
  intros;
    unfold not_none_none in *;
    unfold not in *.
  eauto.
Defined.

Lemma not_hshsig_alseq_pieces: forall r t1 t2,
    not_hash_sig_term (alseq r t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  intros;
    unfold not_hash_sig_term in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_hshsig_abseq_pieces: forall r s t1 t2,
    not_hash_sig_term (abseq r s t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  intros;
    unfold not_hash_sig_term in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_hshsig_abpar_pieces: forall r s t1 t2,
    not_hash_sig_term (abpar r s t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  intros;
    unfold not_hash_sig_term in *;
    unfold not in *.
  split; eauto.
Defined.

Lemma not_hshsig_aatt_pieces: forall r q t1,
    not_hash_sig_term (aatt r q t1) ->
    not_hash_sig_term t1.
Proof.
  intros;
    unfold not_hash_sig_term in *;
    unfold not in *.
  eauto.
Defined.

Ltac do_not_none_alseq_pieces :=
  match goal with
  | [H: not_none_none (alseq _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_alseq_pieces; apply H)
  end.

Ltac do_not_none_abseq_pieces :=
  match goal with
  | [H: not_none_none (abseq _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_abseq_pieces; apply H)
  end.

Ltac do_not_none_abpar_pieces :=
  match goal with
  | [H: not_none_none (abpar _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_abpar_pieces; apply H)
  end.

Ltac do_not_none_aatt_pieces :=
  match goal with
  | [H: not_none_none (aatt _ _ ?t1)

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
  | [H: not_hash_sig_term (alseq _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_alseq_pieces; apply H)
  end.

Ltac do_not_hshsig_abseq_pieces :=
  match goal with
  | [H: not_hash_sig_term (abseq _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_abseq_pieces; apply H)
  end.

Ltac do_not_hshsig_abpar_pieces :=
  match goal with
  | [H: not_hash_sig_term (abpar _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_abpar_pieces; apply H)
  end.

Ltac do_not_hshsig_aatt_pieces :=
  match goal with
  | [H: not_hash_sig_term (aatt _ _ ?t1)

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

Lemma not_none_none_contra_bseq: forall r t1 t2 (P:Prop),
    not_none_none (abseq r (NONE, NONE) t1 t2) ->
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

Lemma not_none_none_contra_bpar: forall r t1 t2 (P:Prop),
    not_none_none (abpar r (NONE, NONE) t1 t2) ->
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
  | [H: not_none_none (abseq _ (NONE,NONE) _ _)

     |- _] =>
    (eapply not_none_none_contra_bseq; apply H)
  end.

Ltac do_none_none_contra_bpar :=
  match goal with
  | [H: not_none_none (abpar _ (NONE,NONE) _ _)

     |- _] =>
    (eapply not_none_none_contra_bpar; apply H)
  end.

Ltac do_none_none_contra :=
  try do_none_none_contra_bseq;
  try do_none_none_contra_bpar.

Lemma evsubt_preserved_aeval: forall t et ett p,
    not_none_none t ->
    EvSubT ett et ->
    EvSubT ett (aeval t p et).
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

Lemma evsubt_preserved: forall t e e' et et' tr tr' p p' ett,
    well_formed_r t ->
    not_none_none t ->
    copland_compile t {| st_ev := evc e et; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := evc e' et'; st_trace := tr'; st_pl := p' |}) ->
    EvSubT ett et ->
    EvSubT ett et'.
Proof.
  intros.
  assert (et' = Term_Defs.eval (unanno t) p et).
  {
    eapply cvm_refines_lts_evidence; eauto.
  }
  subst.

  rewrite eval_aeval.
  eapply evsubt_preserved_aeval; eauto.
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
    exists (uuc n l n0 n1 1 IHy).
    ff.
  -
    destruct_conjs.
    exists (ggc n 1 IHy).
    ff.
  -
    destruct_conjs.
    exists (hhc n 1 y).
    ff.
  -
    exists (nnc n 1).
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

Lemma not_hshsig_uuc: forall e' n l n1 n2 x,
    not_hash_sig_ev e' ->
    not_hash_sig_ev (uuc n l n1 n2 x e').
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
    Some e = reconstruct_ev ecc ->
    EvSubT (gg x y) (get_et ecc) ->
    gg_sub e.
Proof.
  intros e ecc x y H H0.
  generalizeEverythingElse e.
  induction e; intros; ff.
  -
    destruct ecc; ff;
      do_inv_recon.
    solve_by_inversion.
  -
    destruct ecc; ff;
      do_inv_recon.
    solve_by_inversion.
  -
    destruct ecc; ff;
      do_inv_recon.
    (*
    assert (exists et', e1 = uu n l n0 n1 et') by
        (eapply inv_recon_uu; eauto).
    destruct_conjs.
    subst.
     *)
    
    repeat ff.
    evSubTFacts.
    rewrite fold_recev in *.
    assert (gg_sub e2).
    {
      eapply IHe with (ecc:=(evc e1 H1)).
      symmetry.
      find_apply_hyp_goal.
      ff.
      eassumption.
    }
    do_ggsub. 
    repeat eexists.
    eauto.
  -
    destruct ecc; ff.
    econstructor.
    repeat eexists.
    eauto.
  -
    destruct ecc; ff;
      do_inv_recon.
    (*
    assert (e1 = hh n e).
    {
      eapply inv_recon_hh; eauto.
    }
    subst.
     *)
    
    repeat ff.
    evSubTFacts.
    (*
    invc H0. *)
    assert (exists y', y = et_fun y').
    {
      eapply etfun_exists.
    }
    destruct_conjs.
    subst.
    
    econstructor.
    repeat eexists.
    eauto.
  -
    destruct ecc; ff;
      do_inv_recon.
    (*
    assert (exists et1 et2, e0 = ss et1 et2).
    {
      eapply inv_recon_ss; eauto.
    }
    destruct_conjs.
    subst.
     *)
    
    repeat ff.
    evSubTFacts.
    (*
    invc H0. *)
    +
      assert (gg_sub e0).
      {
        rewrite fold_recev in *.
        eapply IHe1.
        symmetry.
        eassumption.
        ff.
        eassumption.
      }
      do_ggsub.
      repeat eexists.
      eauto.
    +
      assert (gg_sub e3).
      {
        rewrite fold_recev in *.
        eapply IHe2.
        symmetry.
        eassumption.
        ff.
        eassumption.
      }
      do_ggsub.
      repeat eexists.
      eauto.
  -
    destruct ecc; ff;
      do_inv_recon.
    (*
    assert (exists et1 et2, e0 = pp et1 et2).
    {
      eapply inv_recon_pp; eauto.
    }
    destruct_conjs.
    subst.
     *)
    
    repeat ff.
    evSubTFacts.
    (*
    invc H0. *)
    +
      assert (gg_sub e0).
      {
        rewrite fold_recev in *.
        eapply IHe1.
        symmetry.
        eassumption.
        ff.
        eassumption.
      }
      do_ggsub.
      repeat eexists.
      eauto.
    +
      assert (gg_sub e3).
      {
        rewrite fold_recev in *.
        eapply IHe2.
        symmetry.
        eassumption.
        ff.
        eassumption.
      }
      do_ggsub.
      repeat eexists.
      eauto.
      Unshelve.
      eauto.
Defined.

Lemma hh_recons: forall e ecc x y,
    Some e = reconstruct_ev ecc ->
    EvSubT (hh x y) (get_et ecc) ->
    exists bs, EvSub (hhc x bs y) e.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros; ff.
  -
    destruct ecc; ff;
      do_inv_recon.
    solve_by_inversion.
  -
   destruct ecc; ff;
      do_inv_recon.
    solve_by_inversion.
  -
    (*
    destruct ecc; ff.
    assert (exists et', e1 = uu n l n0 n1 et').
    {
      destruct e1; repeat ff; try solve_by_inversion.
      eauto.
    }
    destruct_conjs.
    subst. *)

    destruct ecc; ff;
      do_inv_recon.
    repeat ff.
    evSubTFacts.
    rewrite fold_recev in *.
    
    edestruct IHe.
    jkjke'.
    ff.
    eassumption.
    eauto.
  -
    destruct ecc; ff;
      do_inv_recon.
    
    repeat ff.
    rewrite fold_recev in *.
    evSubTFacts.
    
    edestruct IHe.
    symmetry.
    eassumption.
    ff.
    eassumption.
    eauto.
  -
    destruct ecc; ff;
      do_inv_recon.
    repeat ff.
    evSubTFacts.
    eauto.
    eauto.

  -
    destruct ecc; ff;
      do_inv_recon.
    repeat ff.
    evSubTFacts.
    +
      rewrite fold_recev in *.
      edestruct IHe1.
      symmetry.
      eassumption.
      ff.
      eassumption.
      eauto.
    +
      (*
      assert (gg_sub e0).
      {
       *)
      rewrite fold_recev in *.
      edestruct IHe2.
      symmetry.
      eassumption.
      ff.
      eassumption.

      eauto.
  -
    destruct ecc; ff;
      do_inv_recon.

    repeat ff.
    evSubTFacts.
    +
      rewrite fold_recev in *.
      edestruct IHe1.
      symmetry.
      eassumption.
      ff.
      eassumption.
      eauto.
    +
      rewrite fold_recev in *.
      edestruct IHe2.
      symmetry.
      eassumption.
      ff.
      eassumption.
      eauto.
      
      Unshelve.
      eauto.
Defined.

Lemma evAccum: forall t p (e e' e'':EvidenceC) tr tr' p' (ecc ecc':EvC),

    well_formed_r t ->
    not_none_none t ->
    wf_ec ecc ->
    Some e =  (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->
    EvSub e'' e ->
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

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
    destruct a;
      repeat ff;
      try jkjke';
      try unfold cons_uu in *;
      try unfold cons_gg in *;
      (repeat ff; try eauto).
    +
      destruct ecc.
      ff.
      assert (e2 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.
      jkjke'.
      ff.
    +
      destruct ecc.
      ff.
      assert (e1 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.
      right.
      repeat eexists.
      econstructor.
      apply evsub_etfun; eauto.
      
  - (* aatt case *)
    do_wf_pieces.
    do_not_none.
    ff.
    
    eapply IHt.
    eassumption.

    2: {
      apply H1.
    }
    2: {
      eassumption. }
    2: {
      
      eassumption. }
    2: {
      eassumption. }
    2: {
      apply copland_compile_at.
      eassumption.
    }
    eassumption.

  - (* alseq case *)
    ff.
    dosome.
    vmsts.

    do_wf_pieces.

    do_wfec_preserved.

    do_somerecons.

    do_not_none.

    do_evsub_ih.
    
    door.
    +
      eapply IHt2 with (ecc:=st_ev); eauto.
    +

      do_evsubh_ih.
      
      door.
      ++
        right.
        repeat (eexists; eauto).
      ++
        destruct_conjs.
        ff.
        
        right.
        repeat (eexists; eauto).
        do_hh_sub.
        eapply evsubT_transitive; eauto.
        
  - (* abseq case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
    subst.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.
    
    clear_skipn_firstn.

    do_wfec_preserved.

    do_somerecons.

    do_not_none.
    
    destruct s; destruct s; destruct s0;

      try (
          ff;
          try unfold mt_evc in *;
          repeat jkjke';
          ff;
          rewrite fold_recev in *;
          do_evsub_ih;
          
          ff;
          
          door; destruct_conjs;
          try eauto;
          try (right; repeat (eexists; eauto))
        ).

    do_none_none_contra.

  - (* abpar case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
    subst.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.
    
    clear_skipn_firstn.

    do_wfec_preserved.

    do_somerecons.

    do_not_none.
    
    destruct s; destruct s; destruct s0;

      try (
          ff;
          try unfold mt_evc in *;
          repeat jkjke';
          ff;
          rewrite fold_recev in *;
          do_evsub_ih;
          
          ff;
          
          door; destruct_conjs;
          try eauto;
          try (right; repeat (eexists; eauto))
        ).

    do_none_none_contra.
Defined.

Ltac do_evaccum :=
  repeat 
    match goal with
    | [ H: well_formed_r ?t,
           H2: wf_ec ?ecc,
               H3: Some ?e = reconstruct_ev ?ecc,
                   H4: Some ?e' = reconstruct_ev ?ecc',
                       H5: EvSub ?e'' ?e,
                           H6: copland_compile ?t
                                               {| st_ev := ?ecc; st_trace := _; st_pl := _ |} =
                               (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}),
                               H7: not_none_none ?t

        |- _] =>
      
      assert_new_proof_by
        (EvSub e'' e' \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett))
        ltac: (eapply evAccum; [apply H | apply H7 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
    end.

Lemma sig_term_ev_lseq: forall r t1 t2 e e0 e1 e2 e3 tr tr' p p',
    not_hash_sig_term_ev (alseq r t1 t2) e ->
    copland_compile t1 {| st_ev := evc e0 e1; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := evc e2 e3; st_trace := tr'; st_pl := p' |}) ->
    Some e  = reconstruct_ev (evc e0 e1) ->
    not_hash_sig_term_ev t1 e.
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in H3.
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
    unfold not.
    intros.
    destruct_conjs.
    unfold hsh_subt in *.
    destruct_conjs.
    find_eapply_hyp_hyp.
    econstructor.
    eauto.
Defined.

Lemma sig_is: forall t ecc ecc' e e' tr tr' p p',

    well_formed_r t ->
    wf_ec ecc ->
    copland_compile t
                    {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt,
     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    Some e = reconstruct_ev ecc ->
    Some e' = reconstruct_ev ecc' ->

    gg_sub e' ->

    gg_sub e \/
    exists r, term_sub (aasp r SIG) t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; repeat ff.
  -
    jkjke'.
    ff.
  -
    unfold cons_uu in *.
    repeat ff.

    do_ggsub.
    evSubFacts.
    
    left.
    econstructor.
    eauto.
  -
    do_ggsub.
    evSubFacts.
    +
      right.
      exists (n, n0).
      econstructor.
    +
      destruct ecc; ff.
      jkjke'.
  -
    do_ggsub.
    evSubFacts.
    ff.
    left.
    eapply gg_recons; eauto.
  -
    do_wf_pieces.

    edestruct IHt.
    eassumption.
    eassumption.
    apply copland_compile_at.
    eassumption.
    apply H2.
    eassumption.
    eassumption.
    left. eauto.
    destruct_conjs.
    eauto.
  -
    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.

    assert (gg_sub H9 \/ (exists r, term_sub (aasp r SIG) t2)).
    {
      eapply IHt2.
      eassumption.
      apply H6.
      eassumption.
      eassumption.
      jkjke'.
      jkjke'.
      jkjke'.
      ff.
    }
    door.

    assert (gg_sub e \/ (exists r, term_sub (aasp r SIG) t1)).
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

    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
    do_wfec_firstn.
    do_wfec_skipn.
    clear_skipn_firstn.
    repeat find_rewrite.
    vmsts.
    do_ggsub.

    evSubFacts.

    +
      ff.
      rewrite fold_recev in *.
      
      jkjke'.
      jkjke'.
      repeat ff.
      do_wfec_preserved.
      do_somerecons.
      
      assert (gg_sub H5 \/ exists r, term_sub (aasp r SIG) t1).
      {
        destruct s.
        destruct s; destruct s0.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          ff.

          repeat eexists.
          eauto.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          jkjke'.
          jkjke'.
          repeat ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          repeat ff.
          
          repeat eexists.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
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
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: {eassumption. }
            
            eassumption.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            
            econstructor.
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
      ff.
      
      rewrite fold_recev in *.
      
      jkjke'.
      jkjke'.
      repeat ff.
      do_wfec_preserved.
      do_somerecons.
      
      assert (gg_sub H5 \/ exists r, term_sub (aasp r SIG) t2).
      {
        destruct s.
        destruct s; destruct s0.
        ++
          eapply IHt2.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          ff.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
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
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
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

  - (* abpar case *)

    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
    do_wfec_firstn.
    do_wfec_skipn.
    clear_skipn_firstn.
    repeat find_rewrite.
    vmsts.
    do_ggsub.

    evSubFacts.

    +
      ff.
      rewrite fold_recev in *.
      
      jkjke'.
      jkjke'.
      repeat ff.
      do_wfec_preserved.
      do_somerecons.
      
      assert (gg_sub H5 \/ exists r, term_sub (aasp r SIG) t1).
      {
        destruct s.
        destruct s; destruct s0.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          ff.

          repeat eexists.
          eauto.
        ++
          eapply IHt1.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          jkjke'.
          jkjke'.
          repeat ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          repeat ff.
          
          repeat eexists.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
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
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            2: {eassumption. }
            
            eassumption.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            
            econstructor.
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
      ff.
      
      rewrite fold_recev in *.
      
      jkjke'.
      jkjke'.
      repeat ff.
      do_wfec_preserved.
      do_somerecons.
      
      assert (gg_sub H5 \/ exists r, term_sub (aasp r SIG) t2).
      {
        destruct s.
        destruct s; destruct s0.
        ++
          eapply IHt2.
          eassumption.
          2: { eassumption. }
          eassumption.
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          jkjke'.
          ff.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
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
          eassumption.
          eassumption.
          rewrite fold_recev in *.
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          jkjke'.
          
          econstructor.
          eauto.
        ++
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            2: { eassumption. }
            ff.
            ff.
            eassumption.
            repeat jkjke'.
            repeat ff.
            repeat jkjke'.
            repeat ff.
            econstructor.
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
Defined.

Ltac do_sig_is :=
  match goal with
  | [H: well_formed_r ?t,
        H2: wf_ec ?ecc,
            H6: gg_sub ?e',
                H4: Some ?e = reconstruct_ev ?ecc,
                    H5: Some ?e' = reconstruct_ev ?ecc',
                        H3: copland_compile ?t {| st_ev := ?ecc; st_trace := _; st_pl := _ |} =
                            (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |})

     |- _] =>
    
    assert_new_proof_by
      (gg_sub e \/ (exists r : Range, term_sub (aasp r SIG) t))
      ltac:(eapply sig_is; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
  end.

Ltac do_hsh_subt :=
  unfold hsh_subt in *;
  destruct_conjs;
  subst.

Lemma sig_term_ev_bseql: forall (r : Range) s (t1 t2 : AnnoTerm) (e : EvidenceC) 
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc',
    not_hash_sig_term_ev (abseq r s t1 t2) e ->
    copland_compile t1 {| st_ev := splitEv_l s (evc e0 e1); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->
    Some e = reconstruct_ev (evc e0 e1) ->
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

Lemma sig_term_ev_bseqr: forall (r : Range) s (t1 t2 : AnnoTerm) (e : EvidenceC) 
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc',
    not_hash_sig_term_ev (abseq r s t1 t2) e ->
    copland_compile t2 {| st_ev := splitEv_r s (evc e0 e1); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->
    Some e = reconstruct_ev (evc e0 e1) ->
    not_hash_sig_term_ev t2 (splitEvr s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in H3.
  
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

Lemma sig_term_ev_bparl: forall (r : Range) s (t1 t2 : AnnoTerm) (e : EvidenceC) 
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc',
    not_hash_sig_term_ev (abpar r s t1 t2) e ->
    copland_compile t1 {| st_ev := splitEv_l s (evc e0 e1); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->
    Some e = reconstruct_ev (evc e0 e1) ->
    not_hash_sig_term_ev t1 (splitEvl s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in H3.
  
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

Lemma sig_term_ev_bparr: forall (r : Range) s (t1 t2 : AnnoTerm) (e : EvidenceC) 
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc',
    not_hash_sig_term_ev (abpar r s t1 t2) e ->
    copland_compile t2 {| st_ev := splitEv_r s (evc e0 e1); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->
    Some e = reconstruct_ev (evc e0 e1) ->
    not_hash_sig_term_ev t2 (splitEvr s e).
Proof.
  intros.
  unfold not_hash_sig_term_ev in H.
  destruct_conjs.
  unfold not in H3.
  
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

Lemma not_hste_att: forall t e n0 n1 n,
    not_hash_sig_term_ev (aatt (n0, n1) n t) e ->
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
  eapply H0 with (t':=(alseq (n2, n3) H4 H2)).
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
  do_hsh_subt.
  econstructor.
  eapply termsub_transitive.
  eassumption.
  econstructor.
  econstructor.
Defined.

Ltac do_nhste_att :=
  match goal with
  | [H: not_hash_sig_term_ev (aatt _ _ ?t) ?e

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t e)
      ltac:(eapply not_hste_att; apply H)
  end.

Ltac do_nste_lseq :=
  match goal with
  | [H: not_hash_sig_term_ev (alseq _ ?t1 _) ?e,
        H2: copland_compile ?t1 {| st_ev := ?ec; st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?e = reconstruct_ev ?ec

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 e)
      ltac:(eapply sig_term_ev_lseq; [apply H | apply H2 | apply H3])
  end.

Lemma nhst_lseq_r: forall r t1 t2 e,
    not_hash_sig_term_ev (alseq r t1 t2) e ->
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
  eapply H with (t':= (alseq (n, n0) H4 H2)).
  econstructor.
  repeat eexists.
  eassumption.
  eassumption.
  subst.
  eauto.
Defined.

Ltac do_nhst_lseqr :=
  match goal with
  | [H: not_hash_sig_term_ev (alseq _ _ ?t2) _

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t2)
      ltac:(eapply nhst_lseq_r; [apply H ])
  end.

Ltac do_ste_bseql :=
  match goal with
  | [H: not_hash_sig_term_ev (abseq _ ?s ?t1 _) ?e,
        H2: copland_compile ?t1 {| st_ev := splitEv_l ?s ?ec; st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?e = reconstruct_ev ?ec

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 (splitEvl s e))
      ltac:(eapply sig_term_ev_bseql; [apply H | apply H2 | apply H3])
  end.

Ltac do_ste_bseqr :=
  match goal with
  | [H: not_hash_sig_term_ev (abseq _ ?s _ ?t2) ?e,
        H2: copland_compile ?t1 {| st_ev := splitEv_r ?s ?ec; st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?e = reconstruct_ev ?ec

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 (splitEvr s e))
      ltac:(eapply sig_term_ev_bseqr; [apply H | apply H2 | apply H3])
  end.

Ltac do_ste_bparl :=
  match goal with
  | [H: not_hash_sig_term_ev (abpar _ ?s ?t1 _) ?e,
        H2: copland_compile ?t1 {| st_ev := splitEv_l ?s ?ec; st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?e = reconstruct_ev ?ec

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 (splitEvl s e))
      ltac:(eapply sig_term_ev_bparl; [apply H | apply H2 | apply H3])
  end.

Ltac do_ste_bparr :=
  match goal with
  | [H: not_hash_sig_term_ev (abpar _ ?s _ ?t2) ?e,
        H2: copland_compile ?t1 {| st_ev := splitEv_r ?s ?ec; st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?e = reconstruct_ev ?ec

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 (splitEvr s e))
      ltac:(eapply sig_term_ev_bparr; [apply H | apply H2 | apply H3])
  end.



(*
Ltac do_nhste :=
  try do_nhste_att.
*)

Lemma hshsig_ev_term_contra: forall t p (e e' :EvidenceC) tr tr' p' (ecc ecc':EvC),

    well_formed_r t ->
    wf_ec ecc ->
    not_hash_sig_term_ev t e ->
    
    Some e =  (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->

    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    not_hash_sig_ev e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; repeat ff.
  -
    jkjke'.
    ff.
    unfold not_hash_sig_term_ev in *.
    destruct_conjs.
    eassumption.
  -
    unfold cons_uu in *.
    repeat ff.
    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    eapply not_hshsig_uuc; eauto.
  -
    repeat ff.
    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    (*
    assert (not_hash_sig_ev e).
    {
      eapply not_ev; eauto.
    } *)
    rewrite fold_recev in *.
    assert ((evc (get_bits ecc) (get_et ecc)) = ecc).
    {
      destruct ecc.
      ff.
    }
    rewrite H5 in *; clear H5.
    jkjke'.
    ff. 
    eapply not_hshsig_ggc; eauto.
  -
    assert (not_hash_sig_ev e).
    {
      eapply not_ev; eauto.
    }

    assert (~ (gg_sub e)).
    {
      cbv in H1.
      destruct_conjs.
      unfold not; intros.
      invc H6.
      destruct_conjs.
      subst.
      eapply H5.
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
    eapply H4.
    invc H5.
    destruct_conjs.
    subst.
    invc H6.

    eapply gg_recons; eauto.

    ff.

    edestruct hh_recons.
    eassumption.
    eassumption.

    unfold not_hash_sig_ev in H3.
    unfold not in *.
    exfalso.
    eapply H3.
    econstructor.
    repeat eexists.
    eassumption.
    eassumption.

  - (* aatt case *)
    do_wf_pieces.
    do_nhste_att.
    
    eapply IHt.
    eassumption.
    2: { eassumption. }
    eassumption.
    eassumption.
    eassumption.
    apply copland_compile_at.
    eassumption.
  -
    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.

    ff.
    destruct ecc; destruct st_ev.

    do_nste_lseq.

    assert (not_hash_sig_ev H9) by eauto.

    do_nhst_lseqr.

    assert (not_hash_sig_term_ev t2 H9).
    {
      split.
      eassumption.
      split.
      eassumption.
      intros.
      unfold not.
      intros.

      do_sig_is.

      repeat jkjke';
      repeat ff;
      rewrite fold_recev in *;
      repeat jkjke';
      repeat ff.
      
      door.
      +
        unfold not_hash_sig_term_ev in H1.
        destruct_conjs.
        unfold not in H19.
        eapply H19.
        eassumption.
        do_hsh_subt.
        econstructor.
        eauto.
      +
        do_hsh_subt.
        unfold not_hash_sig_term_ev in H1.
        destruct_conjs.
        unfold not_hash_sig_term in H1.
        unfold not in H1.
        eapply H1 with (t':= (alseq r t1 t2)).
        econstructor.
        repeat eexists.
        eassumption.
        eassumption.
        econstructor.
    }
    
    eapply IHt2.
    eassumption.
    2: { eassumption. }
    2: { eassumption. }
    eassumption.
    eassumption.
    eassumption.
    
  - (* abseq case *)
    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
    do_wfec_firstn.
    do_wfec_skipn.
    clear_skipn_firstn.
    repeat find_rewrite.

    jkjke'.
    jkjke'.
    vmsts.
    ff.
    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
    
    destruct ecc.
    do_ste_bseql.
    do_ste_bseqr.
    
    invc H11.
    +
      invc H2.
      destruct_conjs.
      solve_by_inversion.
    +
      rewrite fold_recev in *.
      do_wfec_preserved.
      do_somerecons.
        
      assert (not_hash_sig_ev H11).
      {
        eapply IHt1.
        eassumption.
        
        4: { eassumption. }
        4: {
          eassumption. }
        eassumption.
        eassumption.
        destruct s; destruct s; destruct s0; ff.

      }
      
      invc H2.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H24.
      unfold not in *.
      eapply H24.
      econstructor.
      repeat eexists.
      eassumption.
      jkjke'.
      jkjke'.
      jkjke'.
      jkjke'.
      repeat ff.

    +
      rewrite fold_recev in *.
      assert (not_hash_sig_ev e5).
      {
        eapply IHt2.
        eassumption.
        
        4: { symmetry. eassumption. }
        4: {
          eassumption. }
        eassumption.
        eassumption.
        destruct s; destruct s; destruct s0; ff.

      }
      
      invc H2.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H11.
      unfold not in *.
      eapply H11.
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.

  - (* abpar case *)
    do_wf_pieces.
    vmsts.
    do_wfec_preserved.
    do_somerecons.
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
    do_wfec_firstn.
    do_wfec_skipn.
    clear_skipn_firstn.
    repeat find_rewrite.

    jkjke'.
    jkjke'.
    vmsts.
    ff.
    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
    destruct ecc.
    do_ste_bparl.
    do_ste_bparr.
    
    invc H11.
    +
      invc H2.
      destruct_conjs.
      solve_by_inversion.
    +
      rewrite fold_recev in *.
      do_wfec_preserved.
      do_somerecons.
          
      assert (not_hash_sig_ev H11).
      {
        eapply IHt1.
        eassumption.
        
        4: { eassumption. }
        4: {
          eassumption. }
        eassumption.
        eassumption.
        destruct s; destruct s; destruct s0; ff.

      }
      
      invc H2.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H24.
      unfold not in *.
      eapply H24.
      econstructor.
      repeat eexists.
      eassumption.
      jkjke'.
      jkjke'.
      jkjke'.
      jkjke'.
      repeat ff.

    +
      rewrite fold_recev in *.
      assert (not_hash_sig_ev e5).
      {
        eapply IHt2.
        eassumption.
        
        4: { symmetry. eassumption. }
        4: {
          eassumption. }
        eassumption.
        eassumption.
        destruct s; destruct s; destruct s0; ff.

      }
      
      invc H2.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H11.
      unfold not in *.
      eapply H11.
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.
Defined.

(*
Lemma hshsig_ev_term_contra: forall t p (e e' :EvidenceC) tr tr' p' (ecc ecc':EvC),

    well_formed_r t ->
    wf_ec ecc ->
    not_hash_sig_term_ev t e ->
    
    Some e =  (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->

    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    not_hash_sig_ev e'.
Proof.
*)

Ltac do_hste_contra :=
  match goal with
  | [H: well_formed_r ?t,
        H2: wf_ec ?ecc,
            H3: not_hash_sig_term_ev ?t ?e,
                H4: Some ?e = reconstruct_ev ?ecc,
                    H5: Some ?e' = reconstruct_ev ?ecc',
                        H6: copland_compile ?t {| st_ev := ?ecc; st_trace := _; st_pl := _ |} =
                            (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |})

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply hshsig_ev_term_contra; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
  end.

(*
Ltac do_nste :=
  try do_nste_lseq.
*)

Lemma sig_term_ev_lseqr: forall r t1 t2 e e0 e1 e2 e3 tr tr' p p' H5,
    well_formed_r t1 ->
    wf_ec (evc e0 e1) ->
    not_hash_sig_term_ev (alseq r t1 t2) e ->
    copland_compile t1 {| st_ev := evc e0 e1; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := evc e2 e3; st_trace := tr'; st_pl := p' |}) ->
    Some e  = reconstruct_ev (evc e0 e1) ->
    Some H5 = reconstruct_ev (evc e2 e3) ->
    not_hash_sig_term_ev t2 H5.
Proof.
  intros.
  
  do_nste_lseq.
  do_nhst_lseqr.

  split; try eassumption.

  do_hste_contra.

  -
    split; try eassumption.
    (*
    +
      eapply hshsig_ev_term_contra; eauto. *)
    +

      intros.
      unfold not; intros.

      do_sig_is.
      door.

      ++

      

      (*
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption. *)


      (*
      edestruct sig_is; eauto. *)
      unfold not_hash_sig_term_ev in H1.
      destruct_conjs.
      concludes.
      unfold not in *.
      do_hsh_subt.
      forwards;
        eauto.
      ++
        

      unfold not_hash_sig_term_ev in H1.
      destruct_conjs.
      unfold not_hash_sig_term in H1.
      unfold not in *.
      do_hsh_subt.
      eapply H1; eauto.
      econstructor.
      repeat eexists.
      eauto.
      eauto.
Defined.

(*
Lemma sig_term_ev_lseqr: forall r t1 t2 e e0 e1 e2 e3 tr tr' p p' H5,
    well_formed_r t1 ->
    wf_ec (evc e0 e1) ->
    not_hash_sig_term_ev (alseq r t1 t2) e ->
    copland_compile t1 {| st_ev := evc e0 e1; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := evc e2 e3; st_trace := tr'; st_pl := p' |}) ->
    Some e  = reconstruct_ev (evc e0 e1) ->
    Some H5 = reconstruct_ev (evc e2 e3) ->
    not_hash_sig_term_ev t2 H5.
Proof.
*)

Ltac do_evsub_ihhh' :=
  match goal with
  | [H: copland_compile ?t1
                        {| st_ev := ?ee; st_trace := _; st_pl := _ |} =
        (Some tt, {| st_ev := ?stev; st_trace := _; st_pl := _ |}),
        
        (* H2: copland_compile ?t2
                            {| st_ev := _(*?stev'*); st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}), *)
        H3: Some _ = reconstruct_ev ?ee,
            H4: Some ?v' = reconstruct_ev ?stev,
                IH: forall _, _ -> _ ,(*context[forall _, well_formed_r ?t1 -> _], *)
       Hf: well_formed_r ?t1,
       Hnn: not_none_none ?t1,
       Hwf: wf_ec ?ee,
       Hev: events ?t1 _ _ _
                   

       |-  (exists e'' : EvidenceC, EvSub (uuc ?i ?args ?tpl ?tid ?n e'') _) \/
          (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
              EvSub (hhc p'0 bs ett) _ /\ EvSubT (uu ?i ?args ?tpl ?tid et') ett)
            (*context[EvSub _(*(uuc ?i ?args ?tpl ?tid ?n _)*) _ \/ _]*)
    ] => 

    

    assert_new_proof_by 
      (
        (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') v') \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) v' /\ EvSubT (uu i args tpl tid et') ett)
      )

      (*
          assert_new_proof_by
            (exists ee, EvSub (uuc i args tpl tid n ee) v \/
             (exists (ett : Evidence) (p'0 bs : nat) (et':Evidence),
                 EvSub (hhc p'0 bs ett) v /\ EvSubT (uu i args tpl tid et') ett)) 
       *)
      ltac: (eapply IH; [apply Hf | apply Hnn| apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
              (*ltac:(ff; repeat jkjke'; eauto)*)
              
              
  end.

Lemma uu_preserved': forall t p et n p0 i args tpl tid
                       e tr e' tr' p' ecc ecc',

    well_formed_r t ->
    not_none_none t ->
    wf_ec ecc ->
    Some e = (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->
    events t p et (umeas n p0 i args tpl tid) ->
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid et') ett)
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff.
    +
      inv_events.
      ff.
      unfold cons_uu in *.
      repeat ff.
      left.
      eexists.
      econstructor.
  -
    ff.
    invEvents.
    do_wf_pieces.
    do_not_none.

    eapply IHt; eauto.
    apply copland_compile_at; eauto.
  -
    do_wf_pieces.
    do_not_none.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)
      
      do_wfec_preserved.
      do_somerecons.

      repeat do_evsub_ihhh'.

      door.
      ++
        destruct_conjs.

        repeat jkjke'.
        repeat ff.

        do_evaccum.

        (*
        clear H12. *)
        door.
        +++
          left.
          eauto.
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).

      ++
        repeat jkjke'.
        repeat ff.
        
        do_evaccum.

        door.
        +++
          right.
          repeat (eexists; eauto).
        +++
          destruct_conjs.
          ff.
          right.
          repeat eexists.
          eauto.

          eapply evsubT_transitive.
          eapply hhSubT.
          eassumption.
          eassumption.
          
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      do_wfec_preserved.
      do_somerecons.

      repeat do_evsub_ihhh'.

      clear H17.
      door.
      ++
        eauto.
      ++
        destruct_conjs;
          right;
          repeat (eexists; eauto).


  - (* abseq case *)
    do_wf_pieces.
    do_not_none.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons;
        do_evsub_ihhh';

        door; repeat jkjke'; ff;
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).

  - (* abpar case *)
    do_wf_pieces.
    do_not_none.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons;
        do_evsub_ihhh';

        door; repeat jkjke'; ff;
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
Defined.


Lemma uu_preserved: forall t1 t2 p et n p0 i args tpl tid
                      e tr st_ev st_trace p'
                      e' tr' p'' ecc,
    well_formed_r t1 ->
    well_formed_r t2 ->
    not_none_none t1 ->
    not_none_none t2 ->
    wf_ec e ->
    Some e' = (reconstruct_ev ecc) ->
    events t1 p et (umeas n p0 i args tpl tid) ->
    copland_compile t1 {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |}) ->
    
    copland_compile t2
                    {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |} =
    (Some tt, {| st_ev := ecc; st_trace := tr'; st_pl := p'' |}) ->

    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid et') ett)
    ).
Proof.
  intros.

  ff.
  do_wfec_preserved.
  do_somerecons.
  
  assert (
      (exists e'', EvSub (uuc i args tpl tid n e'') H11) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) H11 /\
          EvSubT (uu i args tpl tid et') ett)
    ).
  {
    eapply uu_preserved'.
    apply H.
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
    
    clear H18.
    door; eauto.

    right;
      (repeat eexists; eauto).
  +
    clear H22.
    door; ff.
    ++
      right;
        repeat (eexists; eauto).

    ++
      assert (EvSubT (uu i args tpl tid H19) H22).
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
  | [H: well_formed_r ?t,
        H2: wf_ec ?ecc,
            H3: not_hash_sig_term_ev (alseq _ ?t1 ?t2) ?e,
                H5: Some ?e = reconstruct_ev ?ecc,
                    H6: Some ?e' = reconstruct_ev ?ecc',
                        H4: copland_compile ?t1 {| st_ev := ?ecc; st_trace := _; st_pl := _ |} =
                            (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |})

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 e')
      ltac:(eapply sig_term_ev_lseqr; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
  end.

Ltac do_ste :=
  try do_nhste_att;
  try do_nste_lseq;
  try do_nhst_lseqr;
  try do_nhste_lseqr;
  try do_ste_bseql;
  try do_ste_bseqr;
  try do_ste_bparl;
  try do_ste_bparr;
  try do_hste_contra.

Ltac sigEventFacts :=
  match goal with
  | [H: sigEvent _ _ _ _ |- _] => invc H
  end.

Ltac sigEventPFacts :=
  match goal with
  | [H: sigEventP _ |- _] => invc H
  end.

Lemma nhse_bseql_nosplit: forall t1 t2 ecc ecc' r s tr tr' p p' e e' H19,
    well_formed_r t1 ->
    wf_ec ecc ->
    wf_ec (splitEv_l s ecc) -> 
    not_hash_sig_term_ev (abseq r s t1 t2) H19 ->
    copland_compile t1
                    {|
                      st_ev := splitEv_l s ecc;
                      st_trace := tr;
                      st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    
    Some H19 = reconstruct_ev ecc ->
    Some e = reconstruct_ev (splitEv_l s ecc) ->
    Some e' = reconstruct_ev ecc' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  6: { eassumption. }
  eassumption.
  eassumption.
  eapply sig_term_ev_bseql.
  eassumption.
  eassumption.
  eassumption.
  
  destruct s; destruct s; destruct s0; ff.
  eassumption.
Defined.

Ltac do_nhse_bseql_nosplit :=
  match goal with
  | [H: well_formed_r ?t1,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_l ?s ?ecc),
                H4: not_hash_sig_term_ev (abseq _ ?s ?t1 _) ?H19,
                    H6: Some ?H19 = reconstruct_ev ?ecc,
                        H7: Some ?e = reconstruct_ev (splitEv_l ?s ?ecc),
                            H8: Some ?e' = reconstruct_ev ?ecc',
                                H5: copland_compile ?t1 {| st_ev := splitEv_l ?s ?ecc; st_trace := _; st_pl := _ |} =
                                    (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |})

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseql_nosplit; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.

Lemma nhse_bseqr_nosplit: forall t1 t2 ecc ecc' r s tr tr' p p' e e' H19,
    well_formed_r t2 ->
    wf_ec ecc ->
    wf_ec (splitEv_r s ecc) -> 
    not_hash_sig_term_ev (abseq r s t1 t2) H19 ->
    copland_compile t2
                    {|
                      st_ev := splitEv_r s ecc;
                      st_trace := tr;
                      st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    
    Some H19 = reconstruct_ev ecc ->
    Some e = reconstruct_ev (splitEv_r s ecc) ->
    Some e' = reconstruct_ev ecc' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  6: { eassumption. }
  eassumption.
  eassumption.
  eapply sig_term_ev_bseqr.
  eassumption.
  eassumption.
  eassumption.
  
  destruct s; destruct s; destruct s0; ff.
  eassumption.
Defined.

Ltac do_nhse_bseqr_nosplit :=
  match goal with
  | [H: well_formed_r ?t2,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_r ?s ?ecc),
                H4: not_hash_sig_term_ev (abseq _ ?s _ ?t2) ?H19,
                    H6: Some ?H19 = reconstruct_ev ?ecc,
                        H7: Some ?e = reconstruct_ev (splitEv_r ?s ?ecc),
                            H8: Some ?e' = reconstruct_ev ?ecc',
                                H5: copland_compile ?t2 {| st_ev := splitEv_r ?s ?ecc; st_trace := _; st_pl := _ |} =
                                    (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |})

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseqr_nosplit; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.

Lemma nhse_bparl_nosplit: forall t1 t2 ecc ecc' r s tr tr' p p' e e' H19,
    well_formed_r t1 ->
    wf_ec ecc ->
    wf_ec (splitEv_l s ecc) -> 
    not_hash_sig_term_ev (abpar r s t1 t2) H19 ->
    copland_compile t1
                    {|
                      st_ev := splitEv_l s ecc;
                      st_trace := tr;
                      st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    
    Some H19 = reconstruct_ev ecc ->
    Some e = reconstruct_ev (splitEv_l s ecc) ->
    Some e' = reconstruct_ev ecc' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  6: { eassumption. }
  eassumption.
  eassumption.
  eapply sig_term_ev_bparl.
  eassumption.
  eassumption.
  eassumption.
  
  destruct s; destruct s; destruct s0; ff.
  eassumption.
Defined.

Ltac do_nhse_bparl_nosplit :=
  match goal with
  | [H: well_formed_r ?t1,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_l ?s ?ecc),
                H4: not_hash_sig_term_ev (abpar _ ?s ?t1 _) ?H19,
                    H6: Some ?H19 = reconstruct_ev ?ecc,
                        H7: Some ?e = reconstruct_ev (splitEv_l ?s ?ecc),
                            H8: Some ?e' = reconstruct_ev ?ecc',
                                H5: copland_compile ?t1 {| st_ev := splitEv_l ?s ?ecc; st_trace := _; st_pl := _ |} =
                                    (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |})

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bparl_nosplit; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.

Lemma nhse_bparr_nosplit: forall t1 t2 ecc ecc' r s tr tr' p p' e e' H19,
    well_formed_r t2 ->
    wf_ec ecc ->
    wf_ec (splitEv_r s ecc) -> 
    not_hash_sig_term_ev (abpar r s t1 t2) H19 ->
    copland_compile t2
                    {|
                      st_ev := splitEv_r s ecc;
                      st_trace := tr;
                      st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    
    Some H19 = reconstruct_ev ecc ->
    Some e = reconstruct_ev (splitEv_r s ecc) ->
    Some e' = reconstruct_ev ecc' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  6: { eassumption. }
  eassumption.
  eassumption.
  eapply sig_term_ev_bparr.
  eassumption.
  eassumption.
  eassumption.
  
  destruct s; destruct s; destruct s0; ff.
  eassumption.
Defined.

Ltac do_nhse_bparr_nosplit :=
  match goal with
  | [H: well_formed_r ?t2,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_r ?s ?ecc),
                H4: not_hash_sig_term_ev (abpar _ ?s _ ?t2) ?H19,
                    H6: Some ?H19 = reconstruct_ev ?ecc,
                        H7: Some ?e = reconstruct_ev (splitEv_r ?s ?ecc),
                            H8: Some ?e' = reconstruct_ev ?ecc',
                                H5: copland_compile ?t2 {| st_ev := splitEv_r ?s ?ecc; st_trace := _; st_pl := _ |} =
                                    (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |})

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bparr_nosplit; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.


Ltac do_nhse_nosplit :=
  try do_nhse_bseql_nosplit;
  try do_nhse_bseqr_nosplit;
  try do_nhse_bparl_nosplit;
  try do_nhse_bparr_nosplit.

Lemma gg_preserved': forall t p et n p0 et'
                       tr e e' tr' p' bits ecc',

    well_formed_r t ->
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    wf_ec (evc bits et) ->
    Some e = (reconstruct_ev (evc bits et)) ->
    Some e' = (reconstruct_ev ecc') ->
    events t p et (sign n p0 et') ->
    copland_compile t {| st_ev := (evc bits et); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    (
      (exists bits e'', EvSub (ggc p0 (do_sig (MonadVM.encodeEv (evc bits et')) p0) e'') e' /\
                   et_fun e'' = et'
      )
    ).
Proof.

  intros.
  generalizeEverythingElse t.
  
  induction t; intros.
  -
    subst.
    destruct a; try (ff; tauto).
    +
      ff.
      invEvents.
      ff.

      repeat eexists.
      econstructor.
      rewrite fold_recev in *.
      symmetry.
      
      eapply etfun_reconstruct; eauto.

  - (* aatt case *)
    ff.
    invEvents.
    do_wf_pieces.
    do_not_none.

    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    (*
    invc H1. *)
    
    do_not_hshsig.

    eapply IHt; eauto.
    econstructor.
    eassumption.
    split; try eassumption.
    intros.
    unfold not in *; intros.
    do_hsh_subt.
    do_ggsub.
    (*
    invc H11. *)
    
    eapply H8.
    econstructor.
    repeat eexists.
    eassumption.
    econstructor.
    econstructor.
    eassumption.
    apply copland_compile_at; eauto.
  - (* alseq case *)
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)
      
      do_wfec_preserved.
      do_somerecons.

      jkjke'.
      jkjke'.
      repeat ff.
      jkjke'.
      ff.
     
      rewrite fold_recev in *.
      destruct ecc'; destruct st_ev.

      do_ste.
      
      edestruct IHt1.
      eassumption.
      eassumption.
      (*
      eapply sig_term_ev_lseq; eassumption. *)
      eassumption.
      4: { eassumption. }
      eassumption.
      eassumption.
      2: { eassumption. }
      eassumption.

      destruct_conjs.

      repeat jkjke'.
      repeat ff.
      repeat jkjke'.
      repeat ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.

      do_evaccum.

      door.
      +++
        eauto.
      +++
        ff.
        
        unfold not_hash_sig_ev in H19.
        specialize H19 with (e':=(hhc H24 H25 H23)).
        unfold not in *.
        exfalso.
        apply H19.
        econstructor.
        repeat eexists.
        eassumption.
        eassumption.       
        
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      do_wfec_preserved.
      do_somerecons.
      destruct st_ev.
      destruct ecc'.

      assert (e1 = (aeval t1 p et)).
      {
        rewrite <- eval_aeval.
        eapply cvm_refines_lts_evidence.
        eassumption.
        eassumption.
      }
      subst.

      rewrite fold_recev in *.
      repeat jkjke'.
      repeat ff.
      rewrite fold_recev in *.

      repeat do_ste.

      edestruct IHt2.
      eassumption.
      eassumption.
      (*
      eapply sig_term_ev_lseqr. *)
      eassumption.
      (*
      apply H2. *)
      4: { eassumption. }
      eassumption.
      eassumption.
      2: { eassumption. }
      eassumption.

      (*
      eassumption.
      2: { eassumption. }
      eassumption.
      2: { eassumption. }
      2: { eassumption. }
      eassumption. *)
      eauto.

      
  - (* abseq case *)
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons;
        try do_evsub_ihhh'.

    +

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.
      repeat rewrite fold_recev in *.

      do_nhse_nosplit.  
      
      destruct s; destruct s; destruct s0; ff;
        rewrite fold_recev in *;
        
        
        try(
        edestruct IHt1;
        
        [apply H7 | apply H9
         | eapply sig_term_ev_bseql; [apply H1 | apply Heqp0 | apply H30]
         | apply H2 | apply H30 | apply H34 | apply H16 | apply Heqp0 | idtac]);

        try
          (
            edestruct IHt1;
        
            [apply H7 | apply H9
             | eapply sig_term_ev_bseql; [apply H1 | apply Heqp0 | apply H30]
             | apply H4 | (ff; tauto) | apply H34 | apply H16 | apply Heqp0 | idtac]);
        destruct_conjs; eauto.

    +

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.
      repeat rewrite fold_recev in *.

      do_nhse_nosplit.
      
      destruct s; destruct s; destruct s0; ff;
        rewrite fold_recev in *;
        
        
        try(
        edestruct IHt2;
        
        [apply H8 | apply H10
         | eapply sig_term_ev_bseqr; [apply H1 | apply Heqp5 | apply H30]
         | apply H2 | apply H30 | apply H33 | apply H16 | apply Heqp5 | idtac]);
        

        try
          (
            edestruct IHt2;
        
            [apply H8 | apply H10
             | eapply sig_term_ev_bseqr; [apply H1 | apply Heqp5 | apply H30]
             | apply H5 | (ff; tauto) | apply H33 | apply H16 | apply Heqp5 | idtac]);
        destruct_conjs; eauto.


  - (* abpar case *)
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons;
        try do_evsub_ihhh'.

    +

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.
      repeat rewrite fold_recev in *.

      do_nhse_nosplit.  
      
      destruct s; destruct s; destruct s0; ff;
        rewrite fold_recev in *;
        
        
        try(
        edestruct IHt1;
        
        [apply H7 | apply H9
         | eapply sig_term_ev_bparl; [apply H1 | apply Heqp0 | apply H30]
         | apply H2 | apply H30 | apply H34 | apply H16 | apply Heqp0 | idtac]);

        try
          (
            edestruct IHt1;
        
            [apply H7 | apply H9
             | eapply sig_term_ev_bparl; [apply H1 | apply Heqp0 | apply H30]
             | apply H4 | (ff; tauto) | apply H34 | apply H16 | apply Heqp0 | idtac]);
        destruct_conjs; eauto.

    +

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.
      repeat rewrite fold_recev in *.

      do_nhse_nosplit.
      
      destruct s; destruct s; destruct s0; ff;
        rewrite fold_recev in *;
        
        
        try(
        edestruct IHt2;
        
        [apply H8 | apply H10
         | eapply sig_term_ev_bparr; [apply H1 | apply Heqp5 | apply H30]
         | apply H2 | apply H30 | apply H33 | apply H16 | apply Heqp5 | idtac]);
        

        try
          (
            edestruct IHt2;
        
            [apply H8 | apply H10
             | eapply sig_term_ev_bparr; [apply H1 | apply Heqp5 | apply H30]
             | apply H5 | (ff; tauto) | apply H33 | apply H16 | apply Heqp5 | idtac]);
        destruct_conjs; eauto.
Defined.

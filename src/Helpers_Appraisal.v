Require Import ConcreteEvidence Appraisal_Defs StVM Impl_vm Impl_appraisal Auto AutoApp External_Facts MonadVM Helpers_VmSemantics VmSemantics.

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

Lemma uuc_app: forall e' e'' i args tpl tid p n,
    EvSub (uuc i args tpl tid p n e'') e' ->
    exists e'', EvSub (uuc i args tpl tid p (checkASPF i args tpl tid n) e'')
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
    EvSub (hhc p (fromSome 0 (checkHash et p bs)) et)
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
    | [H: context [well_formed_r ?t -> _](*
                   wf_ec _ ->
                   copland_compile _ _ _ = _ ->
                   wf_ec _]*),
          H2: well_formed_r ?t,
              H3: wf_ec ?e,
                  H4: copland_compileP ?t
                                       {| st_ev := ?e; st_trace := _; st_pl := _ |}
                                       (_)
                                       {| st_ev := ?e'; st_trace := _; st_pl := _ |}
       |- _ ] => 
      assert_new_proof_by
        (wf_ec e')
        
        ltac:(eapply H; [apply H2 | apply H3 | apply H4])
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
    copland_compileP t1
                    {| st_ev := e; st_trace := tr; st_pl := p |}
                    (Some tt)
                    {| st_ev := e'; st_trace := tr'; st_pl := p' |} ->
    wf_ec (e').
Proof.
  intros.
  generalizeEverythingElse t1.
  induction t1; intros.
  -
    rewrite <- ccp_iff_cc in *.
    destruct a; ff;
      invc H0;
      try (
          econstructor;
          ff;
          try tauto;
          try congruence).  
  -
    rewrite <- ccp_iff_cc in *.
    dd.
    do_wf_pieces.

    eapply wf_ec_preserved_remote; eauto.

  -
    do_wf_pieces.
    rewrite <- ccp_iff_cc in *.
    dd.
    rewrite ccp_iff_cc in *.
    eauto.
  -
    do_wf_pieces.
    rewrite <- ccp_iff_cc in *.
    dd.
    rewrite ccp_iff_cc in *.

    do_wfec_split.
        find_wfec;
      inv_wfec;
      dd;
      econstructor;
      dd; repeat jkjke';
        eapply app_length.

  -
    do_wf_pieces.

    rewrite <- ccp_iff_cc in *.
    dd.
    rewrite ccp_iff_cc in *.
    (*
    repeat ff; vmsts; subst.
    do_wf_pieces.
     *)
    

    do_wfec_split.

    find_wfec;
      inv_wfec;
      ff;
      econstructor;
      dd;
      repeat jkjke'.

    erewrite app_length.

    assert (wf_ec (evc e2 e3)).
    {
      rewrite par_evidence in Heqe2.
      rewrite <- at_evidence in Heqe2.
      rewrite <- Heqe2.
      eapply wf_ec_preserved_remote.
      econstructor.
      eassumption.
      eassumption.
    }

    solve_by_inversion.
Defined.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [H: well_formed_r ?t,
          H2: wf_ec ?stev,
              H3: copland_compileP ?t
                                   {| st_ev := ?stev; st_trace := _; st_pl := _ |}
                                   (Some tt)
                                   {| st_ev := ?stev'; st_trace := _; st_pl := _ |}
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [apply H | apply H2 | apply H3])
                                 
    end.



Ltac do_evsub_ih :=
  match goal with
  | [H: copland_compileP ?t1
                         {| st_ev := _; st_trace := _; st_pl := _ |}
                         (Some tt)
                         {| st_ev := ?stev; st_trace := _; st_pl := _ |},
        
   (*     H2: copland_compileP ?t2
                             {| st_ev := ?stev'; st_trace := _; st_pl := _ |}
                             (Some tt)
                             {| st_ev := _; st_trace := _; st_pl := _ |}, *)
            H3: reconstruct_evP ?stev ?v (*Some ?v = reconstruct_ev ?stev *)

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

Lemma evsubt_preserved: forall t pt e e' et et' tr tr' p p' ett,
    well_formed_r_annt t ->
    not_none_none t ->
    anno_parP pt t 0 ->
    copland_compileP pt
                     {| st_ev := evc e et; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := evc e' et'; st_trace := tr'; st_pl := p' |} ->
    EvSubT ett et ->
    EvSubT ett et'.
Proof.
  intros.

  (*

  assert (exists l' t', anno_par t 0 = (l',t')).
  {
    destruct (anno_par t 0).
    repeat eexists.
  }
  destruct_conjs.
   *)

  destruct (anno_par t 0) eqn:hi.
  
  assert (t = (unannoPar pt)).
  {
    inversion H1.
    erewrite anno_unanno_par.
    reflexivity.
    rewrite hi in *.
    simpl in H4.
    subst.
    tauto.
    (*
    rewrite <- H4 in *.
    eassumption.
    invc H1.
    eassumption. *)
  }
  (*
  subst.
  unfold annotated_par in *.
  rewrite H5 in *.
  simpl in H1.
   *)
  

  assert (et' = eval (unanno t) p et).
  {
    rewrite H4.
    Check cvm_refines_lts_evidence.
    eapply cvm_refines_lts_evidence.
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    eassumption.
    eassumption.
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
    exists (uuc n l n0 n1 n2 1 IHy).
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

Lemma not_hshsig_uuc: forall e' n l n1 n2 p x,
    not_hash_sig_ev e' ->
    not_hash_sig_ev (uuc n l n1 n2 p x e').
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

Ltac do_rewrap_reconP :=
  match goal with
  | [H: reconstruct_evP (evc _ (?cc _)) _
     |- _] =>
    invc H;
    repeat ff;
    try rewrite fold_recev in *;
    do_wrap_reconP
  end.

Lemma reconP_determ: forall ec e e',
    reconstruct_evP ec e ->
    reconstruct_evP ec e' ->
    e = e'.
Proof.
  intros.
  invc H; invc H0.
  repeat jkjke'.
  ff.
Defined.

Ltac do_reconP_determ :=
  repeat 
  match goal with
  | [H: reconstruct_evP ?ec ?e,
        H2: reconstruct_evP ?ec ?e2
     |- _] =>
    assert_new_proof_by (e = e2)
                        ltac:(eapply reconP_determ; [apply H | apply H2]);
    clear H2
  end; subst.

Lemma anno_parP_redo: forall t pt loc loc',
    anno_par t loc = (loc', pt) ->
    anno_parP pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Defined.

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac inv_annoparP :=
  match goal with
  | [H: anno_parP ?t (?c _) _
     |- _ ] =>
    inversion H
  end.


Ltac wrap_ccp :=
  
  try rewrite <- ccp_iff_cc in *;
  try inv_annoparP;
  dd;
  repeat do_annopar_redo;
  do_wf_pieces;
  repeat do_pl_immut;
  dd;
  try rewrite ccp_iff_cc in *.

Ltac do_t_at_zero t x :=
  let y := fresh in
  assert (exists l' t', anno_par t 0 = (l',t')) as y by
        (destruct (anno_par t 0); repeat eexists);
  destruct y;
  destruct y as [x].

Ltac do_assert_remote t e p :=
  assert (
      copland_compile t
                      {| st_ev := e; st_trace := []; st_pl := p|} =
      (Some tt,
       {| st_ev := toRemote (unannoPar t) p e;
                   st_trace := remote_events (unannoPar t) p;
                               st_pl := p
       |})
    ) by
    (eapply copland_compile_at;
     eapply wfr_annt_implies_wfr_par;
     [eassumption | econstructor; jkjke]).

Ltac do_assert_unannoPar t x :=
  assert (t = unannoPar x) by
    (erewrite anno_unanno_par;
     [reflexivity | eassumption]).

Ltac do_assume_remote t e p x :=
  do_t_at_zero t x;
  do_assert_remote x e p;
  do_assert_unannoPar t x.

Lemma evAccum: forall t pt p (e e' e'':EvidenceC) tr tr' p' (ecc ecc':EvC) loc,

    (*
    well_formed_r_annt t ->
     *)
    anno_parP pt t loc ->
    well_formed_r pt ->
    not_none_none t ->
    wf_ec ecc ->

    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' ->

    (*
    Some e =  (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->
     *)
    
    EvSub e'' e ->
    copland_compileP (pt)
                     {| st_ev := ecc; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->

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
      (*try jkjke'; *)
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
      do_reconP_determ.

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

    wrap_ccp.
    do_not_none.

    (*
    
    do_wf_pieces.
    do_not_none.
    rewrite <- ccp_iff_cc in *.
    inversion H2.
    dd.
    (*
    ff.
    repeat break_let.
    simpl. *)
     *)

    do_assume_remote t ecc n HHH.
    
    

    (*

    assert (exists l' t', anno_par t 0 = (l',t')).
    {
      destruct (anno_par t 0).
      repeat eexists.
    }
    destruct_conjs.


    assert (t = unannoPar H9).
    {
    erewrite anno_unanno_par.
    reflexivity.
    eassumption.
    }
     *)
    
     

    
    
    

    
    eapply IHt.

    (*
    eassumption.
    eassumption. *)


    (*

    5: {
      eassumption.
    }
    5: {
      eassumption.
    }
    3: {
      eassumption.
    }
    eassumption.
    econstructor.
    rewrite H11.
    tauto
    
    
    
      econstructor.
      find_rewrite.
      reflexivity.
    }
    3: {
      eassumption.
    }
    3: {
      eassumption.
    }
    
    
    2: {
      eassumption. }
    eassumption.

(*
    2: {
      
      eassumption. }
    2: {
      eassumption. }
    eassumption.
    rewrite H9.
 *)
    
     *)

    8: {
      econstructor.
      eassumption.

      (*

      rewrite <- ccp_iff_cc.
      eapply copland_compile_at.
      
      
      eapply wfr_annt_implies_wfr_par.
      eassumption.
      econstructor.
      reflexivity.
      (*
      rewrite H10.
      tauto. *)
       *)
      
    }
    econstructor. rewrite H8. tauto.
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    do_annopar_redo. eassumption.
    
    eassumption.
    eassumption.
    eassumption.
    rewrite <- H10.
    eassumption.
    eassumption.

  - (* alseq case *)

    wrap_ccp.

    (*
    specialize IHt1 with (loc:=loc).
    specialize IHt2 with (loc:=l).
     *)
    

    do_wfec_preserved.

    do_somerecons.

    do_not_none.

    do_reconP_determ.
    
    do_evsub_ih.
    
    door.
    +
      eapply IHt2 with (ecc:=st_ev0).
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      (*
      rewrite Heqp1 in *.
      invc H15. *)
      eassumption.
    +
      do_evsubh_ih.
      
      door.
      ++
        right.
        repeat (eexists; eauto).
      ++
        (*
        destruct_conjs.
        ff. *)
        
        right.
        repeat (eexists; eauto).
        simpl in *.
        (*
        simpl in H30. *)
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

    (*
    specialize IHt1 with (loc := loc).
    (*
    find_rewrite. *)

    specialize IHt2 with (loc:=l).
    (*
    find_rewrite. *)
     *)
    
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
      do_assume_remote t2 ecc p HHH.

      edestruct IHt2.
      8: {
        econstructor.
        eassumption. }

      econstructor. rewrite H14. tauto.
      
      eapply wfr_annt_implies_wfr_par.
      eassumption.
      econstructor. rewrite H14. tauto.
     
      eassumption.
      eassumption.
     
      eassumption.
      rewrite <- Heqe2 in *.
      rewrite par_evidence in *.
      rewrite at_evidence in *.
      rewrite <- H20.
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

Ltac do_evaccum :=
  repeat 
    match goal with
    | [ H: well_formed_r ?pt,
           H2: wf_ec ?ecc,
               H3: reconstruct_evP ?ecc ?e,
                   H4: reconstruct_evP ?ecc' ?e',
                       H5: EvSub ?e'' ?e,
                           H6: copland_compileP ?pt
                                                {| st_ev := ?ecc; st_trace := _; st_pl := _ |}
                                                (Some tt)
                                                {| st_ev := ?ecc'; st_trace := _; st_pl := _ |},
                               H7: not_none_none ?t,
                                   H8: anno_parP ?pt ?t _

        |- _] =>
      
      assert_new_proof_by
        (EvSub e'' e' \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett))
        ltac: (eapply evAccum; [apply H8 | apply H | apply H7 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
    end.



Lemma sig_term_ev_lseq: forall r t1 t2 e (*e0 e1 e2 e3 tr tr' p p' loc*),
    not_hash_sig_term_ev (alseq r t1 t2) e ->
    (*
    copland_compileP (snd (anno_par t1 loc))
                     {| st_ev := evc e0 e1; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := evc e2 e3; st_trace := tr'; st_pl := p' |} ->
    Some e  = reconstruct_ev (evc e0 e1) ->
     *)
    
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

    (*
    unfold not.
    intros.
    destruct_conjs.
    unfold hsh_subt in *.
    destruct_conjs.
    find_eapply_hyp_hyp.
    econstructor.
    eauto. *)
Defined.


Lemma sig_is: forall t pt ecc ecc' e e' tr tr' p p' loc,

    anno_parP pt t loc ->
    well_formed_r pt ->
    wf_ec ecc ->
    copland_compileP pt
                     {| st_ev := ecc; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->

    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' ->

    gg_sub e' ->

    gg_sub e \/
    exists r, term_sub (aasp r SIG) t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ff.
  -
    wrap_ccp.
    (*
    rewrite <- ccp_iff_cc in *.
    inversion H.
     *)
    
    
    destruct a; dd.
    +
      do_reconP_determ.
      eauto.
    (*
      ff.
    jkjke'.
    ff. *)
    +
      unfold cons_uu in *.
      repeat ff.
      Print do_inv_recon_gg.
      Print do_recon_inv_gg.
      Print do_recon_inv_uu.

      do_rewrap_reconP.


      (*

      Ltac do_inv_recon_uu' :=
        match goal with
        | H:reconstruct_evP (evc _ (?c _ )) _
          |- _ => invc H
        end; repeat ff.

      do_inv_recon_uu'.
      rewrite fold_recev in *.
      do_wrap_reconP.
      Print
      do_wrap_reconP.

      Ltac do_wrap :=
        match goal with
        | H:reconstruct_evP (evc _ (?c _ )) _
          |- _ => invc H
        end; repeat ff.
      
      

      Print do_inv_recon_mt'.
       
      

      invc H4.
      repeat ff.
      
      do_annopar_redo.
       *)

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
      do_rewrap_reconP.
      do_ggsub.
      evSubFacts.
  - (* aatt case *)
    wrap_ccp.
    (*
    inversion H.
    rewrite <- ccp_iff_cc in *.
    dd.
    do_wf_pieces.
     *)
    

    edestruct IHt.
    econstructor.
    reflexivity.
    Search "implies".
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    econstructor.
    tauto.
    

    
    eassumption.

    rewrite <- ccp_iff_cc.

    apply copland_compile_at.
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    econstructor. tauto.
    eassumption.
    (*
    eapply annopar_fst_snd.
    apply H2. *)
    erewrite anno_unanno_par.
    eassumption.
    eapply annopar_fst_snd.
    (*
    unfold annotated_par.
    eapply annopar_fst_snd. *)
    
    eassumption.
    
    left. eauto.
    destruct_conjs.
    eauto.
  -
    (*
    do_wf_pieces.
     *)
    

    (*
    assert (well_formed_r a).
    {
      invc H.
      eassumption.
    }

    assert (well_formed_r a0).
    {
      invc H.
      eassumption.
    }
     *)
    
    (*
    
    
    do_wf_pieces. *)

    wrap_ccp.

    (*

    rewrite <- ccp_iff_cc in *.
    inversion H.
    dd.
    do_wf_pieces.
    repeat do_pl_immut.
    subst.
    rewrite ccp_iff_cc in *.
    assert (anno_parP a t1 loc).
    {
      econstructor.
      jkjke.
    }
    assert (anno_parP a0 t2 l).
    {
      econstructor.
      jkjke.
    }
    clear Heqp0; clear Heqp1.
     *)
    
    
    
    do_wfec_preserved.
    do_somerecons.

    do_reconP_determ.

    specialize IHt1 with (loc:=loc).
    (*
    find_rewrite. *)

    specialize IHt2 with (loc:=l).
    (*
    find_rewrite. *)


    


   
    (*
    unfold annotated_par in *.
    unfold anno_par in *.
    monad_unfold.
    ff.
    ff.
    fold anno_par in *.
     *)
    

    


    assert (gg_sub H10 \/ (exists r, term_sub (aasp r SIG) t2)).
    {
      eapply IHt2.
      eassumption.
      eassumption.
      2: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      eassumption.
    }
    door.

    assert (gg_sub H11 \/ (exists r, term_sub (aasp r SIG) t1)).
    {
      eapply IHt1.
      eassumption.
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

    (*


    rewrite <- ccp_iff_cc in *.
    inversion H.
    dd.
    do_wf_pieces.
    repeat do_pl_immut.
    subst.
    rewrite ccp_iff_cc in *.
    assert (anno_parP a t1 loc).
    {
      econstructor.
      jkjke.
    }
    assert (anno_parP a0 t2 l).
    {
      econstructor.
      jkjke.
    }
    clear Heqp0; clear Heqp1.
    
    

    repeat break_match; try solve_by_inversion.
    dd.
    rewrite fold_recev in *.
     *)

    do_rewrap_reconP.

    do_reconP_determ.

    do_wfec_split.
    


    
    Print do_wfec_preserved.
    (*
Ltac do_wfec_preserved :=
  repeat
   match goal with
   | H:well_formed_r ?t,
     H2:wf_ec ?stev,
     H3:copland_compileP ?t {| st_ev := ?stev; st_trace := _; st_pl := _ |}
          (Some tt) {| st_ev := ?stev'; st_trace := _; st_pl := _ |}
     |- _ =>
         assert_new_proof_by (wf_ec stev')
          ltac:(eapply wf_ec_preserved_by_cvm;
                 [ apply H | apply H2 | apply H3 ])
   end
     *)
    
    do_wfec_preserved.

    
    do_wfec_firstn.


    (*
    do_wfec_preserved.
     *)
    
    do_somerecons.

    (*
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
     
    
    do_wfec_firstn.
     *)
    
    do_wfec_skipn.
    clear_skipn_firstn.

    do_reconP_determ.

    (*


    
    repeat find_rewrite.
    dd.
    vmsts.
     *)
    
    do_ggsub.

    evSubFacts.

    +
      (*
      rewrite fold_recev in *.
      
      jkjke'.
      jkjke'.
      repeat ff.
      (*
      do_wfec_preserved.
      do_somerecons.
       *)
      rewrite fold_recev in *.
       *)
      
      
      
      assert (gg_sub H15 \/ exists r, term_sub (aasp r SIG) t1).
      {
        destruct s.
        destruct s; destruct s0;
          dd.
        ++
          (*
          repeat jkjke'. *)
          eapply IHt1.
          eassumption.
          eassumption.
          2: { eassumption. }
          eassumption.
          (*
          repeat find_rewrite.
          tauto. *)
          eassumption.
          (*

          repeat find_rewrite.
          rewrite fold_recev in *. *)
          eauto.
          (*
          eassumption.
          jkjke'.
          jkjke'.
          eassumption.
          
          rewrite fold_recev in *.
          repeat jkjke'.
          repeat find_rewrite.
          
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          ff.
           *)
          


          repeat eexists.
          eauto.

        ++
          (*
          repeat jkjke'. *)
          eapply IHt1.
          eassumption.
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          (*
         
          rewrite fold_recev in *. *)
          eauto.

          (*

          2: { repeat find_rewrite.
               eassumption.
             }
          eassumption.
          repeat find_rewrite.
          tauto.
          rewrite fold_recev in *.
          eauto.
           *)
          
          (*
          eassumption.
          jkjke'.
          jkjke'.
          eassumption.
          
          rewrite fold_recev in *.
          repeat jkjke'.
          repeat find_rewrite.
          
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          ff.
           *)
          


          repeat eexists.
          eauto.

        ++
          (*
          repeat jkjke'. *)
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            eassumption.
            2: { eassumption. }
            econstructor.
            eauto.
            econstructor. tauto.
            (*
            jkjke.
            jkjke.
            2: { jkjke. }
            eassumption.
            ff. *)
            (*
            rewrite fold_recev in *. *)
            
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
          (*
          repeat jkjke'. *)
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.
            (*
            jkjke.
            jkjke.
            2: { jkjke. }
            eassumption.
            ff. *)
            (*
            rewrite fold_recev in *.
             *)
            
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

      (*
      rewrite fold_recev in *.
      
      jkjke'.
      jkjke'.
      repeat ff.
      (*
      do_wfec_preserved.
      do_somerecons.
       *)
       *)
      
      
      
      assert (gg_sub H15 \/ exists r, term_sub (aasp r SIG) t2).
      {
        destruct s.
        destruct s; destruct s0;
          dd.
        ++
          (*
          repeat jkjke'. *)
          eapply IHt2.
          eassumption.
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          (*
          rewrite fold_recev in *. *)
          eauto.
          
          (*
          repeat find_rewrite.
          ff.
          ff
          repeat jkjke'.
          ff.
          eauto.
          

          2: { repeat find_rewrite.
               eassumption.
             }
          eassumption.
          repeat find_rewrite.
          tauto.
          rewrite fold_recev in *.
          eauto.
          (*
          eassumption.
          jkjke'.
          jkjke'.
          eassumption.
          
          rewrite fold_recev in *.
          repeat jkjke'.
          repeat find_rewrite.
          
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          ff.
           *)
          
           *)
          

          repeat eexists.
          eauto.
        ++
          
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.
            eauto.

            (*
            jkjke.
            2: { jkjke. }
            eassumption.
            ff.
            rewrite fold_recev in *.
            eauto. *)
           
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
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          eauto.

          (*
          jkjke.

          2: { repeat find_rewrite.
               eassumption.
             }
          eassumption.
          repeat find_rewrite.
          tauto.
          rewrite fold_recev in *.
          eauto.
          (*
          eassumption.
          jkjke'.
          jkjke'.
          eassumption.
          
          rewrite fold_recev in *.
          repeat jkjke'.
          repeat find_rewrite.
          
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          ff.
           *)
           *)
          
          


          repeat eexists.
          eauto.
        ++
         
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.
            eauto.

            (*
            jkjke.
            2: { jkjke. }
            eassumption.
            ff.
            rewrite fold_recev in *.
            eauto. 
             *)
            
           
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


    (*
    rewrite <- ccp_iff_cc in *.
    inversion H.
    dd.
    do_wf_pieces.
    repeat do_pl_immut.
    subst.
    rewrite ccp_iff_cc in *.

    assert (anno_parP a t1 (S loc)).
    {
      econstructor.
      jkjke.
    }
    clear Heqp0.
    
    

    repeat break_match; try solve_by_inversion.
    dd.
    rewrite fold_recev in *.
     *)
    wrap_ccp.
    do_rewrap_reconP.

    do_wfec_split.
    


    
    Print do_wfec_preserved.
    (*
Ltac do_wfec_preserved :=
  repeat
   match goal with
   | H:well_formed_r ?t,
     H2:wf_ec ?stev,
     H3:copland_compileP ?t {| st_ev := ?stev; st_trace := _; st_pl := _ |}
          (Some tt) {| st_ev := ?stev'; st_trace := _; st_pl := _ |}
     |- _ =>
         assert_new_proof_by (wf_ec stev')
          ltac:(eapply wf_ec_preserved_by_cvm;
                 [ apply H | apply H2 | apply H3 ])
   end
     *)
    
    do_wfec_preserved.

    
    do_wfec_firstn.


    (*
    do_wfec_preserved.
     *)
    
    do_somerecons.

    (*
    do_wfec_split.
    do_wfec_preserved.
    ff.
    subst.
     
    
    do_wfec_firstn.
     *)
    
    do_wfec_skipn.
    clear_skipn_firstn.
    (*
    repeat find_rewrite.
    dd.
    vmsts.
     *)
    do_reconP_determ.
    do_ggsub.

    evSubFacts.
    (*
    rewrite fold_recev in *.
    repeat jkjke'.
    ff.
    rewrite fold_recev in *.
     *)
    

    +
      
      (*
      do_wfec_preserved.
      do_somerecons.
       *)
      
      
      assert (gg_sub H13 \/ exists r, term_sub (aasp r SIG) t1).
      {
        destruct s.
        destruct s; destruct s0;
          dd; do_reconP_determ.
        ++
          eapply IHt1.
          eassumption.
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          eauto.


          (*
         
          jkjke.

          2: { repeat find_rewrite.
               eassumption.
             }
          eassumption.
          repeat find_rewrite.
          tauto.
          rewrite fold_recev in *.
          eauto.
          (*
          eassumption.
          jkjke'.
          jkjke'.
          eassumption.
          
          rewrite fold_recev in *.
          repeat jkjke'.
          repeat find_rewrite.
          
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          ff.
           *)
           *)
          
          


          repeat eexists.
          eauto.


        ++
          eapply IHt1.
          eassumption.
          eassumption.
          2: { eassumption. }
          eassumption.
          eauto.
          eauto.
          (*
          eassumption.
          rewrite fold_recev in *.
          symmetry. eassumption. *)


          (*

          jkjke.
          repeat find_rewrite.
               eassumption.
             }
          eassumption.
          repeat find_rewrite.
          tauto.
          rewrite fold_recev in *.
          eauto.
          (*
          eassumption.
          jkjke'.
          jkjke'.
          eassumption.
          
          rewrite fold_recev in *.
          repeat jkjke'.
          repeat find_rewrite.
          
          jkjke'.
          jkjke'.
          ff.
          jkjke'.
          jkjke'.
          ff.
           *)
          *)


          repeat eexists.
          eauto.

        ++
         
          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t1)).
          {
            eapply IHt1.
            eassumption.
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.
           
            eauto.

            (*
            jkjke.
            2: { jkjke. }
            eassumption.
            ff.
            rewrite fold_recev in *.
            eauto. *)
           
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
            eassumption.
            2: { eassumption. }
            eauto.
            econstructor. tauto.
            (*
            jkjke.
            2: { jkjke. }
            eassumption.
            ff. *)
           
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


      (*
      rewrite fold_recev in *.
      
      jkjke'.
      jkjke'.
      repeat ff.
      rewrite fold_recev in *.


      (*
      
      ff.
      rewrite fold_recev in *.
      
      jkjke'.
      jkjke'.
      repeat ff.
       *)
       *)
      wrap_ccp.

      
      

       assert (exists l' t', anno_par t2 0 = (l',t')).
       {
         destruct (anno_par t2 0).
         repeat eexists.
       }     
       destruct_conjs.
       
       specialize IHt2 with (loc:=0).
       (*
       find_rewrite. *)
       assert (well_formed_r H21).
       {
         Search "implies".
         eapply wfr_annt_implies_wfr_par.
         2: {
           econstructor.
           jkjke. }
         eassumption.
       }

      

       
       Print do_wfec_preserved.
       (*
Ltac do_wfec_preserved :=
  repeat
   match goal with
   | H:well_formed_r ?t,
     H2:wf_ec ?stev,
     H3:copland_compileP ?t {| st_ev := ?stev; st_trace := _; st_pl := _ |}
          (Some tt) {| st_ev := ?stev'; st_trace := _; st_pl := _ |}
     |- _ =>
         assert_new_proof_by (wf_ec stev')
          ltac:(eapply wf_ec_preserved_by_cvm;
                 [ apply H | apply H2 | apply H3 ])
   end
        *)
       

       (*
      do_wfec_preserved. 
      do_somerecons.
        *)

       do_annopar_redo.

       (*

       assert (anno_parP H18 t2 0).
       {
         econstructor.
         jkjke.
       }
        *)

      
       
       
      
      assert (gg_sub H13 \/ exists r, term_sub (aasp r SIG) t2).
      {
        destruct s.
        destruct s; destruct s0;
          dd.
        ++
         

          eapply IHt2.
          eassumption.
          eassumption.
          

          2: {
            rewrite <- ccp_iff_cc.
            eapply copland_compile_at.
            eassumption.
          }
          3: {
          
          rewrite at_evidence.
          rewrite <- par_evidence.
          erewrite anno_unanno_par.
          rewrite Heqe2.
          2: {
            invc H22.
            eapply annopar_fst_snd.
          }
          eauto.
          }
          eassumption.
          eassumption.
          repeat eexists.
          eauto.

        ++
          
          

          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            eassumption.
            2: {
              rewrite <- ccp_iff_cc.
              eapply copland_compile_at.
              eassumption.
            }
            3: {
          
          rewrite at_evidence.
          rewrite <- par_evidence.
          erewrite anno_unanno_par.
          rewrite Heqe2.
          2: {
            invc H22.
            eapply annopar_fst_snd.  }

          eauto.
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
          eassumption.
          

          2: {
            rewrite <- ccp_iff_cc.
            eapply copland_compile_at.
            eassumption.
          }
          3: {
          
          rewrite at_evidence.
          rewrite <- par_evidence.
          erewrite anno_unanno_par.
          rewrite Heqe2.
          2: {
            invc H22.
            eapply annopar_fst_snd.
          }
          eauto.
          }
          eassumption.
          
          eassumption.
          repeat eexists.
          eauto.


                  ++
          
          

          assert (gg_sub mtc \/ (exists r, term_sub (aasp r SIG) t2)).
          {
            eapply IHt2.
            eassumption.
            eassumption.
            2: {
              rewrite <- ccp_iff_cc.
              eapply copland_compile_at.
              eassumption.
            }
            3: {
          
          rewrite at_evidence.
          rewrite <- par_evidence.
          erewrite anno_unanno_par.
          rewrite Heqe2.
          2: {
            invc H22.
            eapply annopar_fst_snd.  }

          eauto.
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
      }



      
      door; eauto.
      
      Unshelve.
      eauto.
Defined.

Ltac do_sig_is :=
  match goal with
  | [H: well_formed_r ?pt,
        H2: wf_ec ?ecc,
            H': anno_parP ?pt ?t _,
            H6: gg_sub ?e',
                H4: reconstruct_evP ?ecc ?e,
                    H5: reconstruct_evP ?ecc' ?e',
                        H3: copland_compileP ?pt
                                             {| st_ev := ?ecc; st_trace := _; st_pl := _ |}
                                             (Some tt)
                                             {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}

     |- _] =>
    
    assert_new_proof_by
      (gg_sub e \/ (exists r : Range, term_sub (aasp r SIG) t))
      ltac:(eapply sig_is; [apply H' | apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
  end.

Ltac do_hsh_subt :=
  unfold hsh_subt in *;
  destruct_conjs;
  subst.

Lemma sig_term_ev_bseql: forall (r : Range) s (t1 t2 : AnnoTerm)
                           (e : EvidenceC)
                           (*
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc' loc *),
    not_hash_sig_term_ev (abseq r s t1 t2) e ->
    (*
    copland_compileP (snd(anno_par t1 loc))
                     {| st_ev := splitEv_l s (evc e0 e1); st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->
    Some e = reconstruct_ev (evc e0 e1) ->
     *)
    
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

Lemma sig_term_ev_bseqr: forall (r : Range) s (t1 t2 : AnnoTerm)
                           (e : EvidenceC)
                           (*
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc' loc *),
    not_hash_sig_term_ev (abseq r s t1 t2) e ->
    (*
    copland_compileP (snd(anno_par t2 loc))
                    {| st_ev := splitEv_r s (evc e0 e1); st_trace := tr; st_pl := p |}
                    (Some tt)
                    {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->
    Some e = reconstruct_ev (evc e0 e1) ->
     *)
    
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

Lemma sig_term_ev_bparl: forall (r : Range) s (t1 t2 : AnnoTerm)
                           (e : EvidenceC)
                           (*
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc' loc*),
    not_hash_sig_term_ev (abpar r s t1 t2) e ->
    (*
    copland_compileP (snd(anno_par t1 loc))
                     {| st_ev := splitEv_l s (evc e0 e1); st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->
    Some e = reconstruct_ev (evc e0 e1) ->
     *)
    
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

Lemma sig_term_ev_bparr: forall (r : Range) s (t1 t2 : AnnoTerm)
                           (e : EvidenceC)
                           (*
                           (e0 : EvBits) (e1 : Evidence)
                           (tr tr' : list Ev) (p p' : nat) ecc' loc*),
    not_hash_sig_term_ev (abpar r s t1 t2) e ->
    (*
    copland_compileP (snd(anno_par t2 loc))
                     {| st_ev := splitEv_r s (evc e0 e1); st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->
    Some e = reconstruct_ev (evc e0 e1) ->
     *)
    
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
  (*
  do_hsh_subt. *)
  econstructor.
  eauto.
  (*
  eapply termsub_transitive.
  eassumption.
  econstructor.
  econstructor. *)
Defined.

Ltac do_nhste_att :=
  match goal with
  | [H: not_hash_sig_term_ev (aatt _ _ ?t) ?e

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t e)
      ltac:(eapply not_hste_att; apply H)
  end.

Ltac do_nhste_lseql :=
  match goal with
  | [H: not_hash_sig_term_ev (alseq _ ?t1 _) ?e (*,
        
        H2: copland_compileP (snd (anno_par ?t1 _))
                             {| st_ev := ?ec; st_trace := _; st_pl := _ |}
                             (Some tt)
                             {| st_ev := _; st_trace := _; st_pl := _ |},
            H3: Some ?e = reconstruct_ev ?ec *)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 e)
      ltac:(eapply sig_term_ev_lseq; [apply H (* | apply H2 | apply H3 *) ])
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
  | [H: not_hash_sig_term_ev (alseq _ _ ?t2) _

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t2)
      ltac:(eapply nhst_lseq_r; [apply H ])
  end.

Ltac do_nhste_bseql :=
  match goal with
  | [H: not_hash_sig_term_ev (abseq _ ?s ?t1 _) ?e (*,
        
        H2: copland_compileP (snd (anno_par ?t1 _))
                             {| st_ev := splitEv_l ?s ?ec; st_trace := _; st_pl := _ |}
                             (Some tt)
                             {| st_ev := _; st_trace := _; st_pl := _ |},
            H3: Some ?e = reconstruct_ev ?ec *)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 (splitEvl s e))
      ltac:(eapply sig_term_ev_bseql; [apply H (* | apply H2 | apply H3 *) ])
  end.

Ltac do_nhste_bseqr :=
  match goal with
  | [H: not_hash_sig_term_ev (abseq _ ?s _ ?t2) ?e (*,
        H2: copland_compileP (snd (anno_par ?t1 _))
                            {| st_ev := splitEv_r ?s ?ec; st_trace := _; st_pl := _ |}
                            (Some tt)
                            {| st_ev := _; st_trace := _; st_pl := _ |},
            H3: Some ?e = reconstruct_ev ?ec *)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 (splitEvr s e))
      ltac:(eapply sig_term_ev_bseqr; [apply H (*| apply H2 | apply H3 *)])
  end.

Ltac do_nhste_bparl :=
  match goal with
  | [H: not_hash_sig_term_ev (abpar _ ?s ?t1 _) ?e (*,
        H2: copland_compileP (snd (anno_par ?t1 _))
                            {| st_ev := splitEv_l ?s ?ec; st_trace := _; st_pl := _ |}
                            (Some tt)
                            {| st_ev := _; st_trace := _; st_pl := _ |},
            H3: Some ?e = reconstruct_ev ?ec *)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 (splitEvl s e))
      ltac:(eapply sig_term_ev_bparl; [apply H (* | apply H2 | apply H3 *)])
  end.

Ltac do_nhste_bparr :=
  match goal with
  | [H: not_hash_sig_term_ev (abpar _ ?s _ ?t2) ?e (*,
        
        H2: copland_compileP (snd (anno_par ?t1 _))
                             {| st_ev := splitEv_r ?s ?ec; st_trace := _; st_pl := _ |}
                             (Some tt)
                             {| st_ev := _; st_trace := _; st_pl := _ |},
            H3: Some ?e = reconstruct_ev ?ec *)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 (splitEvr s e))
      ltac:(eapply sig_term_ev_bparr; [apply H (* | apply H2 | apply H3 *) ])
  end.



(*
Ltac do_nhste :=
  try do_nhste_att.
 *)

Lemma hshsig_ev_term_contra: forall t pt p (e e' :EvidenceC) tr tr' p' (ecc ecc':EvC) loc,

    anno_parP pt t loc ->
    well_formed_r pt ->
    wf_ec ecc ->
    not_hash_sig_term_ev t e ->
    
    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' ->

    copland_compileP pt
                     {| st_ev := ecc; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->

    not_hash_sig_ev e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros. (* repeat ff. *)
  -
    wrap_ccp.
    (*
    rewrite <- ccp_iff_cc in *.
    inversion H. *)
    destruct a; dd.
    +
    unfold not_hash_sig_term_ev in *.
    destruct_conjs.
    do_reconP_determ.
    eassumption.
    +
    unfold cons_uu in *.
    repeat ff.
    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    do_rewrap_reconP.
    do_reconP_determ.
    eapply not_hshsig_uuc; eauto.
    +
    repeat ff.
    unfold not_hash_sig_term_ev in *;
      destruct_conjs.

    (*
    
    assert (not_hash_sig_ev e).
    {
      eapply not_ev; eauto.
    } *)
    unfold cons_sig in *.
    ff.
    do_rewrap_reconP.
    do_reconP_determ.
   
    (*
    rewrite fold_recev in *.
    assert ((evc (get_bits ecc) (get_et ecc)) = ecc).
    {
      destruct ecc.
      ff.
    }
    rewrite H5 in *; clear H5.
     *)
    
    
    ff.
    eapply not_hshsig_ggc; eauto.
  +
    assert (not_hash_sig_ev e).
    {
      eapply not_ev; eauto.
    }
    unfold cons_hh in *.
    do_rewrap_reconP.

    assert (~ (gg_sub e)).
    {
      cbv in *.
      destruct_conjs.
      unfold not; intros.
      do_ggsub.
      (*
      invc H7.
      destruct_conjs.
      subst. *)
      eapply H6.
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
    invc H7.
    invc H6.
    destruct_conjs.
   
    invc H10.

    eapply gg_recons; eauto.

    (*

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
    eassumption. *)

  - (* aatt case *)
    (*
    do_wf_pieces.
    do_nhste_att.
     *)

    

    wrap_ccp.

    (*

    cbn in *.
    rewrite <- ccp_iff_cc in *.
    inversion H.
    dd.
    do_wf_pieces. 
     *)
    
    do_nhste_att.



        do_assume_remote t ecc n HHH.
          

    (*

    assert (exists l' t', anno_par t 0 = (l',t')).
    {
      destruct (anno_par t 0).
      repeat eexists.
    }
    destruct H7 as [xx];
      destruct H7 as [y7].
    destruct_conjs.
     *)
    
    (*
    jkjke.
     *)
    




    
    specialize IHt with (loc:=0).
    (*
    find_rewrite.
    simpl in *. *)


    (*

    

    assert (
            copland_compile H8 {| st_ev := ecc; st_trace := []; st_pl := n |} =
    (Some tt,
     {| st_ev := toRemote (unannoPar H8) n ecc;
        st_trace := remote_events (unannoPar H8) n;
        st_pl := n
     |})
      ).
    {
      eapply copland_compile_at.
      eapply wfr_annt_implies_wfr_par.
      eassumption.
      econstructor.
      jkjke.
    }
    
     *)
    

    
    eapply IHt.
    econstructor. tauto.
    Search "implies".
    eapply wfr_annt_implies_wfr_par;
      [eassumption | econstructor; jkjke].

  
    2: { eassumption. }
    2: { eassumption. }
    
    eassumption.
    eassumption.
    simpl.
    econstructor.

    subst.
    jkjke.
    
  - (* alseq case *)
    (*
    cbn in *.
    repeat break_let.
    cbn in *.
    do_wf_pieces.
     *)




    (*
    assert (anno_parP a t1 loc).
    {
      econstructor.
      jkjke.
    }
    assert (anno_parP a0 t2 l).
    {
      econstructor.
      jkjke.
    }
    clear Heqp0; clear Heqp1.
     *)

    wrap_ccp.
    
    
    specialize IHt1 with (loc:=loc).
    specialize IHt2 with (loc:=l).
    

    do_wfec_preserved.
    do_somerecons.
    (*
    repeat jkjke'.
    dd. *)
    do_reconP_determ.
    Print do_nhste_lseql.
    (*
Ltac do_nste_lseq :=
  match goal with
  | H:not_hash_sig_term_ev (alseq _ ?t1 _) ?e,
    H2:copland_compileP (snd (anno_par ?t1 _))
         {| st_ev := ?ec; st_trace := _; st_pl := _ |} 
         (Some tt) {| st_ev := _; st_trace := _; st_pl := _ |},
    H3:Some ?e = reconstruct_ev ?ec
    |- _ =>
        assert_new_proof_by (not_hash_sig_term_ev t1 e)
         ltac:(eapply sig_term_ev_lseq; [ apply H | apply H2 | apply H3 ])
  end
     *)
    

    (*
   
    Check sig_term_ev_lseq.
     *)
    
    

    (*
    destruct ecc; destruct st_ev0.
    
    assert (a = snd (anno_par t1 loc)).
    {
      inversion H5.
      jkjke.
    }
     *)
    
    do_nhste_lseql.


    (*

    assert_new_proof_by (not_hash_sig_term_ev t1 H10)
                        ltac:(eapply sig_term_ev_lseq;
                              [apply H1 | apply Heqp2 | apply H11]).
     *)
    

    (*

    assert (a0 = snd (anno_par t2 l)).
    {
      jkjke.
    }
    subst.
     *)


    (*

    rewrite <- H2 in *. *)
    
    
    
     
      

    assert (not_hash_sig_ev H10) by eauto.

    Print do_nhst_lseqr.

    do_nhst_lseqr.
    (*
    destruct ecc'. *)

    

    assert (not_hash_sig_term_ev t2 H10).
    {
      split.
      eassumption.
      split.
      eassumption.
      intros.
      unfold not.
      intros.

      (*

      assert (a0 = snd (anno_par t2 l)).
      {
        jkjke.
      }
      rewrite H18 in Heqp3, H6.

      rewrite H2 in Heqp2, H5.



      


      
      Check sig_is.

      Print do_sig_is.
       *)
      
      (*
Ltac do_sig_is :=
  match goal with
  | H:well_formed_r (snd (anno_par ?t _)),
    H2:wf_ec ?ecc,
    H6:gg_sub ?e',
    H4:Some ?e = reconstruct_ev ?ecc,
    H5:Some ?e' = reconstruct_ev ?ecc',
    H3:copland_compileP (snd (anno_par ?t _))
         {| st_ev := ?ecc; st_trace := _; st_pl := _ |} 
         (Some tt) {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}
    |- _ =>
        assert_new_proof_by
         (gg_sub e \/ (exists r : Range, term_sub (aasp r SIG) t))
         ltac:(eapply sig_is;
                [ apply H
                | apply H2
                | apply H3
                | apply H4
                | apply H5
                | apply H6 ])
  end
       *)
      
      

      do_sig_is.

      (*

      repeat jkjke';
      repeat ff;
      try rewrite fold_recev in *;
      repeat jkjke';
      repeat ff.
       *)
      
      
      door.
      +
        unfold not_hash_sig_term_ev in H2.
        destruct_conjs.
        unfold not in H20.
        eapply H20.
        eassumption.
        eauto.
        (*
        do_hsh_subt.
        econstructor.
        eauto. *)
      +
        (*
        do_hsh_subt.
         *)
        
        unfold not_hash_sig_term_ev in *.
        destruct_conjs.
        unfold not_hash_sig_term in *.
        unfold not in *.
        eapply H2. (*with (t':= (alseq r t1 t2)). *)
        
        
        econstructor.
        repeat eexists.
        eassumption.
        
        eassumption.
        econstructor.

    }
    
    eapply IHt2.
    eassumption.
    eassumption.

    2: { eassumption. }
    2: { eassumption. }
    eassumption.
    eassumption.
    eassumption.
    
  - (* abseq case *)

    (*
    do_wf_pieces.
    vmsts.
     *)

    wrap_ccp.

    (*

     cbn in *.
    repeat break_let.
    cbn in *.
    do_wf_pieces.

    rewrite <- ccp_iff_cc in *.
    dd.
     *)
    
    do_rewrap_reconP.
    specialize IHt1 with (loc:=loc).
    specialize IHt2 with (loc:=l).
   

    do_wfec_split.
    do_wfec_preserved.







    (*
    do_wfec_preserved. *)
    do_somerecons.
    (*
    do_wfec_split.
    do_wfec_preserved.
    ff.
     
    
    subst.
     *)
    
    do_wfec_firstn.
    do_wfec_skipn.
    clear_skipn_firstn.

    (*
    repeat find_rewrite.

    jkjke'.
    jkjke'.
    vmsts.
    ff.
    rewrite fold_recev in *.
     *)
    do_reconP_determ.



    
    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
    

    (*
    destruct ecc.
    Check sig_term_ev_bseql.
    Print do_ste_bseql.
    (*
Ltac do_ste_bseql :=
  match goal with
  | H:not_hash_sig_term_ev (abseq _ ?s ?t1 _) ?e
    |- _ =>
        assert_new_proof_by (not_hash_sig_term_ev t1 (splitEvl s e))
         ltac:(eapply sig_term_ev_bseql; [ apply H ])
  end
     *)
    
    
    simpl.
     *)
    
    (*
    assert (a = snd (anno_par t1 loc)).
    {
      jkjke.
    }
    subst.

    assert (a0 = snd (anno_par t2 l)).
    {
      jkjke.
    }
    subst.
     *)
    
    
    
    do_nhste_bseql.
    do_nhste_bseqr.

    evSubFacts.

    (*
    
    invc H10. *)
    +
      invc H15.
      destruct_conjs.
      solve_by_inversion.
    +
      (*
      rewrite fold_recev in *. 
      do_wfec_preserved.
      do_somerecons.
       *)
      
        
      assert (not_hash_sig_ev H11).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        
        4: {
          eassumption. }
        4: {
          eassumption. }
        eassumption.
        eassumption.
        destruct s; destruct s; destruct s0; ff.
        econstructor. tauto.
        econstructor. tauto.

      }
      
      invc H15.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H18.
      unfold not in *.
      eapply H18.
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.
      (*
      jkjke'.
      jkjke'.
      jkjke'.
      jkjke'.
      repeat ff. *)

    +
      (*
      rewrite fold_recev in *.
       *)
      
      assert (not_hash_sig_ev H10).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        
        4: { eassumption. }
        4: {
          eassumption. }
        eassumption.
        eassumption.
        destruct s; destruct s; destruct s0; ff.
        econstructor. tauto.
        econstructor. tauto.

      }
      
      invc H15.
      destruct_conjs.
      subst.
      unfold not_hash_sig_ev in H18.
      unfold not in *.
      eapply H18.
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.

  - (* new abpar case *)
    
    (*
    do_wf_pieces.
    vmsts.
     *)

    wrap_ccp.

    (*

    cbn in *.
    repeat break_let.
    cbn in *.
    do_wf_pieces.

    rewrite <- ccp_iff_cc in *.
    dd.
    do_pl_immut.
    ff.
    rewrite ccp_iff_cc in *.
     *)
    
    specialize IHt1 with (loc:=S loc).
    specialize IHt2 with (loc:=0).

    do_rewrap_reconP.

  

    do_wfec_split.
    do_wfec_preserved.







    (*
    do_wfec_preserved. *)
    do_somerecons.
    (*
    do_wfec_split.
    do_wfec_preserved.
    ff.
     
    
    subst.
     *)
    
    do_wfec_firstn.
    do_wfec_skipn.
    clear_skipn_firstn.

    (*
    repeat find_rewrite.

    jkjke'.
    jkjke'.
    ff.
    rewrite fold_recev in *.
     *)

    do_reconP_determ.


    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
    (*
    destruct ecc.
    assert (a = snd (anno_par t1 (S loc))).
    {
      jkjke.
    }
    rewrite H15 in *.
     *)
    

    (*

    assert (a0 = snd (anno_par t2 l)).
    {
      jkjke.
    }
    subst.
     *)
    
    do_nhste_bparl.
    
    do_nhste_bparr.
    

    (*
    inversion H8; clear H8.
    rewrite <- H17 in *; clear H17.
    rewrite H18 in *; clear H18.
     *)
    evSubFacts.
    +
      invc H13.
      destruct_conjs.
      solve_by_inversion.
    +
      (*
      rewrite fold_recev in *.
       
      
      do_wfec_preserved.
      do_somerecons.
       *)
      
          
      assert (not_hash_sig_ev H9).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        5: { eassumption. }
        eassumption.
        eassumption.

        

        destruct s; destruct s; destruct s0; ff.
        econstructor. tauto.
        econstructor. tauto.
        eassumption.

      }
      
      invc H13.
      destruct_conjs.
      unfold not_hash_sig_ev in H16.
      unfold not in *.
      eapply H16.
      econstructor.
      repeat eexists.
      eassumption.
      jkjke'.
      (*
      jkjke'.
      jkjke'.
      jkjke'.
      repeat ff. *)

    +
      (*
      rewrite fold_recev in *.
       *)

      wrap_ccp.

      do_assume_remote t2 (splitEv_r s ecc) p HHH.


      (*

      
      assert (exists l' t', anno_par t2 l = (l',t')).
    {
      destruct (anno_par t2 l).
      repeat eexists.
    }
    destruct_conjs.
       *)
      
      

      
    assert (well_formed_r HHH).
    {
      eapply wfr_annt_implies_wfr_par.
      eassumption.
      econstructor.
      subst.
      jkjke.
    }

    (*
    

    assert (
    copland_compile H20 {| st_ev := (splitEv_r s ecc); st_trace := []; st_pl := p |} =
    (Some tt,
     {| st_ev := toRemote (unannoPar H20) p (splitEv_r s ecc);
        st_trace := remote_events (unannoPar H20) p;
        st_pl := p
     |})
      ).
    {
      eapply copland_compile_at.
      
      eassumption.
    }
     *)

   

    

      

    (*
   
    specialize IHt2 with (loc:= 0).
     *)
    
      assert (not_hash_sig_ev e5).
    {
      do_reconP_determ.
        eapply IHt2 with (e:=(splitEvr s H10)).
        7: {
          econstructor.
          eassumption.
        }

        (*
        
          econstructor.
          eapply copland_compile_at.
          Search "implies".
          eapply wfr_annt_implies_wfr_par.
          apply H6.
          econstructor.
          reflexivity.
         } *)
        econstructor. subst.
        jkjke.
        eassumption.
        eassumption.
        
        destruct s; destruct s; destruct s0; dd;
          do_reconP_determ; ff.
         destruct s; destruct s; destruct s0; dd;
           do_reconP_determ; ff.
         econstructor. tauto.
         econstructor. tauto.


         destruct s; destruct s; destruct s0; dd;
           unfold mt_evc;
           do_reconP_determ; ff.

         rewrite at_evidence.
         rewrite par_evidence in Heqe2.
         (*
          rewrite <- Heqe2.
          rewrite <- Heqe2. *)
         congruence.
         rewrite at_evidence.
         rewrite par_evidence in Heqe2.
         rewrite <- Heqe2 in *.
         eassumption.

         rewrite at_evidence.
         rewrite par_evidence in Heqe2.
         (*
          rewrite <- Heqe2.
          rewrite <- Heqe2. *)
         congruence.

         rewrite at_evidence.
         rewrite par_evidence in Heqe2.
         rewrite <- Heqe2 in *.
         eassumption.
         

 

         (*
          assert (unannoPar H20 = t2).
          {
            erewrite anno_unanno_par.
            reflexivity.
            eassumption.
          }
          congruence.
          *)
         




          (*
        simpl in *.
        eassumption.
        ff.
        
        eassumption.
        rewrite <- H20.
        tauto.
        eapply wfr_annt_implies_wfr_par.
        eassumption.
        econstructor.
        tauto.

        3: { destruct s; destruct s; destruct s0; ff.
             jkjke.
        


          
        eassumption.
        econstructor.
       

        eapply sig_term_ev_bparr.
        ++
          eassumption.
        ++
          rewrite Heqp1.
          simpl.
          eassumption.

        ++
          jkjke.



        
        (*
        
        eapply wfr_annt_implies_wfr_par.
        apply H4.
        eassumption.
         *)
        

        5: {
          eassumption.
        }
        eassumption.
        3: {
          rewrite at_evidence.
          rewrite par_evidence in Heqe2.
          rewrite <- Heqo0.
          rewrite <- Heqe2.
          assert (unannoPar a0 = t2).
          {
            erewrite anno_unanno_par.
            reflexivity.
            eassumption.
          }
          congruence.
        }
        
        2: { destruct s; destruct s; destruct s0; ff. }
        
          
          
       
        (*
        
        4: { symmetry. eassumption. }
        4: {
          eassumption.
          jkjke.

          rewrite <- Heqe2.
          rewrite par_evidence.
          rewrite <- at_evidence.
          assert (t2 = unannoPar H12).
          {
            erewrite anno_unanno_par.
            reflexivity.
            eassumption.
          }
          rewrite H17.
          eassumption. }
        eassumption.
        2: { destruct s; destruct s; destruct s0; ff. }
         *)
        

        eapply sig_term_ev_bparr.
        ++
          eassumption.
        ++
          rewrite Heqp1.
          simpl.
          eassumption.

        ++
          jkjke.
        }
        

          

          (*
          simpl.
          rewrite <- Heqe2.
          rewrite par_evidence.
          rewrite <- at_evidence.
          assert (t2 = unannoPar H12).
          {
            erewrite anno_unanno_par.
            reflexivity.
            eassumption.
          }
          rewrite H16.
          simpl.
          
          eapply copland_compile_at.
          eapply wfr_annt_implies_wfr_par.
          eassumption.
          eassumption.
          
        
        eassumption.

         do_ste_bparr.

        econstructor.

        invc H1.
        admit.

      }
           *)
           *)

      }
      
          
      

      
      invc H13.
      destruct_conjs.
      subst.
     
      unfold not_hash_sig_ev in H25.
      unfold not in *.
      eapply H25.
      econstructor.
      repeat eexists.
      eassumption.
      eassumption.
Defined.

Check hshsig_ev_term_contra.

Ltac do_hste_contra :=
  match goal with
  | [H: well_formed_r ?pt,
        H': anno_parP ?pt ?t _,
        H2: wf_ec ?ecc,
            H3: not_hash_sig_term_ev ?t ?e,
                H4: reconstruct_evP ?ecc ?e,
                    H5: reconstruct_evP ?ecc' ?e',
                        H6: copland_compileP ?pt
                                             {| st_ev := ?ecc; st_trace := _; st_pl := _ |}
                                             (Some tt)
                                             {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply hshsig_ev_term_contra; [apply H' | apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
  end.

(*
Ltac do_nste :=
  try do_nste_lseq.
*)

Lemma sig_term_ev_lseqr: forall r t1 t2 pt e e0 e1 e2 e3 tr tr' p p' H5 loc,
    anno_parP pt t1 loc ->
    well_formed_r pt ->
    wf_ec (evc e0 e1) ->
    not_hash_sig_term_ev (alseq r t1 t2) e ->
    copland_compileP pt
                     {| st_ev := evc e0 e1; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := evc e2 e3; st_trace := tr'; st_pl := p' |} ->
    reconstruct_evP (evc e0 e1) e ->
    reconstruct_evP (evc e2 e3) H5 ->
    not_hash_sig_term_ev t2 H5.
Proof.
  intros.
  
  do_nhste_lseql.
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
      unfold not_hash_sig_term_ev in H2.
      destruct_conjs.
      concludes.
      unfold not in *.
      do_hsh_subt.
      forwards;
        eauto.
      ++
        

      unfold not_hash_sig_term_ev in H2.
      destruct_conjs.
      unfold not_hash_sig_term in H2.
      unfold not in *.
      do_hsh_subt.
      eapply H2; eauto.
      econstructor.
      repeat eexists.
      eauto.
      eauto.
Defined.

Ltac do_evsub_ihhh' :=
  match goal with
  | [H: copland_compileP ?pt
                         {| st_ev := ?ee; st_trace := _; st_pl := _ |}
                         (Some tt)
                         {| st_ev := ?stev; st_trace := _; st_pl := _ |},
        H': anno_parP ?pt ?t1 _,
        
        (* H2: copland_compile ?t2
                            {| st_ev := _(*?stev'*); st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}), *)
        H3: reconstruct_evP ?ee _,
            H4: reconstruct_evP ?stev ?v',
                IH: forall _, _ -> _ ,(*context[forall _, well_formed_r ?t1 -> _], *)
       Hf: well_formed_r ?pt,
       Hnn: not_none_none ?t1,
       Hwf: wf_ec ?ee,
       Hev: events ?t1 _ _ _
                   

       |-  (exists e'' : EvidenceC, EvSub (uuc ?i ?args ?tpl ?tid ?p0 ?n e'') _) \/
          (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
              EvSub (hhc p'0 bs ett) _ /\ EvSubT (uu ?i ?args ?tpl ?tid ?p0 et') ett)
            (*context[EvSub _(*(uuc ?i ?args ?tpl ?tid ?n _)*) _ \/ _]*)
    ] => 

    

    assert_new_proof_by 
      (
        (exists e'' : EvidenceC, EvSub (uuc i args tpl tid p0 n e'') v') \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) v' /\ EvSubT (uu i args tpl tid p0 et') ett)
      )

      (*
          assert_new_proof_by
            (exists ee, EvSub (uuc i args tpl tid n ee) v \/
             (exists (ett : Evidence) (p'0 bs : nat) (et':Evidence),
                 EvSub (hhc p'0 bs ett) v /\ EvSubT (uu i args tpl tid et') ett)) 
       *)
      ltac: (eapply IH; [apply H' | apply Hf | apply Hnn| apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
              (*ltac:(ff; repeat jkjke'; eauto)*)
              
              
  end.

Lemma uu_preserved': forall t pt p et n p0 i args tpl tid
                       e tr e' tr' p' ecc ecc' loc,

    anno_parP pt t loc ->
    well_formed_r pt ->
    not_none_none t ->
    wf_ec ecc ->
    reconstruct_evP ecc e ->
    reconstruct_evP ecc' e' ->
    events t p et (umeas n p0 i args tpl tid) ->
    copland_compileP pt
                     {| st_ev := ecc; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->

    (
      (exists e'', EvSub (uuc i args tpl tid p0 n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid p0 et') ett)
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    wrap_ccp.
    
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
    invEvents.
    do_not_none.

    (*
    invc H.
    dd.
     *)

    do_assume_remote t ecc n H9.

    (*

    assert (exists loc loc' t2',
                 anno_par t loc = (loc', t2')).
      {
        exists 0.
        destruct (anno_par t 0).
        repeat eexists.
      }
      destruct_conjs.
     *)
    
      specialize IHt with (loc:=0).

    

      eapply IHt.
      econstructor.
      reflexivity.
      eapply wfr_annt_implies_wfr_par.
      eassumption.
      econstructor. tauto.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      

      (*


      assert (t = unannoPar H9).
      {
        erewrite anno_unanno_par; eauto.
      }
      rewrite H11.
       *)
      rewrite H7.
      simpl.
      rewrite H10.
      econstructor.
      eassumption.
    
  -
    (*
    do_wf_pieces.
     *)


    wrap_ccp.

    (*

    
    repeat ff.
    assert (well_formed_r a).
    {
      invc H.
      eauto.
    }
    assert (well_formed_r a0).
    {
      invc H.
      eauto.
    }
     *)
    
    
    


    
    do_not_none.
    (*
    ff.
    dosome.
    ff.
    vmsts.
    ff.
     *)
    

    invEvents.
    + (* t1 case *)
      
      do_wfec_preserved.
      do_somerecons.
      do_reconP_determ.

      (*

      assert (a = snd (anno_par t1 loc)).
      {
        admit.
      }
      subst.

      assert (a0 = snd (anno_par t2 l)).
      {
        admit.
      }
      subst.
       *)
      

      
      
      

      repeat do_evsub_ihhh'.

      door.
      ++

        (*
        
        destruct_conjs.
        repeat ff.

        repeat jkjke'.
        repeat ff.
         *)
        

        (*

         assert (a = snd (anno_par t1 loc)).
      {
        admit.
      }
      rewrite H2 in Heqp3.
      

      assert (a0 = snd (anno_par t2 l)).
      {
        admit.
      }
      rewrite H3 in Heqp2.
         *)
        
      Print do_evaccum.
(*
Ltac do_evaccum :=
  repeat
   match goal with
   | H:well_formed_r (snd (anno_par ?t _)),
     H2:wf_ec ?ecc,
     H3:Some ?e = reconstruct_ev ?ecc,
     H4:Some ?e' = reconstruct_ev ?ecc',
     H5:EvSub ?e'' ?e,
     H6:copland_compile (snd (anno_par ?t _))
          {| st_ev := ?ecc; st_trace := _; st_pl := _ |} =
        (Some tt,
        {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}),
     H7:not_none_none ?t
     |- _ =>
         assert_new_proof_by
          (EvSub e'' e' \/
           (exists (ett : Evidence) (p'0 bs : nat),
              EvSub (hhc p'0 bs ett) e' /\
              EvSubT (et_fun e'') ett))
          ltac:(eapply evAccum';
                 [ apply H
                 | apply H7
                 | apply H2
                 | apply H3
                 | apply H4
                 | apply H5
                 | apply H6 ])
   end
 *)

     

      (*

      assert (well_formed_r a).
      {
        jkjke.
        jkjke.
      }
      assert (well_formed_r a0).
      {
        jkjke.
        jkjke.
      }

      assert (t1 = unannoPar a0).
      {
        erewrite anno_unanno_par.
        tauto.
        eassumption.
      }

      assert (t2 = unannoPar a).
      {
        erewrite anno_unanno_par.
        tauto.
        eassumption.
      }
      rewrite H21 in H7.
      rewrite H22 in H8.
       *)


      do_evaccum.


      
     (*
      


      edestruct evAccum'.
      apply H2.
      eassumption.
      eassumption.
      5 : {
        rewrite H2.
        eassumption.
      }
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      left.
      eauto.

      destruct_conjs.
      ff.
      right.
      repeat (eexists; eauto).
      ++
        repeat jkjke'.
        repeat ff.

                 assert (a = snd (anno_par t1 loc)).
      {
        admit.
      }
      rewrite H2 in Heqp3.
      

      assert (a0 = snd (anno_par t2 l)).
      {
        admit.
      }
      rewrite H3 in Heqp2.

       assert (well_formed_r a).
      {
        jkjke.
        jkjke.
      }
      assert (well_formed_r a0).
      {
        jkjke.
        jkjke.
      }

      assert (t1 = unannoPar a0).
      {
        erewrite anno_unanno_par.
        tauto.
        eassumption.
      }

      assert (t2 = unannoPar a).
      {
        erewrite anno_unanno_par.
        tauto.
        eassumption.
      }
      rewrite H25 in H7.
      rewrite H26 in H8.


      

      edestruct evAccum'.
      apply H2.
      eassumption.
      eassumption.
    
      5: { rewrite H2.
           eassumption.
      }
      eassumption.
      eassumption.
      eassumption.
      eassumption.


          right.
          repeat (eexists; eauto).
        
          destruct_conjs.
          ff.
          right.
          repeat eexists.
          eauto.

          eapply evsubT_transitive.
          eapply hhSubT.
          eassumption.
          eassumption.


*)


          (*
      left.
      eauto.

      destruct_conjs.
      ff.
      right.
      repeat (eexists; eauto).
      
      
        

        
        
      
        
        eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.


     
      
      

        do_evaccum.
           *)
      

        (*
        clear H12. *)
        door.
        +++
          left.
          eauto.
        +++
          
          right.
          repeat (eexists; eauto).
           
          

      ++
        (*
        repeat jkjke'.
        repeat ff. *)
        
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

      (*

      do_pl_immut.
      do_pl_immut.
      subst.
       *)
      

      do_wfec_preserved.
      do_somerecons.

      (*

      assert (a = (snd (anno_par t1 loc))).
      {
        rewrite Heqp1.
        tauto.
      }

      rewrite H17 in Heqp2.
      rewrite H17 in H5.

      assert (a0 = (snd (anno_par t2 l))).
      {
        rewrite Heqp0.
        tauto.
      }

      rewrite H18 in Heqp3.
      rewrite H18 in H6.

      
      

      Print do_evsub_ihhh'.
       *)

      do_reconP_determ.
      

      repeat do_evsub_ihhh'.

      (*

      clear H18. *)
      door.
      ++
        eauto.
      ++
        destruct_conjs;
          right;
          repeat (eexists; eauto).


  - (* abseq case *)

    wrap_ccp.
    do_not_none.

    (*
    do_wf_pieces.
    do_not_none.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
     *)

    do_rewrap_reconP.
    

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      (*repeat do_pl_immut; 
      do_somerecons; 
      repeat jkjke'; ff; *)
      (*
        try (rewrite fold_recev in * ); *)
        try do_somerecons;
        do_reconP_determ;
        do_evsub_ihhh';

        door; (*repeat jkjke'; dd; *)
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).

  - (* abpar case *)


    wrap_ccp.
    do_not_none.

    (*
    
    do_wf_pieces.
    do_not_none.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
     *)

    do_rewrap_reconP.


    invEvents;

      try (
      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      (*repeat do_pl_immut; 
      do_somerecons; 
      repeat jkjke'; ff; *)
        
      try do_somerecons;
      do_reconP_determ;
        do_evsub_ihhh';

        door; (*repeat jkjke'; dd; *)
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

      

      do_assume_remote t2 (splitEv_r s ecc) p HHH.

      (*

      assert (exists a0 loc loc', anno_par t2 loc  = (loc',a0)).
      {
        destruct (anno_par t2 0) eqn:hi.
        repeat eexists.
        eassumption.
      }
      destruct_conjs.
       *)
      
     

      
      

      edestruct IHt2.
      econstructor.
      reflexivity.
      
      eapply wfr_annt_implies_wfr_par.
      eassumption.
      econstructor.
      tauto.
      eassumption.
      5: {
        econstructor.
        rewrite H15.
        simpl.
        eassumption.
        (*
        econstructor.
        eapply copland_compile_at.
        eapply wfr_annt_implies_wfr_par.
        eassumption.
        eassumption. *)
      }
      4: {
        eassumption.
      }
      3 : {
        rewrite par_evidence in *.
        rewrite at_evidence in *.
        (*
        assert (t2 = unannoPar H20).
        {
          inversion H23.
          rewrite H26.
          erewrite anno_unanno_par.
          reflexivity.
          eapply annopar_fst_snd.
        }
         *)
        
        rewrite <- H20.
        rewrite Heqe2.
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


Lemma uu_preserved: forall t1 t2 pt1 pt2 loc1 loc2 p et n p0 i args tpl tid
                      e tr st_ev st_trace p'
                      e' tr' p'' ecc,
    anno_parP pt1 t1 loc1 ->
    anno_parP pt2 t2 loc2 ->
    well_formed_r pt1 ->
    well_formed_r pt2 ->
    not_none_none t1 ->
    not_none_none t2 ->
    wf_ec e ->
    reconstruct_evP ecc e' ->
    events t1 p et (umeas n p0 i args tpl tid) ->
    copland_compileP pt1
                     {| st_ev := e; st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |} ->
    
    copland_compileP pt2
                     {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |}
                     (Some tt)
                     {| st_ev := ecc; st_trace := tr'; st_pl := p'' |} ->

    (
      (exists e'', EvSub (uuc i args tpl tid p0 n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid p0 et') ett)
    ).
Proof.
  intros.

  wrap_ccp.

  (*

  ff.
   *)
  
  do_wfec_preserved.
  do_somerecons.
  
  assert (
      (exists e'', EvSub (uuc i args tpl tid p0 n e'') H13) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) H13 /\
          EvSubT (uu i args tpl tid p0 et') ett)
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
    
    clear H20.
    door; eauto.

    right;
      (repeat eexists; eauto).
  +
    clear H24.
    door; ff.
    ++
      right;
        repeat (eexists; eauto).

    ++
      assert (EvSubT (uu i args tpl tid p0 H21) H24).
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
  | [H: well_formed_r ?pt,
        H': anno_parP ?pt ?t1 _,
        H2: wf_ec ?ecc,
            H3: not_hash_sig_term_ev (alseq _ ?t1 ?t2) ?e,
                H5: reconstruct_evP ?ecc ?e,
                    H6: reconstruct_evP ?ecc' ?e',
                        H4: copland_compileP ?pt
                                             {| st_ev := ?ecc; st_trace := _; st_pl := _ |}
                                             (Some tt)
                                             {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 e')
      ltac:(eapply sig_term_ev_lseqr; [apply H' | apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
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

Lemma nhse_bseql_nosplit: forall t1 t2 pt loc ecc ecc' r s tr tr' p p' e e' H19,
    anno_parP pt t1 loc ->
    well_formed_r pt ->
    wf_ec ecc ->
    wf_ec (splitEv_l s ecc) -> 
    not_hash_sig_term_ev (abseq r s t1 t2) H19 ->
    copland_compileP pt
                     {|
                      st_ev := splitEv_l s ecc;
                      st_trace := tr;
                      st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->

    
    reconstruct_evP ecc H19 ->
    reconstruct_evP (splitEv_l s ecc) e ->
    reconstruct_evP ecc' e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  eassumption.
  6: { eassumption. }
  eassumption.
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
  | [H: well_formed_r ?pt,
        H': anno_parP ?pt ?t1 _,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_l ?s ?ecc),
                H4: not_hash_sig_term_ev (abseq _ ?s ?t1 _) ?H19,
                    H6: reconstruct_evP ?ecc ?H19,
                        H7: reconstruct_evP (splitEv_l ?s ?ecc) ?e,
                            H8: reconstruct_evP ?ecc' ?e',
                                H5: copland_compileP ?pt
                                                     {| st_ev := splitEv_l ?s ?ecc; st_trace := _; st_pl := _ |}
                                                     (Some tt)
                                                     {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseql_nosplit; [apply H' | apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.

Lemma nhse_bseqr_nosplit: forall t1 t2 pt loc ecc ecc' r s tr tr' p p' e e' H19,
    anno_parP pt t2 loc ->
    well_formed_r pt ->
    wf_ec ecc ->
    wf_ec (splitEv_r s ecc) -> 
    not_hash_sig_term_ev (abseq r s t1 t2) H19 ->
    copland_compileP pt
                     {|
                      st_ev := splitEv_r s ecc;
                      st_trace := tr;
                      st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->

    
    reconstruct_evP ecc H19 ->
    reconstruct_evP (splitEv_r s ecc) e ->
    reconstruct_evP ecc' e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  eassumption.
  6: { eassumption. }
  eassumption.
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
  | [H: well_formed_r ?pt,
        H': anno_parP ?pt ?t2 _,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_r ?s ?ecc),
                H4: not_hash_sig_term_ev (abseq _ ?s _ ?t2) ?H19,
                    H6: reconstruct_evP ?ecc ?H19,
                        H7: reconstruct_evP (splitEv_r ?s ?ecc) ?e,
                            H8: reconstruct_evP ?ecc' ?e',
                                H5: copland_compileP ?pt
                                                     {| st_ev := splitEv_r ?s ?ecc; st_trace := _; st_pl := _ |}
                                                     (Some tt)
                                                     {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseqr_nosplit; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.

Lemma nhse_bparl_nosplit: forall t1 t2 pt loc ecc ecc' r s tr tr' p p' e e' H19,
    anno_parP pt t1 loc ->
    well_formed_r pt ->
    wf_ec ecc ->
    wf_ec (splitEv_l s ecc) -> 
    not_hash_sig_term_ev (abpar r s t1 t2) H19 ->
    copland_compileP pt
                    {|
                      st_ev := splitEv_l s ecc;
                      st_trace := tr;
                      st_pl := p |}
                    (Some tt)
                    {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->

    
    reconstruct_evP ecc H19 ->
    reconstruct_evP (splitEv_l s ecc) e ->
    reconstruct_evP ecc' e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  eassumption.
  6: { eassumption. }
  eassumption.
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
  | [H: well_formed_r ?t1,
        H': anno_par ?pt ?t1 _,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_l ?s ?ecc),
                H4: not_hash_sig_term_ev (abpar _ ?s ?t1 _) ?H19,
                    H6: reconstruct_evP ?ecc ?H19,
                        H7: reconstruct_evP (splitEv_l ?s ?ecc) ?e,
                            H8: reconstruct_evP ?ecc' ?e',
                                H5: copland_compileP ?pt
                                                     {| st_ev := splitEv_l ?s ?ecc; st_trace := _; st_pl := _ |}
                                                     (Some tt)
                                                     {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bparl_nosplit; [apply H' | apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.

Lemma nhse_bparr_nosplit: forall t1 t2 pt loc ecc ecc' r s tr tr' p p' e e' H19,
    anno_parP pt t2 loc ->
    well_formed_r pt ->
    wf_ec ecc ->
    wf_ec (splitEv_r s ecc) -> 
    not_hash_sig_term_ev (abpar r s t1 t2) H19 ->
    copland_compileP pt
                    {|
                      st_ev := splitEv_r s ecc;
                      st_trace := tr;
                      st_pl := p |}
                    (Some tt)
                    {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->

    
    reconstruct_evP ecc H19 ->
    reconstruct_evP (splitEv_r s ecc) e ->
    reconstruct_evP ecc' e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  destruct ecc.
  eapply hshsig_ev_term_contra.
  eassumption.
  6: { eassumption. }
  eassumption.
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
  | [H: well_formed_r ?pt,
        H': anno_parP ?pt ?t2 _,
        H2: wf_ec ?ecc,
            H3: wf_ec (splitEv_r ?s ?ecc),
                H4: not_hash_sig_term_ev (abpar _ ?s _ ?t2) ?H19,
                    H6: reconstruct_evP ?ecc ?H19,
                        H7: reconstruct_evP (splitEv_r ?s ?ecc) ?e,
                            H8: reconstruct_evP ?ecc' ?e',
                                H5: copland_compileP ?pt
                                                     {| st_ev := splitEv_r ?s ?ecc; st_trace := _; st_pl := _ |}
                                                     (Some tt)
                                                     {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bparr_nosplit; [apply H' | apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8])
  end.


Ltac do_nhse_nosplit :=
  try do_nhse_bseql_nosplit;
  try do_nhse_bseqr_nosplit;
  try do_nhse_bparl_nosplit;
  try do_nhse_bparr_nosplit.

Lemma gg_preserved': forall t pt loc p et n p0 et'
                       tr e e' tr' p' bits ecc',

    anno_parP pt t loc ->
    well_formed_r pt ->
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    wf_ec (evc bits et) ->
    reconstruct_evP (evc bits et) e ->
    reconstruct_evP ecc' e' ->
    events t p et (sign n p0 et') ->
    copland_compileP pt
                     {| st_ev := (evc bits et); st_trace := tr; st_pl := p |}
                     (Some tt)
                     {| st_ev := ecc'; st_trace := tr'; st_pl := p' |} ->

    (
      (exists bits e'', EvSub (ggc p0 (do_sig (MonadVM.encodeEvBits (evc bits et')) p0 n) e'') e' /\
                   et_fun e'' = et'
      )
    ).
Proof.

  intros.
  generalizeEverythingElse t.
  
  induction t; intros.
  -
    wrap_ccp.
    subst.
    destruct a; try (ff; tauto).
    +
      ff.
      invEvents.
      ff.
      do_rewrap_reconP.
      do_reconP_determ.

      repeat eexists.
      econstructor.
      symmetry.
     
      
      eapply etfun_reconstruct; eauto.

  - (* aatt case *)

    wrap_ccp.
    invEvents.
    (*
    do_wf_pieces. *)
    do_not_none.

    

    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
     
    
    (*
    invc H1. *)

  
    do_not_hshsig.



  

    do_assume_remote t (evc bits et) n HHH.

    (*
    
    assert (exists l' t', anno_par t 0 = (l',t')).
    {
      destruct (anno_par t 0).
      repeat eexists.
    }     
    destruct_conjs.
     *)
    

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
    (*
    assert (t = unannoPar H12).
    {
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
    }
    subst.
     *)
    
    
    eapply copland_compile_at.
    eapply wfr_annt_implies_wfr_par.
    eassumption.
    econstructor.
    rewrite H11.
    tauto.
    
  - (* alseq case *)

    wrap_ccp.
    do_not_none.

    (*
    invc H2; destruct_conjs.
    do_not_hshsig.
     *)
    

    

    assert (not_hash_sig_term t1 /\ not_hash_sig_term t2).
    {
      eapply not_hshsig_alseq_pieces.
      invc H2.
      eassumption.
    }
    destruct_conjs.
    

    (*
    
    
    
    do_not_hshsig. *)
    (*
    ff.
    dosome.
    ff.
    vmsts.
    ff.
     *)
    

    invEvents.
    + (* t1 case *)
      
      do_wfec_preserved.
      do_somerecons.

      do_reconP_determ.

      (*

      repeat jkjke'.
      repeat ff.
      repeat jkjke'.

     
      rewrite fold_recev in *.
       *)
      
      destruct ecc'; destruct st_ev0.
      (*
      ff.
      rewrite fold_recev in *.
       *)
      


      (*
      Print do_nhste_lseqr.
      do_nhste_lseqr.

      Print do_nhste_lseqr.

      do_nhste_lseqr.


      assert (not_hash_sig_term_ev t2 H15).
      {
        
        eapply sig_term_ev_lseqr.
        apply Heqp1.
        eassumption.
      
        2: { eassumption. }
        2: { eassumption. }
        eassumption.
        eassumption.
        eassumption.
      }
      

      Print do_ste.
      Print do_nhste_lseqr.
      do_nhste_lseqr.
      Print do_nhste_lseql.

      do_nhste_lseql.
      Print do_nhst_lseqr.
      do_nhst_lseqr.
       *)

      Print do_ste.

      Print do_nhste_lseql.
      
      

      repeat do_ste.

      
      edestruct IHt1.
      eassumption.
      eassumption.
      (*
      eapply sig_term_ev_lseq; eassumption. *)
      eassumption.
      5: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
      2: { eassumption. }
      eassumption.

      destruct_conjs.

      (*

      repeat jkjke'.
      repeat ff.
      repeat jkjke'.
      repeat ff.
      repeat jkjke'.
      repeat ff.

      rewrite fold_recev in *.
       *)
      

      do_evaccum.

      door.
      +++
        eauto.
      +++
        dd.
        
        unfold not_hash_sig_ev in H22.
        (*
        specialize H21 with (e':=(hhc H26 H27 H25)).
         *)
        
        unfold not in *.
        exfalso.
        eapply H22.
        econstructor.
        repeat eexists.
        eassumption.
        eassumption.       
        
    + (* t2 case *)

      wrap_ccp.

      (*

      do_pl_immut.
      do_pl_immut.
      subst.
       *)
      

      do_wfec_preserved.
      do_somerecons.
      do_reconP_determ.
      destruct st_ev0;
      destruct ecc'.

      assert (e0 = (aeval t1 p et)).
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

      (*

      rewrite fold_recev in *.
      repeat jkjke'.
      repeat ff.
      rewrite fold_recev in *.
       *)
      

      repeat do_ste.

      edestruct IHt2.
      eassumption.
      eassumption.
      (*
      eapply sig_term_ev_lseqr. *)
      eassumption.
      (*
      apply H2. *)
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

    (*
    do_wf_pieces. *)
    do_not_none.
   

    Print do_not_hshsig.
    Print do_not_hshsig_abseq_pieces.
    
    do_not_hshsig.
    (*
    ff.
    dosome.
    ff.
    vmsts.
    ff. *)

    do_rewrap_reconP.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      (*repeat do_pl_immut; *)
      do_somerecons;
      (*
      do_reconP_determ;
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons; *)
        try do_evsub_ihhh'.

    +

      do_reconP_determ.

      (*

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.
      repeat rewrite fold_recev in *.
       *)
      

      Print do_nhse_nosplit.
      Print do_nhse_bseql_nosplit.
      (*
Ltac do_nhse_bseql_nosplit :=
  match goal with
  | H:well_formed_r ?pt,
    H':anno_parP ?pt ?t1 _,
    H2:wf_ec ?ecc,
    H3:wf_ec (splitEv_l ?s ?ecc),
    H4:not_hash_sig_term_ev (abseq _ ?s ?t1 _) ?H19,
    H6:Some ?H19 = reconstruct_ev ?ecc,
    H7:Some ?e = reconstruct_ev (splitEv_l ?s ?ecc),
    H8:Some ?e' = reconstruct_ev ?ecc',
    H5:copland_compileP ?pt {| st_ev := splitEv_l ?s ?ecc; st_trace := _; st_pl := _ |} (Some tt)
         {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}
    |- _ =>
        assert_new_proof_by (not_hash_sig_ev e')
         ltac:(eapply nhse_bseql_nosplit; [ apply H' | apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8 ])
  end
       *)
      

      do_nhse_nosplit.  
      
      destruct s; destruct s; destruct s0; ff.
        (*rewrite fold_recev in *. *)

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
        destruct_conjs; eauto.
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
        destruct_conjs; eauto.
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
        destruct_conjs; eauto.
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
        destruct_conjs; eauto.

    +

      (*

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.
      repeat rewrite fold_recev in *.
       *)
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
        destruct_conjs; eauto.
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
        destruct_conjs; eauto.
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
        destruct_conjs; eauto.
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
        destruct_conjs; eauto.

  - (* abseq case *)
    wrap_ccp.
    ff.
    inversion H2.
    destruct_conjs.

    (*
    do_wf_pieces. *)
    do_not_none.
    (*
    rewrite fold_recev in *.
     *)
    do_reconP_determ.

    Print do_not_hshsig.
    Print do_not_hshsig_abseq_pieces.
    
    do_not_hshsig.
    (*
    ff.
    dosome.
    ff.
    vmsts.
    ff. *)

    do_rewrap_reconP.

    Print do_evsub_ihhh'.
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
      (*
      repeat jkjke'; ff;
        try (rewrite fold_recev in * );
        try do_somerecons; *)
        try do_evsub_ihhh'.

    +

      do_reconP_determ.

      (*

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.
      repeat rewrite fold_recev in *.
       *)
      

      Check nhse_bparl_nosplit.
      Print do_nhse_bparl_nosplit.
      (*
Ltac do_nhse_bparl_nosplit :=
  match goal with
  | H:well_formed_r ?t1,
    H':anno_par ?pt ?t1 _,
    H2:wf_ec ?ecc,
    H3:wf_ec (splitEv_l ?s ?ecc),
    H4:not_hash_sig_term_ev (abpar _ ?s ?t1 _) ?H19,
    H6:reconstruct_evP ?ecc ?H19,
    H7:reconstruct_evP (splitEv_l ?s ?ecc) ?e,
    H8:reconstruct_evP ?ecc' ?e',
    H5:copland_compileP ?pt {| st_ev := splitEv_l ?s ?ecc; st_trace := _; st_pl := _ |} (Some tt)
         {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}
    |- _ =>
        assert_new_proof_by (not_hash_sig_ev e')
         ltac:(eapply nhse_bparl_nosplit; [ apply H' | apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6 | apply H7 | apply H8 ])
  end
       *)
      
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
        destruct_conjs; eauto.
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
        destruct_conjs; eauto.
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

        destruct_conjs; eauto.
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

        destruct_conjs; eauto.

    +
      do_reconP_determ.

      (*
      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.
      repeat rewrite fold_recev in *. *)

      

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
        rewrite Heqe2.
        eassumption.


        (*
        rewrite Heqe2.
        symmetry.
        eassumption.
        



        
        econstructor.
        eassumption.
        eassumption.
        4: { eassumption. }
        eassumption.
        simpl.
        ff.
        2: { eassumption. }
        eassumption. *)
        
        destruct_conjs; eauto.
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
        rewrite Heqe2.
        eassumption.

        destruct_conjs; eauto.
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
        rewrite Heqe2.
        eassumption.



        (*
        rewrite Heqe2.
        symmetry.
        eassumption.
        



        
        econstructor.
        eassumption.
        eassumption.
        4: { eassumption. }
        eassumption.
        simpl.
        ff.
        2: { eassumption. }
        eassumption. *)
        
        destruct_conjs; eauto.
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
        rewrite Heqe2.
        eassumption.

        destruct_conjs; eauto.
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

(*
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
    
    HERE

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
*)

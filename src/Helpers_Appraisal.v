Require Import Term ConcreteEvidence Appraisal_Defs StVM Impl_VM Impl_appraisal Auto AutoApp External_Facts Helpers_VmSemantics Appraisal_Evidence VmSemantics Evidence_Bundlers AutoPrim Axioms_Io IO_Stubs.

Require Import StructTactics.

Require Import Coq.Program.Tactics Lia.

Require Import OptMonad.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)

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

Lemma recon_build_app : forall e',
      exists bits,
        reconstruct_evP (evc bits (et_fun e')) (build_app_comp_evC e').
Proof.
  intros.
  induction e';
    ff.
  -
    exists [].
    econstructor.
    repeat ff.
    tauto.
  -
    exists [(checkNonceF n b)].
    econstructor.
    repeat ff.
  -
    destruct_conjs.
    invc H.
    ff.
    exists ([(checkASPF a b)] ++ IHe').
    econstructor.
    repeat ff.
  -
    destruct_conjs.
    invc H.
    ff.
    exists ([(checkSigF e' p b)] ++ IHe').
    econstructor.
    repeat ff.
  -
    exists [(checkHashF e p b)].
    econstructor.
    repeat ff.
  -
    destruct_conjs.
    invc H0; invc H.
    repeat ff.
    exists (IHe'1 ++ IHe'2).
    assert (wf_ec (evc IHe'1 (et_fun e'1))).
    {
      eapply wf_recon.
      econstructor.
      eassumption.
    }
    assert (wf_ec (evc IHe'2 (et_fun e'2))).
    {
      eapply wf_recon.
      econstructor.
      eassumption.
    }
    econstructor.
    repeat ff;
    
    try do_wfec_firstn;
    try do_wfec_skipn;
    try clear_skipn_firstn.
    
    jkjke'.
    jkjke'.
    invc Heqo.
    invc Heqo0.
    tauto.

    jkjke'.
    jkjke'.
    solve_by_inversion.

    rewrite H3 in *.
    rewrite Heqo in *.
    solve_by_inversion.
  -
        destruct_conjs.
    invc H0; invc H.
    repeat ff.
    exists (IHe'1 ++ IHe'2).
    assert (wf_ec (evc IHe'1 (et_fun e'1))).
    {
      eapply wf_recon.
      econstructor.
      eassumption.
    }
    assert (wf_ec (evc IHe'2 (et_fun e'2))).
    {
      eapply wf_recon.
      econstructor.
      eassumption.
    }
    econstructor.
    repeat ff;
    
    try do_wfec_firstn;
    try do_wfec_skipn;
    try clear_skipn_firstn.
    
    jkjke'.
    jkjke'.
    invc Heqo.
    invc Heqo0.
    tauto.

    jkjke'.
    jkjke'.
    solve_by_inversion.

    rewrite H3 in *.
    rewrite Heqo in *.
    solve_by_inversion.
Defined.

Lemma uuc_app: forall e' e'' params p n,
    EvSub (uuc params p n e'') e' ->
    exists bits' e''',
      reconstruct_evP (evc bits' (et_fun e'')) e''' /\
      EvSub (uuc params p (checkASPF params n) e''')
                 (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff.
    
  -
    edestruct recon_build_app.
    evSubFacts.
    eexists.
    eexists.
    split.
    2: {
      econstructor.
    }
    eassumption.

    edestruct IHe'.
    eassumption.
    destruct_conjs.
    eauto.
  -
    evSubFacts.
    edestruct IHe'.
    eassumption.
    destruct_conjs.
    eauto.
  -
    evSubFacts.
    +
      edestruct IHe'1.
      eassumption.
      destruct_conjs.
      eauto.
    +
      edestruct IHe'2.
      eassumption.
      destruct_conjs.
      eauto.
  -
    evSubFacts.
    +
      edestruct IHe'1.
      eassumption.
      destruct_conjs.
      eauto.
    +
      edestruct IHe'2.
      eassumption.
      destruct_conjs.
      eauto.
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
    | [H: context [_ -> _],
              H3: wf_ec ?e,
                  H4: copland_compileP ?t
                                       {| st_ev := ?e; st_trace := _; st_pl := _ |}
                                       (_)
                                       {| st_ev := ?e'; st_trace := _; st_pl := _ |}
       |- _ ] => 
      assert_new_proof_by
        (wf_ec e')
        
        ltac:(eapply H; [apply H3 | apply H4])
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
    not_none_none t ->
    anno_parP pt t ->
    copland_compileP pt
                     {| st_ev := evc e et; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := evc e' et'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
    EvSubT ett et ->
    EvSubT ett et'.
Proof.
  intros.
  
  assert (et' = eval t p et).
  {
    eapply cvm_refines_lts_evidence; eauto.
  }
  subst.

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
    exists (uuc a p default_bs IHy).
    ff.
  -
    destruct_conjs.
    exists (ggc p default_bs IHy).
    ff.
  -
    destruct_conjs.
    exists (hhc p default_bs y).
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

Lemma recon_evdenote_decomp: forall a p e,
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

Ltac do_evsub_ih'' :=
  match goal with
  | [ H3: reconstruct_evP ?stev ?v

    |- context[EvSub ?e'' _ \/ _]] =>

    assert
      (EvSub e'' v \/
       (exists (ett : Evidence) p'0 bs,
           EvSub (hhc p'0 bs ett) v /\ EvSubT (et_fun e'') ett))
  end.

Lemma evAccum: forall t annt p e e' e'',

    annoP annt t -> 
    not_none_none t ->
    cvm_evidence_denote annt p e = e' -> 
    EvSub e'' e ->

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
    inv_annoP.
    dd.
    destruct a; dd; eauto.
    right.
    repeat eexists.
    econstructor.
    eapply evsub_etfun.
    eassumption.
  - (* aatt case *)
    inv_annoP.
    dd.
    do_not_none.
    edestruct IHt.
    econstructor. repeat eexists. eassumption.
    eassumption.
    reflexivity.
    eassumption.
    eauto.
    eauto.
  - (* alseq case *)
    dd.
    inv_annoP.
    dd.
    repeat do_anno_redo.
    do_not_none.
    edestruct recon_evdenote_decomp with (a:=a) (p:=p) (e:=e).
    destruct x.
    
    do_evsub_ih''. (* IHt1 *)
    
    {
      eapply IHt1; eauto.
      
    }
    
    door.
    ++
      eapply IHt2; eauto.
    ++
      
      assert
        (EvSub (hhc H8 H9 H7) (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)) \/
         (exists (ett : Evidence) p'0 bs,
             EvSub (hhc p'0 bs ett) (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)) /\ EvSubT (et_fun (hhc H8 H9 H7)) ett)).
      {
        eapply IHt2;
          try eassumption;
          try reflexivity.
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

    inv_annoP.
    dd.
    repeat do_anno_redo.
    do_not_none.

    destruct s; destruct s; destruct s0;
      dd.

    +
      edestruct IHt1; eauto.
      destruct_conjs.
      right.
      repeat eexists; eauto.

    +
      edestruct IHt1; eauto.

      destruct_conjs.
      right.
      repeat eexists; eauto.
    +
      edestruct IHt2; eauto.
      destruct_conjs.
      right.
      repeat eexists; eauto.
    +
      do_none_none_contra.
  - (* abpar case *)

    inv_annoP.
    dd.
    repeat do_anno_redo.
    do_not_none.

    destruct s; destruct s; destruct s0;
      dd.

    +
      edestruct IHt1; eauto.

      destruct_conjs.
      right.
      repeat eexists; eauto.

    +
      edestruct IHt1; eauto.

      destruct_conjs.
      right.
      repeat eexists; eauto.
    +
      edestruct IHt2; eauto.
      destruct_conjs.
      right.
      repeat eexists; eauto.
    +
      do_none_none_contra.
Defined.

Ltac do_evaccum e' :=
  repeat 
    match goal with
    | [H5: EvSub ?e'' _,
           (*H6: cvm_evidence_denote ?annt _ ?e = ?e', *)
           (*e': EvidenceC, *)
               H7: not_none_none ?t,
                   H8: annoP _ ?t

        |- _] =>
      
      assert_new_proof_by
        (EvSub e'' e' \/
         (exists (ett : Evidence) p'0 bs,
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett))
        ltac: (eapply evAccum; [apply H8 (*| apply H *) | apply H7 (*| apply H2 | apply H3 | apply H4*) | try eassumption; try reflexivity | apply H5])
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

Lemma sig_is: forall t annt e e' p,

    annoP annt t ->
    cvm_evidence_denote annt p e = e' ->
    gg_sub e' ->
    gg_sub e \/
    term_sub (asp SIG) t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ff.
  -
    dd.
    
    destruct a; inv_annoP; dd; eauto; try tauto.
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
    inv_annoP.
    dd.
    
    edestruct IHt.
    econstructor. repeat eexists. eassumption.
    reflexivity.
    eassumption.
    eauto.
    eauto.
    
  -
    inv_annoP.
    dd.

    assert (gg_sub (cvm_evidence_denote a p e) \/ term_sub (asp SIG) t2).
    {
      eapply IHt2.
      econstructor. repeat eexists. eassumption.
      reflexivity.
      eassumption.
    }

    door.
    +
      edestruct IHt1.
      econstructor. repeat eexists. eassumption.
      reflexivity.
      eauto.
      eauto.
      eauto.
    +
      eauto.

  - (* abseq case *)
    inv_annoP.
    dd.

    do_ggsub.
    evSubFacts.
    +

      edestruct IHt1.
      econstructor. repeat eexists. eassumption.
      reflexivity.

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
      econstructor. repeat eexists. eassumption.
      reflexivity.
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
    inv_annoP.
    dd.

    do_ggsub.
    evSubFacts.
    +

      edestruct IHt1.
      econstructor. repeat eexists. eassumption.
      reflexivity.
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
      econstructor. repeat eexists. eassumption.
      reflexivity.
      

      repeat eexists.
      eassumption.
      destruct_conjs; subst.
      left. repeat eexists.
      destruct s; destruct s; destruct s0;
        dd;
        try solve_by_inversion;
        eauto.
      right.
      eauto.
Defined.

Ltac do_sig_is He :=
  repeat 
  match goal with
  | [ H': annoP ?annt ?t,
          H6: gg_sub ?e'
              (*He: EvidenceC *)
     |- _] =>
    
    assert_new_proof_by
      (gg_sub He \/ (term_sub (asp SIG) t))
      ltac:(eapply sig_is; [apply H' | try eassumption; try reflexivity |  apply H6])
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
      ltac:(eapply sig_term_ev_lseq; [apply H ])
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
      ltac:(eapply nhst_lseq_r; [apply H])
  end.

Ltac do_nhste_bseql :=
  match goal with
  | [H: not_hash_sig_term_ev (bseq ?s ?t1 _) ?e
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 (splitEvl s e))
      ltac:(eapply sig_term_ev_bseql; [apply H])
  end.

Ltac do_nhste_bseqr :=
  match goal with
  | [H: not_hash_sig_term_ev (bseq ?s _ ?t2) ?e 
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 (splitEvr s e))
      ltac:(eapply sig_term_ev_bseqr; [apply H])
  end.

Ltac do_nhste_bparl :=
  match goal with
  | [H: not_hash_sig_term_ev (bpar ?s ?t1 _) ?e
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t1 (splitEvl s e))
      ltac:(eapply sig_term_ev_bparl; [apply H])
  end.

Ltac do_nhste_bparr :=
  match goal with
  | [H: not_hash_sig_term_ev (bpar ?s _ ?t2) ?e
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term_ev t2 (splitEvr s e))
      ltac:(eapply sig_term_ev_bparr; [apply H])
  end.

Lemma gg_recons'': forall e x y,
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

Lemma hshsig_ev_term_contra: forall t annt p e e',

    annoP annt t ->
    not_hash_sig_term_ev t e ->
    cvm_evidence_denote annt p e = e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    inv_annoP.
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

    eapply not_hshsig_uuc; eauto.
    +
    repeat ff.
    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    unfold cons_sig in *.
    ff.
      
    eapply not_hshsig_ggc; eauto.
    +
      assert (~ (gg_sub e)).
      {
        unfold not_hash_sig_term_ev in *.
        destruct_conjs.
        unfold not in *; intros.
        apply H3.
        eassumption.
        eauto.
      }
      unfold not_hash_sig_term_ev in *.
      destruct_conjs.
      
      unfold not_hash_sig_ev.
      intros.
      unfold not in *; intros.
      invc H5.
      unfold hash_sig_ev in *.
      destruct_conjs.
      invc H6.
      invc H13.
      apply H1.

      eapply gg_recons''; eauto.

  - (* aatt case *)

    inv_annoP.
    dd.
    
    do_nhste_att.
     
    eapply IHt.
    econstructor. repeat eexists. eassumption.
    eassumption.
    reflexivity.
        
  - (* alseq case *)

    inv_annoP.
    dd.
    repeat do_anno_redo.
        
    do_nhste_lseql.
    
    assert (not_hash_sig_ev (cvm_evidence_denote a p e)) by eauto.

    do_nhst_lseqr.

    eapply IHt2.
    eassumption.
      
    2: { reflexivity. }
    split.
    eassumption.
    split.
    eassumption.
    intros.
    unfold not.
    intros.

    do_sig_is e.
    
    door.
    ++

      unfold not_hash_sig_term_ev in H0.
      destruct_conjs.
      unfold not in H10.
      eapply H10.
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


    inv_annoP.
    dd.
    repeat do_anno_redo.
        
    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
        
    do_nhste_bseql.
    do_nhste_bseqr.
    
    evSubFacts.

    +
      invc H1.
      
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

      eapply H3; eassumption.

    +
      assert (not_hash_sig_ev (cvm_evidence_denote a0 p (splitEvr s e))) by eauto.
      eapply H3; eassumption.
  - (* bpar case *)
    
    inv_annoP.
    dd.
    repeat do_anno_redo.
       
    unfold not_hash_sig_ev.
    intros.
    unfold not.
    intros.
        
    do_nhste_bparl.
    do_nhste_bparr.
    
    evSubFacts.

    +
      invc H1.
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

      eapply H3; eassumption.

    +
      assert (not_hash_sig_ev (cvm_evidence_denote a0 p (splitEvr s e))) by eauto.
      eapply H3; eassumption.
Defined.

Ltac do_hste_contra He :=
  repeat 
  match goal with
  | [H': annoP ?annt ?t,
         H3: not_hash_sig_term_ev ?t ?e
             (*He: EvidenceC *)
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev He)
      ltac:(eapply hshsig_ev_term_contra; [apply H' | apply H3 | try eassumption; reflexivity])
  end.

Lemma sig_term_ev_lseqr: forall t1 t2 annt e e' p,
    annoP annt t1 ->
    not_hash_sig_term_ev (lseq t1 t2) e ->
    cvm_evidence_denote annt p e = e' ->  
    not_hash_sig_term_ev t2 e'.
Proof.
  intros.
  
  do_nhste_lseql.
  do_nhst_lseqr.

  split; try eassumption.

  do_hste_contra e'.

  -
    split; try eassumption.
    +
      intros.
      unfold not; intros.

      do_sig_is e.
      door.

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

Ltac do_nhste_lseqr :=
  match goal with
  | [H': annoP ?annt ?t1,
         H3: not_hash_sig_term_ev (lseq ?t1 ?t2) ?e
        |- _] =>
    edestruct sig_term_ev_lseqr;
      [apply H' | apply H3 |
      try eassumption; try reflexivity | idtac ]
  end.

Lemma uu_preserved': forall t annt p n p0 e e' params et,

    annoP annt t ->
    not_none_none t ->
    events annt p (et_fun e) (umeas n p0 params et) ->
    cvm_evidence_denote annt p e = e' ->

    (
      (exists bits'' e'',
          (reconstruct_evP (evc bits'' et) e'' /\
          EvSub (uuc params p0 (do_asp params p0 n) e'') e')) \/
      (exists ett p' bs,
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu params p0 et) ett)
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    inv_annoP.
    dd.

        
    destruct a; ff.
    +
      invEvents.

      unfold cons_uu in *.
      repeat ff.
      left.
      exists (encodeEv e).
      eexists.
      split.
      econstructor.
      eapply recon_same.
      econstructor.
  -
    inv_annoP.
    dd.

    do_anno_redo.
       
    inv_events.

    do_not_none.
    inv_annoP.

    do_assume_remote t (evc (encodeEv e) (et_fun e)) n (S H4) HHH.
    do_annopar_redo.

    eapply IHt;
      try eassumption;
      try reflexivity.  
  -
    inv_annoP.
    dd.
    repeat do_anno_redo.
    
    do_not_none.

    invEvents.
    + (* t1 case *)

      edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      reflexivity.

      destruct_conjs.

      do_evaccum (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)).
      door.

      ++
        left.
        eauto.
        
      ++
        assert (et = et_fun H6).
        {
          eapply etfun_reconstruct.
          eassumption.
        }
        subst.

        right.
        repeat (eexists; eauto).
      ++
        destruct_conjs.

        do_evaccum (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)).
        door.
        +++
          right.
          repeat (eexists; eauto).
        +++
          
          destruct_conjs.
          right.
          repeat eexists.
          eauto.

          eapply evsubT_transitive.
          eapply hhSubT.
          eassumption.
          eassumption.
          
    + (* t2 case *)

      assert (et_fun (cvm_evidence_denote a p e) = (aeval a p (et_fun e))).
      {
        eapply cvm_ev_denote_evtype.
      }
        
      edestruct IHt2.
      eassumption.
      eassumption.
      rewrite H1.
      eassumption.
      reflexivity.

      destruct_conjs.

      ++
        eapply IHt2.
        eassumption.
        eassumption.
        rewrite H1.
        eassumption.
        reflexivity.
      ++
        destruct_conjs;
          right;
          repeat (eexists; eauto).

  - (* abseq case *)

    inv_annoP.
    dd.
    repeat do_anno_redo.
    do_not_none.

    invEvents.
    +
      destruct s; destruct s; destruct s0; dd.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H6.
          eassumption.

          eauto.
          (*
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)). *)
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H6. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        assert (mt = et_fun mtc) by tauto.
        edestruct IHt1.
        eassumption.
        eassumption.
        rewrite <- H1.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H7. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
          
      ++
        exfalso.
        eapply not_none_none_contra_bseq; eauto.
    +
      destruct s; destruct s; destruct s0; dd.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H6. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        assert (mt = et_fun mtc) by tauto.
        edestruct IHt2.
        eassumption.
        eassumption.
        rewrite <- H1.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H7. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H6. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        exfalso.
        eapply not_none_none_contra_bseq; eauto.

  - (* new abpar case *)

    inv_annoP.
    dd.
    repeat do_anno_redo.
  
    do_not_none.

    invEvents.

    +
      destruct s; destruct s; destruct s0; dd.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H6. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H6. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        assert (mt = et_fun mtc) by tauto.
        edestruct IHt1.
        eassumption.
        eassumption.
        rewrite <- H1.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H7. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        exfalso.
        eapply not_none_none_contra_bpar; eauto.
    + (* t2 case *)
      destruct s; destruct s; destruct s0; dd.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H6. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        assert (mt = et_fun mtc) by tauto.
        edestruct IHt2.
        eassumption.
        eassumption.
        rewrite <- H1.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H7. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eassumption.
        reflexivity.
        destruct_conjs.
        +++
          left.
          repeat eexists.
          invc H6. eassumption.
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
        +++
          try eauto;
          try (destruct_conjs;
               right;
               repeat (eexists; eauto)).
      ++
        exfalso.
        eapply not_none_none_contra_bpar; eauto.
Defined.

Lemma uu_preserved:
  forall t1 t2 annt p n p0 e e''' e' params et,
    annoP annt t1 ->
    not_none_none t1 ->
    not_none_none t2 ->
    events annt p (et_fun e) (umeas n p0 params et) ->
    cvm_evidence_denote annt p e = e''' ->
    cvm_evidence_denote annt p e''' = e' ->
    
    (
      (exists bits'' e'',
          (reconstruct_evP (evc bits'' et) e'' /\
           EvSub (uuc params p0 (do_asp params p0 n) e'') e')) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu params p0 et') ett)
    ).
Proof.
  intros.
  
  assert (
      (exists bits'' e'',
          (reconstruct_evP (evc bits'' et) e'' /\
           EvSub (uuc params p0 (do_asp params p0 n) e'') e''')) \/
      (exists ett p' bs,
          EvSub (hhc p' bs ett) e''' /\
          EvSubT (uu params p0 et) ett)
    ).
  {
    eapply uu_preserved'.
    apply H.
    eassumption.
    eassumption.
    tauto.
  }
  rewrite <- H3 in *; clear H3.
  door.
  +
    do_evaccum (cvm_evidence_denote annt p (cvm_evidence_denote annt p e)).
    clear H7.
  
    door.
    ++
      
      left.
      eexists.
      jkjke'.
    ++
      
      

    right;
      (repeat eexists; eauto).
    jkjke'.
  +
    do_evaccum (cvm_evidence_denote annt p (cvm_evidence_denote annt p e)).
    door.
    ++
      right.
      repeat (eexists; eauto).
      jkjke'.
    ++
      assert (EvSubT (uu params p0 et) H9).
      {
        eapply evsubT_transitive.
        apply hhSubT.
        eassumption.
        eassumption.
      }
      
      right; 
        repeat (eexists; eauto).
      jkjke'.
Defined.

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

Lemma nhse_bseql_nosplit: forall t1 t2 annt s p e e',
    annoP annt t1 ->
    not_hash_sig_term_ev (bseq s t1 t2) e ->
    cvm_evidence_denote annt p (splitEvl s e) = e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  eapply hshsig_ev_term_contra.
  eassumption.
  eapply sig_term_ev_bseql.
  eassumption.
  destruct s; destruct s; destruct s0; ff.
Defined.

Ltac do_nhse_bseql_nosplit :=
  match goal with
  | [H': annoP ?annt ?t1,
            H4: not_hash_sig_term_ev (bseq ?s ?t1 _) _,
                e': EvidenceC 
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseql_nosplit; [apply H'
                                       | apply H4
                                       | try eassumption; try reflexivity])
  end.

Lemma nhse_bseqr_nosplit: forall t1 t2 annt s p e e',
    annoP annt t2 ->
    not_hash_sig_term_ev (bseq s t1 t2) e ->
    cvm_evidence_denote annt p (splitEvr s e) = e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  eapply hshsig_ev_term_contra.
  eassumption.
  eapply sig_term_ev_bseqr.
  eassumption.
  destruct s; destruct s; destruct s0; ff.
Defined.

Ltac do_nhse_bseqr_nosplit :=
  match goal with
  | [H': annoP ?annt ?t2,
            H4: not_hash_sig_term_ev (bseq ?s _ ?t2) _,
                e': EvidenceC 
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseqr_nosplit; [apply H'
                                       | apply H4
                                       | try eassumption; try reflexivity])
  end.



Lemma nhse_bparl_nosplit: forall t1 t2 annt s p e e',
    annoP annt t1 ->
    not_hash_sig_term_ev (bpar s t1 t2) e ->
    cvm_evidence_denote annt p (splitEvl s e) = e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  eapply hshsig_ev_term_contra.
  eassumption.
  eapply sig_term_ev_bparl.
  eassumption.
  destruct s; destruct s; destruct s0; ff.
Defined.

Ltac do_nhse_bparl_nosplit :=
  match goal with
  | [H': annoP ?annt ?t1,
            H4: not_hash_sig_term_ev (bpar ?s ?t1 _) _,
                e': EvidenceC 
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseqr_nosplit; [apply H'
                                       | apply H4
                                       | try eassumption; try reflexivity])
  end.

Lemma nhse_bparr_nosplit: forall t1 t2 annt s p e e',
    annoP annt t2 ->
    not_hash_sig_term_ev (bpar s t1 t2) e ->
    cvm_evidence_denote annt p (splitEvr s e) = e' ->
    not_hash_sig_ev e'.
Proof.
  intros.
  eapply hshsig_ev_term_contra.
  eassumption.
  eapply sig_term_ev_bparr.
  eassumption.
  destruct s; destruct s; destruct s0; ff.
Defined.

Ltac do_nhse_bparr_nosplit :=
  match goal with
  | [H': annoP ?annt ?t2,
            H4: not_hash_sig_term_ev (bpar ?s _ ?t2) _,
                e': EvidenceC 
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bparr_nosplit; [apply H'
                                       | apply H4
                                       | try eassumption; try reflexivity])
  end.

Ltac do_nhse_nosplit :=
  try do_nhse_bseql_nosplit;
  try do_nhse_bseqr_nosplit;
  try do_nhse_bparl_nosplit;
  try do_nhse_bparr_nosplit.

Lemma gg_preserved':
  forall t annt p n p0 et' e e',
    annoP annt t ->
    not_none_none t ->
    not_hash_sig_term_ev t e ->
    events annt p (et_fun e) (sign n p0 et') ->
    cvm_evidence_denote annt p e = e' ->
    
    (
      (exists bits e'', EvSub (ggc p0 (do_sig (encodeEvBits (evc bits et')) p0 n) e'') e' /\
                   et_fun e'' = et' /\
                   bits = encodeEv e''
      )
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    inv_annoP.
    dd.
    destruct a; try (ff; tauto).
    +
      ff.
      invEvents.
      ff.
      repeat eexists.
      
      unfold encodeEvBits in *.
      econstructor.
      
  - (* aatt case *)

    inv_annoP.
    dd.
    do_anno_indexed_redo.
    invEvents.
    do_not_none.

    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    do_not_hshsig.

    do_assume_remote t (evc (encodeEv e) (et_fun e)) n (S H4) HHH.

    eapply IHt.
    econstructor. repeat eexists. invc Heqp2. eassumption.
    
    eassumption.
    split.
    eassumption.
    split.
    eassumption.
    
    intros.
    unfold not in *; intros.
    do_hsh_subt.
    do_ggsub.
    
    eapply H5.
    repeat eexists.
    eassumption.
    econstructor.
    eauto.
    eassumption.
    reflexivity.
        
  - (* alseq case *)

    inv_annoP.
    dd.
    repeat do_anno_redo.
    do_not_none.
    
    assert (not_hash_sig_term t1 /\ not_hash_sig_term t2).
    {
      eapply not_hshsig_alseq_pieces.
      invc H1.
      eassumption.
    }
    destruct_conjs.
    
    invEvents.
    + (* t1 case *)

      try do_nhste_lseql.
      try do_nhste_lseqr.
      destruct_conjs.

      do_hste_contra (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)).
      
      edestruct IHt1; try eassumption; try reflexivity.

      destruct_conjs.
      subst.

      do_evaccum (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)).
      door.

      +++
        eauto.
      +++
        destruct_conjs.
        dd.
            
        unfold not_hash_sig_ev in H12.
        
        unfold not in *.
        exfalso.
        eapply H12.
        econstructor.
        repeat eexists.
        eassumption.
        eassumption.       
        
    + (* t2 case *)
  
      do_ste.
      destruct_conjs.
      do_hste_contra (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)).
      
      assert (et_fun ((cvm_evidence_denote a p e)) =  (aeval a p (et_fun e))).
      {
        eapply cvm_ev_denote_evtype.
      }
      
      edestruct IHt2.
      eassumption.
      eassumption.
      2: { jkjke.  }
      
      econstructor.
      eassumption.
      split; try eassumption.
      reflexivity.

      eauto.
      
  - (* abseq case *)

    inv_annoP.
    dd.
    repeat do_anno_redo.
    do_not_none.

    invEvents.
    
    +
      destruct s; destruct s; destruct s0; ff.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseql.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
    +
      destruct s; destruct s; destruct s0; ff.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bseqr.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.


  - (* abpar case *)

    inv_annoP.
    dd.
    repeat do_anno_redo.
    do_not_none.

    invEvents.
    
    +
      destruct s; destruct s; destruct s0; ff.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt1.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparl.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
    +
      destruct s; destruct s; destruct s0; ff.

      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
      ++
        edestruct IHt2.
        eassumption.
        eassumption.
        eapply sig_term_ev_bparr.
        eassumption.
        dd. eassumption.
        reflexivity.
        destruct_conjs.
        esplit; eauto.
        Unshelve.
        eauto.
Defined.

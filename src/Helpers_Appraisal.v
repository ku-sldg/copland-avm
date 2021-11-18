Require Import Term ConcreteEvidence Appraisal_Defs StVM Impl_vm Impl_appraisal Auto AutoApp External_Facts Helpers_VmSemantics Appraisal_Evidence VmSemantics Evidence_Bundlers AutoPrim Axioms_Io IO_Stubs.

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
    anno_parP pt t 0 ->
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

Lemma evAccum: forall t annt p e e' e'' i,

    annoP annt t i -> 
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
    dd.
    invc H.
    dd.
    destruct a; dd; eauto.
    right.
    repeat eexists.
    econstructor.
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
      (EvSub (hhc H5 H6 H4) (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)) \/
       (exists (ett : Evidence) p'0 bs,
           EvSub (hhc p'0 bs ett) (cvm_evidence_denote a0 p (cvm_evidence_denote a p e)) /\ EvSubT (et_fun (hhc H5 H6 H4)) ett)).
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
    dd.
    invc H.
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

    dd.
    invc H.
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

Ltac do_evaccum :=
  repeat 
    match goal with
    | [H5: EvSub ?e'' ?e,
           (*H6: cvm_evidence_denote ?annt _ ?e = ?e', *)
           e': EvidenceC,
               H7: not_none_none ?t,
                   H8: annoP ?annt ?t _

        |- _] =>
      
      assert_new_proof_by
        (EvSub e'' e' \/
         (exists (ett : Evidence) p'0 bs,
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett))
        ltac: (eapply evAccum; [apply H8 (*| apply H *) | apply H7 (*| apply H2 | apply H3 | apply H4*) | try reflexivity; try eassumption | apply H5])
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


Lemma sig_is: forall t annt e e' p i,

    annoP annt t i ->
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
    
    destruct a; invc H; dd; eauto; try tauto.
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
    reflexivity.
    jkjke.
    eauto.
    eauto.
    
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

Ltac do_sig_is :=
  repeat 
  match goal with
  | [ H': annoP ?annt ?t _,
          H6: gg_sub ?e',
              He: EvidenceC
     |- _] =>
    
    assert_new_proof_by
      (gg_sub He \/ (term_sub (asp SIG) t))
      ltac:(eapply sig_is; [apply H' | try reflexivity; try eassumption |  apply H6])
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

Lemma hshsig_ev_term_contra: forall t annt p e e' i,

    annoP annt t i ->
    not_hash_sig_term_ev t e ->
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

      eapply gg_recons''; eauto.

  - (* aatt case *)

    dd.
    invc H.
    dd.
    
    do_nhste_att.
     
    eapply IHt.
    econstructor. tauto.
    eassumption.
    jkjke.
        
  - (* alseq case *)

    dd.
    invc H.
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

    do_sig_is.
    
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

Ltac do_hste_contra :=
  repeat 
  match goal with
  | [H': annoP ?annt ?t _,
         H3: not_hash_sig_term_ev ?t ?e,
             He: EvidenceC
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev He)
      ltac:(eapply hshsig_ev_term_contra; [apply H' | apply H3 | try reflexivity; try eassumption])
  end.

Lemma sig_term_ev_lseqr: forall t1 t2 annt e e' p loc,
    annoP annt t1 loc ->
    not_hash_sig_term_ev (lseq t1 t2) e ->
    cvm_evidence_denote annt p e = e' ->  
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

Ltac do_nhste_lseqr :=
  match goal with
  | [H': annoP ?annt ?t1 _,
         H3: not_hash_sig_term_ev (lseq ?t1 ?t2) ?e
        |- _] =>
    edestruct sig_term_ev_lseqr;
      [apply H' | apply H3 |
      try eassumption; try reflexivity | idtac ]
  end.

Lemma uu_preserved': forall t annt p n p0 i args tpl tid
                       e e' l,

    annoP annt t l ->
    not_none_none t ->
    events annt p (et_fun e) (umeas n p0 i args tpl tid) ->
    cvm_evidence_denote annt p e = e' ->

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
    dd.
    invc H.
    dd.
        
    destruct a; ff.
    +
      invEvents.

      unfold cons_uu in *.
      repeat ff.
      left.
      eexists.
      econstructor.
  -
    dd.
    invc H.
    dd.
    do_anno_redo.
       
    inv_events.

    do_not_none.

    do_assume_remote t (evc (encodeEv e) (et_fun e)) n (S l) H9.
    do_annopar_redo.

    eapply IHt;
      try eassumption;
      try reflexivity.  
  -
    dd.
    invc H.
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

      edestruct evAccum.
      apply Heqp0.
      eassumption.
      2 : { eassumption. }
      reflexivity.

      ++
        left. eauto.

      ++
        destruct_conjs.
        
      right.
      repeat (eexists; eauto).
      ++
        destruct_conjs.

        edestruct evAccum.
        apply Heqp0.
        eassumption.
        2: { eassumption. }
        reflexivity.

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
        eassumption.
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

    dd.
    invc H.
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

    dd.
    invc H.
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
  forall t1 t2 annt p n p0 i args tpl tid e e''' e' l,
    annoP annt t1 l ->
    not_none_none t1 ->
    not_none_none t2 ->
    events annt p (et_fun e) (umeas n p0 i args tpl tid) ->
    cvm_evidence_denote annt p e = e''' ->
    cvm_evidence_denote annt p e''' = e' ->
    
    (
      (exists e'', EvSub (uuc (asp_paramsC i args tpl tid) p0 (do_asp (asp_paramsC i args tpl tid) p0 n) e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu (asp_paramsC i args tpl tid) p0 et') ett)
    ).
Proof.
  intros.
  
  assert (
      (exists e'', EvSub (uuc (asp_paramsC i args tpl tid) p0 (do_asp (asp_paramsC i args tpl tid) p0 n) e'') e''') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e''' /\
          EvSubT (uu (asp_paramsC i args tpl tid) p0 et') ett)
    ).
  {
    eapply uu_preserved'.
    apply H.
    eassumption.
    eassumption.
    tauto.
  }
  door;
    do_evaccum.
  +
    clear H6.
    door; eauto.

    right;
      (repeat eexists; eauto).
  +
    door; ff.
    ++
      right;
        repeat (eexists; eauto).

    ++
      assert (EvSubT (uu (asp_paramsC i args tpl tid) p0 H8) H11).
      {
        eapply evsubT_transitive.
        apply hhSubT.
        eassumption.
        eassumption.
      }
      
      right; 
        repeat (eexists; eauto).
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

Lemma nhse_bseql_nosplit: forall t1 t2 annt loc s p e e',
    annoP annt t1 loc ->
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
  | [H': annoP ?annt ?t1 _,
            H4: not_hash_sig_term_ev (bseq ?s ?t1 _) _,
                e': EvidenceC 
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseql_nosplit; [apply H'
                                       | apply H4
                                       | try eassumption; try reflexivity])
  end.

Lemma nhse_bseqr_nosplit: forall t1 t2 annt loc s p e e',
    annoP annt t2 loc ->
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
  | [H': annoP ?annt ?t2 _,
            H4: not_hash_sig_term_ev (bseq ?s _ ?t2) _,
                e': EvidenceC 
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseqr_nosplit; [apply H'
                                       | apply H4
                                       | try eassumption; try reflexivity])
  end.



Lemma nhse_bparl_nosplit: forall t1 t2 annt loc s p e e',
    annoP annt t1 loc ->
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
  | [H': annoP ?annt ?t1 _,
            H4: not_hash_sig_term_ev (bpar ?s ?t1 _) _,
                e': EvidenceC 
     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_ev e')
      ltac:(eapply nhse_bseqr_nosplit; [apply H'
                                       | apply H4
                                       | try eassumption; try reflexivity])
  end.

Lemma nhse_bparr_nosplit: forall t1 t2 annt loc s p e e',
    annoP annt t2 loc ->
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
  | [H': annoP ?annt ?t2 _,
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
  forall t annt p n p0 et' e e' l,
    annoP annt t l ->
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
    dd.
    invc H.
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

    dd.
    invc H.
    dd.
    do_anno_redo.
    invEvents.
    do_not_none.

    unfold not_hash_sig_term_ev in *;
      destruct_conjs.
    do_not_hshsig.

    do_assume_remote t (evc (encodeEv e) (et_fun e)) n (S l) HHH.

    eapply IHt.
    econstructor.
    reflexivity.
    
    eassumption.
    split.
    eassumption.
    split.
    eassumption.
    
    intros.
    unfold not in *; intros.
    do_hsh_subt.
    do_ggsub.
    
    eapply H3.
    repeat eexists.
    eassumption.
    econstructor.
    eauto.
    inversion Heqp2.
    rewrite <- H9.
    eassumption.
    inversion Heqp2.
    rewrite <- H9.
    reflexivity.
        
  - (* alseq case *)

    dd.
    invc H.
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

      try do_nhste_att. try do_nhste_lseql.
      


      try do_nhst_lseqr.
      try do_nhste_lseqr.
      destruct_conjs.

      assert (not_hash_sig_ev (cvm_evidence_denote a0 p (cvm_evidence_denote a p e))).
      {
        eapply hshsig_ev_term_contra.
        apply Heqp0.
        econstructor.
        eassumption.
        split; try eassumption.
        reflexivity.
      }
      (*

      do_hste_contra. *)

      (*
      edestruct sig_term_ev_lseqr.
      apply Heqp1.
      eassumption.
      reflexivity.

      destruct_conjs.

      do_ste.
      clear H10.
       *)
      
      edestruct IHt1; try eassumption; try reflexivity.

      destruct_conjs.
      subst.

      edestruct evAccum.
      apply Heqp0.
      eassumption.
      2: { eassumption. }
      reflexivity.

      +++
        eauto.
      +++
        destruct_conjs.
        dd.
            
        unfold not_hash_sig_ev in H9.
        
        unfold not in *.
        exfalso.
        eapply H9.
        econstructor.
        repeat eexists.
        eassumption.
        eassumption.       
        
    + (* t2 case *)
  
      do_ste.
      destruct_conjs.
      assert (not_hash_sig_ev (cvm_evidence_denote a0 p (cvm_evidence_denote a p e))).
      {
        eapply hshsig_ev_term_contra.
        apply Heqp0.
        econstructor.
        eassumption.
        split; try eassumption.
        reflexivity.
      }
      
      assert (et_fun ((cvm_evidence_denote a p e)) =  (aeval a p (et_fun e))).
      {
        eapply cvm_ev_denote_evtype.
        eassumption.
      }
      
      edestruct IHt2.
      eassumption.
      eassumption.
      2: { rewrite H10.
           eassumption. }
      
      econstructor.
      eassumption.
      split; try eassumption.
      reflexivity.

      eauto.
      
  - (* abseq case *)

    dd.
    invc H.
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

    dd.
    invc H.
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
Defined.

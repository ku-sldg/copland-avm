(* This file is the main verification for the Copland Virtual Machine (CVM) 

  In this file we prove the following properties:
  1. Determinicity of CVM Evidence ("cvm_deterministic_Evidence")
  (two CVMs that start with the same Configuration and Evidence will yield the same result Evidence when run on the same term)

  2. Preservation of Evidence Well Typedness ("cvm_preserves_wf_Evidence")
  (any CVM that receives well-typed Evidence and executes to completion without an error will return well-typed Evidence)

  3. Good Evidence type ("cvm_evidence_type")
  (any CVM that executed to completion without errors will yield Evidence that respects the eval evidence function)

  4. CVM respects Events ("cvm_trace_respects_events")
  (any CVM that executes to completion without an error will have a trace that accurately reflects the Event semantics that have been laid out)

*)
Require Import StructTactics Cvm_Impl Cvm_St ResultT Attestation_Session Cvm_Monad Term_Defs Cvm_Axioms.
Require Import Maps.
Require Import Term.

Require Import List.
Import ListNotations.

Require Import Lia Coq.Program.Tactics.

Lemma invoke_ASP_config_immut : forall par e st sc res st' sc',
  invoke_ASP e par st sc = (res, st', sc') ->
  sc = sc'.
Proof.
  cvm_monad_unfold; ff.
Qed.

Ltac target_find_rewrite H :=
  lazymatch type of H with
  | ?X = ?Y =>
    (* rewrite in goals *)
    lazymatch goal with
    | [ |- context[X] ] => rewrite H
    end;
    (* rewrite in hyps *)
    lazymatch goal with
    | [ H' : context[X] |- _ ] => 
      rewrite H in H'; clear H
    end
  end.

Ltac clean_up_hyp H :=
  (* try injc H;
  try target_find_rewrite H; *)
  try simple congruence 1.

Ltac target_break_match H :=
  lazymatch type of H with
  | context[match ?X with _ => _ end] => 
    let Hbm := fresh "Hbm" in
    destruct X eqn:Hbm; 
    try find_injection;
    try simple congruence 1; try target_break_match Hbm;
    try target_break_match H
  end.

Lemma invoke_APPR_config_immut : forall et r st sc res st' sc' out_et,
  invoke_APPR' r et out_et st sc = (res, st', sc') ->
  sc = sc'.
Proof.
  induction et using EvidenceT_double_ind; simpl in *; cvm_monad_unfold.
  - ff.
  - intros; simpl in *;
    target_break_match H.
  - Reset Ltac Profile.
    Set Ltac Profiling.
    intros; simpl in *;
    target_break_match H.
    Show Ltac Profile.
  - intros; simpl in *;
    target_break_match H.
  - intros; simpl in *;
    target_break_match H.
    all: try (find_apply_hyp_hyp; eauto).
    all: admit.
  - intros; simpl in *;
    target_break_match H;
    result_monad_unfold; ff.
    * eapply IHet; rewrite Hbm8; simpl in *; eauto.
    * eapply IHet; rewrite Hbm8; simpl in *; eauto.
    * eapply IHet; rewrite Hbm8; simpl in *; eauto.
    * eapply IHet; rewrite Hbm11; simpl in *; eauto.
    * eapply IHet; rewrite Hbm11; simpl in *; eauto.
    * eapply IHet.

    
    ** ff.
      find_rewrite.
    clear *.
    *  
    injc Hbm18.
  -  
  
  ff. 
  - intros; simpl in *.
    Set Ltac Profiling.
    target_break_match H.
    target_break_match H.
    breaker.
    Show Ltac Profile "congruence".
  - intros; simpl in *.
    breaker.
  - intros; simpl in *.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    * 
    break_match; subst; try find_injection; try congruence.
    * destruct (map_get a0 (asp_comps (session_context sc))); try congruence.
      repeat find_injection.
    break_match; subst; try find_injection; try congruence.
    breaker.
  - ff. 
  - intros.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    *     break_match; subst; try find_injection; try congruence.
    *     break_match; subst; try find_injection; try congruence.
      break_match; subst; try find_injection; try congruence.
      break_match; subst; try find_injection; try congruence.
      ** 
      break_match; subst; try find_injection; try congruence.
      break_match; subst; try find_injection; try congruence.
      ** 
      break_match; subst; try find_injection; try congruence.
      break_match; subst; try find_injection; try congruence.
      *** breaker.
      *** repeat (      break_match; subst; try find_injection; try congruence).
        **** eapply IHet in H; ff.
        **** eapply IHet in H; ff. 
        **** eapply IHet in H; ff. 
        **** eapply IHet in H; ff. 
      *** repeat (      break_match; subst; try find_injection; try congruence).
      break_match; subst; try find_injection; try congruence.
      break_match; subst; try find_injection; try congruence.
  intros.
  unfold invoke_APPR' in *.
  cvm_monad_unfold.
  destruct et; simpl in *.
  - cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff. 
  - cvm_monad_unfold; ff. 
  cvm_monad_unfold.


  induction et using EvidenceT_double_ind; cvm_monad_unfold.
  - cvm_monad_unfold; ff.
  - cvm_monad_unfold; intros; breaker.
  - cvm_monad_unfold; intros; breaker.
  - cvm_monad_unfold; intros; breaker.
  - cvm_monad_unfold; intros.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    * 
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try find_injection; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
    break_match; subst; try congruence.
  - ff; cvm_monad_unfold; ff. 
  induction et; cvm_monad_unfold; ff; cvm_monad_unfold; ff;
  unfold split_evidence in *; cvm_monad_unfold; ff;
  try find_eapply_lem_hyp IHet1;
  try find_eapply_lem_hyp IHet2; ff.
Qed.

Lemma build_cvm_config_immut : forall t e st sc res st' sc',
  build_cvm e t st sc = (res, st', sc') ->
  sc = sc'.
Proof.
  induction t; simpl in *; cvm_monad_unfold; ff;
  try (find_eapply_lem_hyp IHt1;
    find_eapply_lem_hyp IHt2; ff);
  find_eapply_lem_hyp invoke_APPR_config_immut; ff.
Qed.

Lemma split_evidence_determinisitic : forall e st1 st2 res1 res2 st1' st2' et1 et2 sc sc1' sc2',
  split_evidence e et1 et2 st1 sc = (res1, st1', sc1') ->
  split_evidence e et1 et2 st2 sc = (res2, st2', sc2') ->
  res1 = res2.
Proof.
  intros.
  unfold split_evidence in *.
  cvm_monad_unfold; ff.
Qed.

Lemma peel_n_rawev_result_spec : forall n ls ls1 ls2,
  peel_n_rawev n ls = resultC (ls1, ls2) ->
  ls = ls1 ++ ls2 /\ length ls1 = n.
Proof.
  induction n; ffa using cvm_monad_unfold; ffl.
Qed.

Lemma peel_n_none_spec : forall n ls e,
  peel_n_rawev n ls = errC e ->
  length ls < n.
Proof.
  induction n; ffa using cvm_monad_unfold; ffl.
Qed.

Lemma split_evidence_state_immut : forall e sc sc' res st st' et1 et2,
  split_evidence e et1 et2 st sc = (res, st', sc') ->
  st = st' /\ sc = sc'.
Proof.
  unfold split_evidence in *; cvm_monad_unfold; ff.
Qed.

Lemma check_cvm_policy_preserves_state : forall t p evt st1 st1' r sc sc',
  check_cvm_policy t p evt st1 sc = (r, st1', sc') ->
  st1 = st1' /\ sc = sc'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using cvm_monad_unfold.
Qed.

(* Lemma check_cvm_policy_same_outputs : forall t p evt st1 st1' r1 st2 st2' r2 sc1 sc2 sc1' sc2',
  check_cvm_policy t p evt st1 sc1 = (r1, st1') ->
  check_cvm_policy t p evt st2 sc2 = (r2, st2') ->
  (policy sc1 = policy sc2) ->
  r1 = r2 /\ st1 = st1' /\ st2 = st2'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using cvm_monad_unfold.
Qed. *)

Lemma invoke_APPR_deterministic : forall e sc sc1' sc2' st1 st2 st1' st2' res1 res2 r oe,
  st_evid st1 = st_evid st2 ->
  invoke_APPR' r e oe st1 sc = (res1, st1', sc1') ->
  invoke_APPR' r e oe st2 sc = (res2, st2', sc2') ->
  res1 = res2 /\ st_evid st1' = st_evid st2' /\ 
  sc1' = sc2'.
Proof.
  induction e; simpl in *; intros;
  try (cvm_monad_unfold; intuition; repeat find_injection; eauto; fail).
  - cvm_monad_unfold; ff.
  - cvm_monad_unfold.
    repeat (break_match; repeat find_rewrite; repeat find_injection;
      simpl in *; eauto; try congruence; eauto;
      let n := numgoals in guard n <= 1).
    break_match.
    * ff.
    * ff; rewrite PeanoNat.Nat.eqb_eq in *; ff;
      match goal with
      | H1 : invoke_APPR' _ ?e _ _ _ = _,
        H2 : invoke_APPR' _ ?e _ _ _ = _,
        IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
        eapply IH in H1; try eapply H2; ff
      end.
    * repeat match goal with
      | H1 : context[match ?x with _ => _ end],
        H2 : context[match ?x with _ => _ end] |- _ =>
          destruct x; subst;
          simpl in *;
          repeat find_rewrite; 
          simpl in *;
          repeat find_injection;
          simpl in *;
          repeat find_rewrite; eauto;
          simpl in *;
          eauto; try congruence
    end; ff;
    match goal with
    | H1 : invoke_APPR' _ ?e _ _ _ = _,
      H2 : invoke_APPR' _ ?e _ _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; ff
    end.
  - cvm_monad_unfold; repeat find_rewrite; repeat find_injection; eauto;
    repeat break_match; repeat find_injection; eauto;
    match goal with
    | H1 : split_evidence _ _ _ _ _ = _,
      H2 : split_evidence _ _ _ _ _ = _ |- _ =>
      eapply split_evidence_state_immut in H1 as ?;
      eapply split_evidence_state_immut in H2 as ?;
      eapply split_evidence_determinisitic in H1;
      try eapply H2; clear H2; simpl in *; eauto;
      destruct_conjs; repeat find_injection; eauto; try congruence
    end;
    repeat (match goal with
    | H1 : split_evidence _ _ _ _ _ = _,
      H2 : split_evidence _ _ _ _ _ = _ |- _ =>
      eapply split_evidence_determinisitic in H1;
      try eapply H2; clear H2; simpl in *; eauto;
      destruct_conjs; repeat find_injection; eauto; try congruence
    | H1 : invoke_APPR' _ ?e _ _ _ = _,
      H2 : invoke_APPR' _ ?e _ _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply IH in H1; [ | | eapply H2]; clear H2 IH; simpl in *; eauto;
      destruct_conjs; repeat find_injection; eauto; try congruence
    end);
    repeat find_rewrite; eauto; ff. 
Qed.

Theorem invoke_APPR_deterministic_Evidence : forall et st1 st2 r1 r2 st1' st2' r sc sc1' sc2' eo,
  invoke_APPR' r et eo st1 sc = (r1, st1', sc1') ->
  invoke_APPR' r et eo st2 sc = (r2, st2', sc2') ->
  r1 = r2.
Proof.
  induction et; ff; cvm_monad_unfold; ff;
  repeat match goal with
  | H1 : split_evidence _ _ _ _ _ = _,
    H2 : split_evidence _ _ _ _ _ = _ |- _ =>
    let H' := fresh in
    eapply split_evidence_determinisitic in H1 as H';
    try eapply H2; ff; 
    eapply split_evidence_state_immut in H1;
    eapply split_evidence_state_immut in H2;
    simpl in *; ff
  end;
  repeat match goal with
  | H1 : invoke_APPR' _ ?e _ _ _ = _,
    H2 : invoke_APPR' _ ?e _ _ _ = _,
    IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
    eapply invoke_APPR_config_immut in H1 as ?;
    eapply invoke_APPR_config_immut in H2 as ?;
    eapply IH in H1; [ | eapply H2]; ff;
    clear IH H2
  end.
Qed.

Lemma cvm_deterministic :  forall t e sc sc1' sc2' st1 st2 r1 r2 st1' st2',
  st_evid st1 = st_evid st2 ->
  build_cvm e t st1 sc = (r1, st1', sc1') ->
  build_cvm e t st2 sc = (r2, st2', sc2') ->
  (r1 = r2) /\ (st_evid st1' = st_evid st2').
Proof.
  induction t; simpl in *; cvm_monad_unfold; ff;
  try (repeat match goal with
  | u : unit |- _ => destruct u
  | H1 : build_cvm _ ?t _ _ = _,
    H2 : build_cvm _ ?t _ _ = _,
    IH : context[build_cvm _ ?t _ _ = _ -> _] |- _ =>
      eapply build_cvm_config_immut in H1 as ?;
      eapply build_cvm_config_immut in H2 as ?;
      eapply IH in H1; [ | | eapply H2 ];
      clear IH H2; ff
  end; fail).
  find_eapply_lem_hyp invoke_APPR_deterministic; ff;
  try congruence; ff.
Qed.

Lemma appr_events'_errs_deterministic : forall G p e e' i1 e1,
  appr_events' G p e e' i1 = errC e1 ->
  forall i2, appr_events' G p e e' i2 = errC e1.
Proof.
  induction e; ffa using result_monad_unfold;
  try (find_eapply_lem_hyp IHe; ff; fail);
  try (find_eapply_lem_hyp IHe1; ff);
  try (find_eapply_lem_hyp IHe2; ff).
Qed.

Lemma asp_events_errs_deterministic : forall G t p e i1 i2 e1 e2,
  asp_events G p e t i1 = resultC e1 ->
  asp_events G p e t i2 = errC e2 ->
  False.
Proof.
  destruct t; ff; try (destruct e; simpl in *; congruence);
  find_eapply_lem_hyp appr_events'_errs_deterministic; ff.
  unfold appr_events in *; simpl in *; ff.
Qed.

Lemma events_fix_errs_deterministic : forall G t p e i1 i2 e1 e2,
  events_fix G p e t i1 = resultC e1 ->
  events_fix G p e t i2 = errC e2 ->
  False.
Proof.
  induction t; ffa using result_monad_unfold;
  eapply asp_events_errs_deterministic; eauto.
Qed.

Lemma events_fix_only_one_error : forall G t p e i1 i2 e1 e2,
  events_fix G p e t i1 = errC e1 ->
  events_fix G p e t i2 = errC e2 ->
  e1 = e2.
Proof.
  induction t; ffa using result_monad_unfold;
  try match goal with
  | H1 : events_fix _ _ _ ?t _ = resultC _,
    H2 : events_fix _ _ _ ?t _ = errC _ |- _ =>
    eapply events_fix_errs_deterministic in H1; try eapply H2; 
    try exfalso; eauto
  end.
  destruct a; simpl in *;
  try (destruct e; simpl in *; congruence);
  find_eapply_lem_hyp appr_events'_errs_deterministic; 
  unfold appr_events in *; ff.
Qed.

Theorem cvm_deterministic_Evidence : forall t e sc sc1' sc2' st1 st2 r1 r2 st1' st2',
  build_cvm e t st1 sc = (r1, st1', sc1') ->
  build_cvm e t st2 sc = (r2, st2', sc2') ->
  r1 = r2.
Proof.
  induction t; simpl in *; cvm_monad_unfold.
  - ff; eapply invoke_APPR_deterministic_Evidence; eauto.
  - ff; (* NOTE: Why dont we need the remote axiom here!? *)
    match goal with
    | H1 : events_fix _ _ _ ?t _ = _,
      H2 : events_fix _ _ _ ?t _ = _ |- _ =>
      try (eapply events_fix_only_one_error in H1; try eapply H2; ff; exfalso; eauto; fail);
      try (eapply events_fix_errs_deterministic in H1; try eapply H2; ff; exfalso; eauto; fail)
    end.
  - ff; repeat match goal with
    | u : unit |- _ => destruct u
    | H1 : build_cvm _ ?t _ _ = _,
      H2 : build_cvm _ ?t _ _ = _,
      IH : context[build_cvm _ ?t _ _ = _ -> _] |- _ =>
        eapply build_cvm_config_immut in H1 as ?;
        eapply build_cvm_config_immut in H2 as ?;
        simpl in *; ff;
        eapply IH in H1; [ | eapply H2];
        clear IH H2; ff
    end.
  - ff. 
  all: repeat match goal with
    | u : unit |- _ => destruct u
    | H1 : build_cvm _ ?t _ _ = _,
      H2 : build_cvm _ ?t _ _ = _,
      IH : context[build_cvm _ ?t _ _ = _ -> _] |- _ =>
        eapply build_cvm_config_immut in H1 as ?;
        eapply build_cvm_config_immut in H2 as ?;
        simpl in *; ff;
        eapply IH in H1; [ | eapply H2];
        clear IH H2; ff
    end.
    eapply build_cvm_config_immut in Heqp1 as ?;
    eapply build_cvm_config_immut in Heqp as ?; ff.
  - ff; simpl in *; 
    repeat match goal with
    | u : unit |- _ => destruct u
    | H : parallel_vm_thread _ _ _ _ = ?res |- _ =>
      eapply parallel_vm_thread_axiom in H;
      try reflexivity; break_exists
    | H1 : build_cvm _ ?t _ _ = _,
      H2 : build_cvm _ ?t _ _ = _,
      IH : context[build_cvm _ ?t _ _ = _ -> _] |- _ =>
        eapply build_cvm_config_immut in H1 as ?;
        eapply build_cvm_config_immut in H2 as ?; ff;
        eapply IH in H1; [ | eapply H2 ];
        clear IH H2; try (intuition; congruence)
    end.
    all: 
    try match goal with
    | H1 : events_fix _ _ _ ?t _ = _,
      H2 : events_fix _ _ _ ?t _ = _ |- _ =>
      try (eapply events_fix_only_one_error in H1; try eapply H2; ff; try exfalso; eauto; fail);
      try (eapply events_fix_errs_deterministic in H1; try eapply H2; ff; try exfalso; eauto; fail)
    end.
    * eapply build_cvm_config_immut in Heqp0 as ?; ff;
      eapply build_cvm_config_immut in Heqp as ?; ff.
    * eapply build_cvm_config_immut in Heqp0 as ?; ff;
      eapply build_cvm_config_immut in Heqp as ?; ff.
    * eapply build_cvm_config_immut in Heqp0 as ?; ff;
      eapply build_cvm_config_immut in Heqp as ?; ff.
    * eapply build_cvm_config_immut in Heqp0 as ?; ff;
      eapply build_cvm_config_immut in Heqp as ?; ff.
Qed.

Lemma invoke_APPR'_spans : forall et r e' sc c i st sc' eo,
  invoke_APPR' r et eo st sc = (resultC e', c, sc') ->
  forall G,
  G = session_context sc ->
  appr_events_size G et = resultC i ->
  st_evid c = st_evid st + i.
Proof.
  induction et; ffa using (try cvm_monad_unfold; try result_monad_unfold);
  repeat match goal with
  | H : split_evidence _ _ _ _ _ = _ |- _ =>
    eapply split_evidence_state_immut in H as ?; ff;
    clear H
  | H : Nat.eqb _ _ = _ |- _ => 
    try (erewrite PeanoNat.Nat.eqb_eq in H);
    try (erewrite PeanoNat.Nat.eqb_neq in H);
    ff; try lia
  | H : invoke_APPR' _ ?e _ _ _ = _,
    IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
    eapply invoke_APPR_config_immut in H as ?; ff;
    let numgoals := numgoals in
    eapply IH in H; ff; try lia;
    let numgoals' := numgoals in
    guard numgoals' <= numgoals
  end.
Qed.

Inductive et_same_asps : EvidenceT -> EvidenceT -> Prop :=
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
Local Hint Constructors et_same_asps : et_same_asps_db.

Lemma et_same_asps_impl_same_size : forall G e1 e2,
  et_same_asps e1 e2 ->
  et_size G e1 = et_size G e2.
Proof.
  intros.
  induction H; simpl in *; ffa using result_monad_unfold.
Qed.
Local Hint Resolve et_same_asps_impl_same_size : et_same_asps_db.

Lemma et_same_asps_symm : forall e1 e2,
  et_same_asps e1 e2 -> et_same_asps e2 e1.
Proof.
  intros.
  prep_induction H.
  induction H; ff; eauto with et_same_asps_db.
Qed.
Local Hint Resolve et_same_asps_symm : et_same_asps_db.

(* Lemma et_same_asps_split_helper : forall e1 e2 e3 e4,
  et_same_asps (split_evt e1 e2) (split_evt e3 e4) ->
  (et_same_asps e1 e3 /\ et_same_asps e2 e4) \/
  (et_same_asps e1 e4 /\ et_same_asps e2 e3).
Proof.
  intros.
  prep_induction H.
  induction H; ff; eauto with et_same_asps_db.
Qed.
Local Hint Resolve et_same_asps_split_helper : et_same_asps_db. *)

Lemma et_same_asps_appr_procedure : forall G e1 e1' e2 e2' p1 p2 e1o e2o,
  et_same_asps e1 e2 ->
  et_same_asps e1o e2o ->
  appr_procedure' G p1 e1 e1o = resultC e1' ->
  appr_procedure' G p2 e2 e2o = resultC e2' ->
  et_same_asps e1' e2'.
Proof.
  intros.
  generalizeEverythingElse H.
  induction H; simpl in *; intuition; repeat find_injection; eauto;
  try (econstructor; ff; fail).
  - ff; eauto with et_same_asps_db; 
    result_monad_unfold; ff;
    find_eapply_lem_hyp IHet_same_asps; eauto with et_same_asps_db.
  - ff; result_monad_unfold; ff;
    invc H1; econstructor; eauto with et_same_asps_db.
Qed.
Local Hint Resolve et_same_asps_appr_procedure : et_same_asps_db.

Lemma et_same_asps_eval_same_asps : forall G t p1 p2 e1 e1' e2 e2',
  et_same_asps e1 e2 ->
  eval G p1 e1 t = resultC e1' ->
  eval G p2 e2 t = resultC e2' ->
  et_same_asps e1' e2'.
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a; simpl in *; ff; eauto using et_same_asps.
    eapply et_same_asps_appr_procedure; eauto.
  - result_monad_unfold; ffa.
  - result_monad_unfold; ff.
    repeat match goal with
    | H1 : eval _ ?p1 ?e1 ?t = resultC ?e1',
      H2 : eval _ ?p2 ?e2 ?t = resultC ?e2',
      IH : context[eval _ _ _ ?t = _ -> _] |- _ =>
      eapply IH in H2; try eapply H1; 
      clear H1
    end; try (econstructor; eauto; fail);
    destruct s, s, s0; simpl in *; eauto;
    econstructor.
  - result_monad_unfold; ff;
    repeat match goal with
    | H1 : eval _ ?p1 ?e1 ?t = resultC ?e1',
      H2 : eval _ ?p2 ?e2 ?t = resultC ?e2',
      IH : context[eval _ _ _ ?t = _ -> _] |- _ =>
      eapply IH in H2; try eapply H1; 
      clear H1
    end; try (econstructor; eauto; fail);
    destruct s, s, s0; simpl in *; eauto;
    econstructor.
Qed.
Local Hint Resolve et_same_asps_eval_same_asps : et_same_asps_db.

Lemma appr_procedure_et_size_plc_irrel : forall G e1 e1' e2 e2' p1 p2,
  et_same_asps e1 e2 ->
  appr_procedure G p1 e1 = resultC e1' ->
  appr_procedure G p2 e2 = resultC e2' ->
  et_size G e1' = et_size G e2'.
Proof.
  eauto with et_same_asps_db.
Qed.

Lemma eval_et_size_plc_irrel : forall G t p1 p2 e1 e1' e2 e2',
  et_same_asps e1 e2 ->
  eval G p1 e1 t = resultC e1' ->
  eval G p2 e2 t = resultC e2' ->
  et_size G e1' = et_size G e2'.
Proof.
  eauto with et_same_asps_db.
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

Lemma et_same_asps_refl : forall e,
  et_same_asps e e.
Proof.
  induction e; try econstructor; eauto;
  destruct a; econstructor; eauto.
Qed.

Lemma events_size_eval_res_irrel : forall G t1 t p1 p2 et e1 e2 n1 n2,
  eval G p1 et t1 = resultC e1 ->
  eval G p2 et t1 = resultC e2 ->
  events_size G p1 e1 t = resultC n1 ->
  events_size G p2 e2 t = resultC n2 ->
  n1 = n2.
Proof.
  intros.
  assert (et_same_asps e1 e2) by (
    assert (et_same_asps et et) by (eapply et_same_asps_refl);
    eauto with et_same_asps_db
  );
  clear H H0 et.
  generalizeEverythingElse t.
  induction t; simpl in *; intuition; ffa using result_monad_unfold;
  eauto with et_same_asps_db.
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
  end; try lia.
  - eapply events_size_eval_res_irrel in Heqr4;
    try eapply Heqr1; eauto.
Qed.

Definition well_formed_context (G : GlobalContext) : Prop :=
  map_get sig_aspid (asp_types G) = Some (ev_arrow EXTEND InAll (OutN 1)) /\
  map_get hsh_aspid (asp_types G) = Some (ev_arrow REPLACE InAll (OutN 1)) /\
  map_get enc_aspid (asp_types G) = Some (ev_arrow WRAP InAll (OutN 1)) /\
  map_get check_nonce_aspid (asp_types G) = Some (ev_arrow EXTEND InAll (OutN 1)).

Lemma eqb_ASP_PARAMS_eq : forall a1 a2,
  eqb_ASP_PARAMS a1 a2 = true <-> a1 = a2.
Proof.
  induction a1; destruct a2; ff;
  repeat rewrite Bool.andb_true_iff in *; ff;
  repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
  repeat rewrite String.eqb_eq in *; ff;
  repeat rewrite EqClass.general_list_eqb_eq in *; ff.
Qed.

Lemma eqb_EvidenceT_eq : forall e1 e2,
  eqb_EvidenceT e1 e2 = true <-> e1 = e2.
Proof.
  induction e1; destruct e2; ff;
  repeat rewrite Bool.andb_true_iff in *; ff;
  repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
  repeat rewrite String.eqb_eq in *; ff;
  try erewrite IHe1 in *; ff;
  repeat rewrite eqb_ASP_PARAMS_eq in *; ff;
  repeat rewrite IHe1_1 in *; ff;
  repeat rewrite IHe1_2 in *; ff.
Qed.

Lemma invoke_ASP_evidence : forall e par st sc e' st' sc',
  invoke_ASP e par st sc = (resultC e', st', sc') ->
  get_et e' = asp_evt (session_plc sc) par (get_et e).
Proof.
  cvm_monad_unfold; ff.
Qed.

Lemma split_evidence_res_spec : forall e st st' et1 et2 e1 e2 sc sc',
  split_evidence e et1 et2 st sc = (resultC (e1, e2), st', sc') ->
  exists r,
  e = evc r (split_evt et1 et2) /\
  (exists r1 r2, (e1,e2) = (evc r1 et1, evc r2 et2) /\ r = r1 ++ r2).
Proof.
  intros.
  destruct st; simpl in *; ff.
  unfold split_evidence in *;
  cvm_monad_unfold; ff.
  repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
  repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
  repeat rewrite app_nil_r in *;
  repeat rewrite eqb_EvidenceT_eq in *; ff;
  destruct e; ff; eexists; intuition; eauto.
Qed.

Theorem invoke_APPR'_evidence : forall et st r sc sc' st' e' e eo,
  invoke_APPR' r et eo st sc = (resultC e', st', sc') ->
  appr_procedure' (session_context sc) (session_plc sc) et eo = resultC e ->
  get_et e' = e.
Proof.
  induction et; intuition.
  - simpl in *; cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; result_monad_unfold; ff;
    cvm_monad_unfold; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff.
    * eapply IHet in Heqp2; ff.
    * eapply IHet in Heqp2; ff. 
    * eapply IHet in Heqp2; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; result_monad_unfold; ff;
    find_copy_eapply_lem_hyp split_evidence_res_spec; ff;
    find_eapply_lem_hyp split_evidence_state_immut; ff;
    repeat find_rewrite_lem eqb_EvidenceT_eq; ff;
    repeat match goal with
    | H : invoke_APPR' _ ?e _ _ _ = _,
      H1 : appr_procedure' _ _ ?e _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply invoke_APPR_config_immut in H as ?;
      eapply IH in H; [ | eapply H1 ]; ff
    end; ff. 
Qed.

Theorem cvm_evidence_type : forall t e e' st st' sc sc' et',
  build_cvm e t st sc = (resultC e', st', sc') ->
  eval (session_context sc) (session_plc sc) (get_et e) t = resultC et' ->
  get_et e' = et'.
Proof.
  induction t; simpl in *; intuition.
  - cvm_monad_unfold; destruct a; simpl in *;
    repeat find_injection; simpl in *; try congruence;
    unfold well_formed_context in *; simpl in *; destruct_conjs;
    ff; repeat find_rewrite; simpl in *; eauto.
    eapply invoke_APPR'_evidence in H; ff.
  - cvm_monad_unfold; ffa;
    find_eapply_lem_hyp do_remote_res_axiom; ff;
    find_eapply_lem_hyp IHt; ff.
    Unshelve. all: eauto; try eapply (st_config st).
  - ffa using (try cvm_monad_unfold; try result_monad_unfold);
    match goal with
    | H1 : build_cvm _ ?t1 _ _ = _,
      H2 : build_cvm _ ?t2 _ _ = _,
      IH1 : context[build_cvm _ ?t1 _ _ = _ -> _],
      IH2 : context[build_cvm _ ?t2 _ _ = _ -> _] |- _ =>
      eapply IH1 in H1 as ?; ff;
      eapply build_cvm_config_immut in H1; 
      eapply IH2 in H2; ff
    end.
  - ffa using (try cvm_monad_unfold; try result_monad_unfold);
    destruct s, s, s0; simpl in *;
    eapply IHt1 in Heqp as ?; ff;
    eapply build_cvm_config_immut in Heqp; simpl in *; ff;
    eapply IHt2 in Heqp0 as ?; simpl in *;
    eapply build_cvm_config_immut in Heqp0; simpl in *; try (find_higher_order_rewrite; ff; fail);
    ff; find_higher_order_rewrite; eauto.
  - ffa using (try cvm_monad_unfold; try result_monad_unfold);
    destruct s, s, s0; simpl in *;
    eapply IHt1 in Heqp as ?; ff;
    eapply build_cvm_config_immut in Heqp; simpl in *; ff;
    find_eapply_lem_hyp parallel_vm_thread_axiom; eauto;
    break_exists; destruct_conjs; find_eapply_lem_hyp IHt2; ff;
    repeat find_rewrite; try unfold mt_evc; simpl in *; ff.
Qed.

(** * Lemma:  CVM increases event IDs according to event_id_span' denotation. *)
Lemma cvm_spans: forall t st e st' sc i sc' e',
  well_formed_context (session_context sc) ->
  build_cvm e t st sc = (resultC e', st', sc') ->
  events_size (session_context sc) (session_plc sc) (get_et e) t = resultC i ->
  st_evid st' = st_evid st + i.
Proof.
  induction t; simpl in *; intuition.
  - cvm_monad_unfold; ff.
    find_eapply_lem_hyp invoke_APPR'_spans; ff. 
  - cvm_monad_unfold; ff; result_monad_unfold; 
    ff; find_eapply_lem_hyp events_size_plc_irrel;
    try eapply Heqr; ff; lia.
  - cvm_monad_unfold; result_monad_unfold; ff.
    repeat match goal with
    | H : build_cvm _ ?t _ _ = _,
      H1 : events_size _ _ _ ?t = _,
      IH : context[build_cvm _ ?t _ _ = _ -> _] |- _ => 
      eapply build_cvm_config_immut in H as ?;
      eapply IH in H as ?; try eapply H1;
      simpl in *; ff; [
        try (eapply cvm_evidence_type in H as ?; ff; [])
      ]; clear H IH
    end; lia.
  - cvm_monad_unfold; result_monad_unfold; ff.
    eapply build_cvm_config_immut in Heqp as ?; ff;
    eapply IHt1 in Heqp; [ | eauto | destruct s, s, s0; ff ]; ff.
    eapply build_cvm_config_immut in Heqp0 as ?; ff.
    eapply IHt2 in Heqp0; [ | eauto | destruct s, s, s0; ff ]; ff.
    lia.
  - ffa using (try result_monad_unfold; try cvm_monad_unfold).
    eapply build_cvm_config_immut in Heqp as ?;
    repeat find_rewrite;
    eapply IHt1 in Heqp; try eapply Heqr;
    simpl in *; eauto; ff;
    destruct s, s, s0; simpl in *; ff; try lia;
    repeat find_rewrite; repeat find_injection; try lia.
Qed.

Lemma wf_Evidence_split_l : forall G e s,
  wf_Evidence G e ->
  wf_Evidence G (splitEv_l s e).
Proof.
  intros; invc H;
  unfold splitEv_l; ff;
  econstructor; simpl in *; auto.
  Unshelve. eapply 0.
Qed.
Local Hint Resolve wf_Evidence_split_l : wf_Evidence.

Lemma wf_Evidence_split_r : forall G e s,
  wf_Evidence G e ->
  wf_Evidence G (splitEv_r s e).
Proof.
  intros; invc H;
  unfold splitEv_r; ff;
  econstructor; simpl in *; auto.
  Unshelve. eapply 0.
Qed.
Local Hint Resolve wf_Evidence_split_r : wf_Evidence.

Lemma wf_Evidence_split : forall G r1 r2 et1 et2,
  wf_Evidence G (evc r1 et1) ->
  wf_Evidence G (evc r2 et2) ->
  wf_Evidence G (evc (r1 ++ r2) (split_evt et1 et2)).
Proof.
  intros; invc H; invc H0; econstructor; ff;
  rewrite length_app; ff.
Qed.
Local Hint Resolve wf_Evidence_split : wf_Evidence.

Lemma wf_Evidence_impl_et_size_res : forall G e,
  wf_Evidence G e ->
  exists n, et_size G (get_et e) = resultC n.
Proof.
  destruct e; 
  induction e; simpl in *; intros;
  invc H; simpl in *; eauto.
Qed.

Lemma wf_Evidence_mt_evc : forall G,
  wf_Evidence G mt_evc.
Proof.
  unfold mt_evc; econstructor; simpl in *; eauto.
  Unshelve. eapply 0.
Qed.

Lemma wf_Evidence_split_evidence : forall e et1 et2 st st' G r1 r2 sc sc',
  wf_Evidence G e ->
  session_context sc = G ->
  split_evidence e et1 et2 st sc = (resultC (r1, r2), st', sc') ->
  wf_Evidence G r1 /\ wf_Evidence G r2.
Proof.
  intros; unfold split_evidence in *;
  cvm_monad_unfold; ff;
  intuition; invc H; simpl in *;
  result_monad_unfold; ff;
  econstructor; simpl in *; eauto;
  repeat find_eapply_lem_hyp peel_n_rawev_result_spec;
  intuition; ff.
Qed.

Fixpoint meta_machinery_pad_n (n : nat) (e : RawEv) : RawEv :=
  match n with
  | 0 => e
  | S n' => passed_bs :: meta_machinery_pad_n n' e
  end.

Lemma meta_machinery_pad_n_size : forall n e,
  length (meta_machinery_pad_n n e) = n + length e.
Proof.
  induction n; ff.
Qed.

Lemma wf_Evidence_exists : forall G e n,
  et_size G e = resultC n ->
  exists r, wf_Evidence G (evc r e).
Proof.
  induction e; ff.
  - eexists; eapply wf_Evidence_mt_evc. 
  - exists [passed_bs]; econstructor; eauto.
  - result_monad_unfold; ff.
    pose proof (IHe _ eq_refl); ff.
    invc H.
    destruct e0, e1, f.
    * exists (meta_machinery_pad_n n nil); econstructor; 
      simpl in *; ff;
      rewrite meta_machinery_pad_n_size; ff.
    * exists (meta_machinery_pad_n n nil); econstructor; 
      simpl in *; ff;
      rewrite meta_machinery_pad_n_size; ff.
    * exists (meta_machinery_pad_n n x); econstructor; 
      simpl in *; ff;
      rewrite meta_machinery_pad_n_size; ff.
  - result_monad_unfold; ff.
    pose proof (IHe1 _ eq_refl);
    pose proof (IHe2 _ eq_refl); ff.
    econstructor; eapply wf_Evidence_split; ff.
Qed.

Lemma wf_Evidence_asp_unfold : forall G r p ps e,
  wf_Evidence G (evc r (asp_evt p ps e)) ->
  exists r', wf_Evidence G (evc r' e).
Proof.
  intros.
  prep_induction H.
  induction H; ff; result_monad_unfold; ff.
  eapply wf_Evidence_exists; ff.
Qed.

Lemma wf_Evidence_asp_unfold_more : forall G r p e n a a1 p0 t,
  wf_Evidence G (evc r (asp_evt p (asp_paramsC a a1 p0 t) e)) ->
  et_size G e = resultC n ->
  forall sig n',
  map_get a (asp_types G) = Some (ev_arrow EXTEND sig (OutN n')) ->
  et_size G (asp_evt p (asp_paramsC a a1 p0 t) e) = resultC (n' + n).
Proof.
  intros.
  prep_induction H.
  induction H; ff; result_monad_unfold; ff.
Qed.

Lemma wf_Evidence_split_unfold : forall G r e1 e2,
  wf_Evidence G (evc r (split_evt e1 e2)) ->
  (exists r1, wf_Evidence G (evc r1 e1)) /\ (exists r2, wf_Evidence G (evc r2 e2)).
Proof.
  intros.
  prep_induction H;
  induction H; ff; result_monad_unfold; ff;
  break_and_goal; eapply wf_Evidence_exists; ff.
Qed.

Lemma wf_Evidence_asp_unpack : forall G r p e a0 a1 p0 t,
  wf_Evidence G (evc r (asp_evt p (asp_paramsC a0 a1 p0 t) e)) ->
  forall in_sig n n',
  map_get a0 (asp_types G) = Some (ev_arrow EXTEND in_sig (OutN n)) ->
  et_size G e = resultC n' ->
  length r = n + n'.
Proof.
  intros.
  prep_induction H; ff; invc H; ff.
Qed.

Lemma wf_Evidence_invoke_ASP : forall ps st e e' st' sc sc',
  wf_Evidence (session_context sc) e ->
  invoke_ASP e ps st sc = (resultC e', st', sc') ->
  wf_Evidence (session_context sc) e'.
Proof.
  destruct st; simpl in *; ff.
  prep_induction H.
  induction H; cvm_monad_unfold; ff;
  econstructor; ff;
  rewrite PeanoNat.Nat.eqb_eq in *; ff;
  rewrite length_app in *; ff.
Qed.


(* Lemma et_size_invoke_APPR : forall e st e' st' n,
  et_size (session_context (st_config st)) (get_et e) = resultC n ->
  et_size (session_context (st_config st)) (get_et (st_ev st)) = resultC n ->
  (* wf_Evidence (session_context (st_config st)) e ->
  wf_Evidence (session_context (st_config st)) (st_ev st) ->  *)
  invoke_APPR (get_et e) st = (resultC e', st') ->
  exists n', et_size (session_context (st_config st)) (get_et e') = resultC n'.
  (* wf_Evidence (session_context (st_config st)) e'. *)
Proof.
  destruct e; simpl in *.
  generalizeEverythingElse e.
  induction e; intuition.
  - ff; cvm_monad_unfold; ff.
  - ff; cvm_monad_unfold; ff. 
  (* rewrite PeanoNat.Nat.eqb_eq in *; ff;
    econstructor; ff; result_monad_unfold; repeat rewrite length_app; ff;
    invc H1; ff;
    repeat find_reverse_rewrite; ff. *)
  - simpl in *; result_monad_unfold.
    unfold err_bind in *; ff.
    * cvm_monad_unfold; ff.
    * eapply sc_immut_invoke_ASP in Heqp1 as ?;
      eapply sc_immut_invoke_APPR in H2 as ?;
      eapply H in H2; ff;
      rewrite PeanoNat.Nat.eqb_eq in *; ff.
    * repeat unfold hoist_result, err_ret in *; ff.
        (* add_trace, err_put, put_trace in *; ff. *)
      eapply sc_immut_invoke_APPR in Heqp2 as ?;
      eapply sc_immut_invoke_ASP in Heqp0 as ?; ff.
      eapply H in Heqp2; simpl in *.
      ** eapply et_size_invoke_ASP in Heqp0; ff.
        cvm_monad_unfold; ff.
      ** repeat find_rewrite; ff.
      ** repeat find_rewrite; ff. 
  - simpl in *; result_monad_unfold; ff.
    unfold err_bind in *; ff.
    eapply split_evidence_state_immut in Heqp as ?; ff.
    eapply split_evidence_res_spec in Heqp; ff.
    eapply sc_immut_invoke_APPR in Heqp0 as ?;
    eapply sc_immut_invoke_APPR in Heqp1 as ?.
    simpl in *; ff;
    repeat find_reverse_rewrite; simpl in *;
    result_monad_unfold; ff.
    eapply H in Heqp0; simpl in *.
    ** eapply H0 in Heqp1; simpl in *; eauto; ff.
      cvm_monad_unfold; ff.
    ** eauto.
    ** eauto.
Qed. *)

Lemma wf_Evidence_invoke_APPR : forall et r eo st e' st' sc sc',
  wf_Evidence (session_context sc) (evc r et) ->
  wf_Evidence (session_context sc) (evc r eo) ->
  invoke_APPR' r et eo st sc = (resultC e', st', sc') ->
  wf_Evidence (session_context sc) e'.
Proof.
  induction et; intuition.
  - ff; cvm_monad_unfold; ff; eapply wf_Evidence_mt_evc.
  - ff; cvm_monad_unfold; ff;
    rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat match goal with
    | H : wf_Evidence _ _ |- _ => invc H; ff
    end; econstructor; ff; rewrite length_app; ff.
  - simpl in *; result_monad_unfold; cvm_monad_unfold; ff;
    rewrite PeanoNat.Nat.eqb_eq in *; ff.
    all: try (repeat match goal with
      | H : wf_Evidence _ _ |- _ => invc H; ff
      end; econstructor; ff; result_monad_unfold; repeat rewrite length_app in *; ff; fail).
    all: try (result_monad_unfold; ff; eapply IHet in H1; eauto; econstructor; 
      repeat rewrite length_app in *; ff;
      repeat match goal with
      | H : wf_Evidence _ _ |- _ => invc H; ff
      end; fail).
    * find_eapply_lem_hyp peel_n_rawev_result_spec; ff.
      eapply IHet in Heqp2.
      ** econstructor; repeat rewrite length_app in *; ff;
        result_monad_unfold; ff;
        repeat match goal with
        | H : wf_Evidence _ _ |- _ => invc H; 
          result_monad_unfold; ff
        end.
      ** econstructor; repeat match goal with
        | H : wf_Evidence _ _ |- _ => invc H; 
          result_monad_unfold; ff
      end; result_monad_unfold; ff; repeat rewrite length_app in *;
      f_equal; lia.
      ** econstructor; repeat match goal with
        | H : wf_Evidence _ _ |- _ => invc H; 
          result_monad_unfold; ff
      end; result_monad_unfold; ff; repeat rewrite length_app in *;
      f_equal; lia.
    * find_eapply_lem_hyp peel_n_rawev_result_spec; ff.
      eapply IHet in Heqp2.
      ** econstructor; repeat rewrite length_app in *; ff;
        result_monad_unfold; ff;
        repeat match goal with
        | H : wf_Evidence _ _ |- _ => invc H; 
          result_monad_unfold; ff
        end.
      ** econstructor; repeat match goal with
        | H : wf_Evidence _ _ |- _ => invc H; 
          result_monad_unfold; ff
      end; result_monad_unfold; ff; repeat rewrite length_app in *;
      f_equal; lia.
      ** econstructor; repeat match goal with
        | H : wf_Evidence _ _ |- _ => invc H; 
          result_monad_unfold; ff
      end; result_monad_unfold; ff; repeat rewrite length_app in *;
      f_equal; lia.
    * find_eapply_lem_hyp peel_n_rawev_result_spec; ff.
      eapply IHet in Heqp2.
      ** econstructor; repeat rewrite length_app in *; ff;
        result_monad_unfold; ff;
        repeat match goal with
        | H : wf_Evidence _ _ |- _ => invc H; 
          result_monad_unfold; ff
        end.
        result_monad_unfold; ff; repeat rewrite length_app in *; ff.
      ** econstructor; repeat match goal with
        | H : wf_Evidence _ _ |- _ => invc H; 
          result_monad_unfold; ff
      end; result_monad_unfold; ff; repeat rewrite length_app in *;
      f_equal; lia.
      ** econstructor; repeat match goal with
        | H : wf_Evidence _ _ |- _ => invc H; 
          result_monad_unfold; ff
      end; result_monad_unfold; ff; repeat rewrite length_app in *;
      f_equal; lia.
  - simpl in *; ff; cvm_monad_unfold; ff.
    unfold split_evidence in *; cvm_monad_unfold; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    repeat rewrite eqb_EvidenceT_eq in *; ff;
    repeat rewrite app_nil_r in *; ff.
    eapply invoke_APPR_config_immut in Heqp0 as ?; ff.
    eapply invoke_APPR_config_immut in Heqp1 as ?; ff.
    eapply IHet1 in Heqp0.
    * eapply IHet2 in Heqp1.
      ** econstructor; repeat rewrite length_app in *; ff;
      result_monad_unfold; ff;
      repeat match goal with
      | H : wf_Evidence _ _ |- _ => invc H; ff
      end; result_monad_unfold; ff.
      ** econstructor; invc H; ff; result_monad_unfold; ff.
      ** econstructor; invc H; ff; result_monad_unfold; ff.
    * econstructor; invc H; ff; result_monad_unfold; ff.
    * econstructor; invc H; ff; result_monad_unfold; ff.
Qed.

(** * Theorem:  CVM execution preserves well-formedness of Evidence bundles 
      (EvidenceT Type of sufficient length for raw EvidenceT). *)
Theorem cvm_preserves_wf_Evidence : forall t st st' e e' sc sc',
  wf_Evidence (session_context sc) e ->
  build_cvm e t st sc = (resultC e', st', sc') ->
  wf_Evidence (session_context sc) e'.
Proof.
  induction t; simpl in *; intuition;
  cvm_monad_unfold; try (ffa; fail).
  - ff;
    try match goal with
    | |- wf_Evidence _ mt_evc => eapply wf_Evidence_mt_evc
    | H : Nat.eqb _ _ = true |- _ =>
      rewrite PeanoNat.Nat.eqb_eq in H
    end;
    try (econstructor; simpl in *; ff; fail);
    try (invc H;
      econstructor; ff;
      repeat find_rewrite;
      repeat find_injection;
      result_monad_unfold; ff;
      repeat rewrite length_app;
      f_equal; lia);
    eapply wf_Evidence_invoke_APPR; eauto; destruct e; ff.
  - ff;
    find_eapply_lem_hyp do_remote_res_axiom; eauto;
    break_exists; destruct_conjs;
    eapply IHt in H0; eauto;
    destruct x, st_ev; simpl in *; ff.
    Unshelve. eapply 0.
  - ff;
    repeat match goal with
    | H1 : build_cvm _ ?t1 _ _ = _,
      IH : context[build_cvm _ ?t1 _ _ = _ -> _]
      |- _ =>
      eapply build_cvm_config_immut in H1 as ?;
      eapply IH in H1; simpl in *;
      try reflexivity; ff; check_num_goals_le 1
    end.
  - ffa; simpl in *.
    eapply build_cvm_config_immut in Heqp as ?;
    eapply build_cvm_config_immut in Heqp0 as ?; ff;
    eapply IHt1 in Heqp; ff; eauto with wf_Evidence.
  - ffa; simpl in *.
    find_eapply_lem_hyp parallel_vm_thread_axiom; ff.
    eapply build_cvm_config_immut in Heqp as ?;
    eapply build_cvm_config_immut in H0 as ?; ff;
    eapply IHt1 in Heqp; ff; eauto with wf_Evidence.
Qed.

Theorem invoke_APPR_respects_events : forall et r eo st sc st' sc' e' i m evs,
  well_formed_context (session_context sc) ->
  st_evid st = i ->
  st_trace st = m ->
  invoke_APPR' r et eo st sc = (resultC e', st', sc') ->
  appr_events' (session_context sc) (session_plc sc) et eo i = resultC evs ->
  st_trace st' = m ++ evs.
Proof.
  induction et; simpl in *; intros; cvm_monad_unfold.
  - ff; rewrite app_nil_r; ff.
  - ff. 
  - ff; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff.
    * eapply IHet in H2; try eapply Heqr3; simpl in *; eauto;
      ff; repeat rewrite <- app_assoc; ff.
    * eapply IHet in H2; try eapply Heqr3; simpl in *; eauto;
      ff; repeat rewrite <- app_assoc; ff.
    * eapply IHet in H2; try eapply Heqr3; simpl in *; eauto;
      ff; repeat rewrite <- app_assoc; ff.
    * repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff.
      eapply invoke_APPR'_spans in Heqp2 as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff.
      eapply invoke_APPR_config_immut in Heqp2 as ?; ff.
      eapply IHet in Heqp2 as ?; try eapply Heqr1; simpl in *; eauto;
      assert (st_evid st + 1 + 1 = st_evid st + 2) by lia; ff.
      repeat rewrite <- app_assoc; ff.
    * repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff.
      eapply invoke_APPR'_spans in Heqp2 as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff.
      eapply invoke_APPR_config_immut in Heqp2 as ?; ff.
      eapply IHet in Heqp2 as ?; try eapply Heqr1; simpl in *; eauto;
      assert (st_evid st + 1 + 1 = st_evid st + 2) by lia; ff.
      repeat rewrite <- app_assoc; ff.
    * repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff.
      eapply invoke_APPR'_spans in Heqp2 as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff.
      eapply invoke_APPR_config_immut in Heqp2 as ?; ff.
      eapply IHet in Heqp2 as ?; try eapply Heqr1; simpl in *; eauto;
      assert (st_evid st + 1 + 1 = st_evid st + 2) by lia; ff.
      repeat rewrite <- app_assoc; ff.
  - ff; result_monad_unfold; ff. 
    unfold split_evidence in *; cvm_monad_unfold; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    repeat rewrite eqb_EvidenceT_eq in *; ff.
    eapply invoke_APPR_config_immut in Heqp0 as ?; ff.
    eapply IHet1 in Heqp0 as ?; ff.
    eapply invoke_APPR'_spans in Heqp0; try reflexivity; ff;
    try (eapply appr_events'_size_works; eauto; ff); ff.
    eapply invoke_APPR_config_immut in Heqp1 as ?; ff.
    eapply IHet2 in Heqp1 as ?; ff.
    eapply invoke_APPR'_spans in Heqp1; try reflexivity; ff;
    try (eapply appr_events'_size_works; eauto; ff); ff.
    repeat rewrite <- app_assoc; ff.
Qed.

(** * Main Theorem: CVM traces are respected the reference "events"
      semantics. *)
Theorem cvm_trace_respects_events : forall t st m st' i p e evs sc sc' e',
  well_formed_context (session_context sc) ->
  events (session_context sc) (cop_phrase p (get_et e) t) i evs ->
  st_trace st = m ->
  st_evid st = i ->
  session_plc sc = p ->
  build_cvm e t st sc = (resultC e', st', sc') ->
  st_trace st' = m ++ evs.
Proof.
  induction t; simpl in *; intros.
  - invc H0; simpl in *; cvm_monad_unfold; ff;
    simpl in *;
    repeat match goal with
    | st : cvm_st |- _ => destruct st; simpl in *; ff
    | e : Evidence |- _ => destruct e; simpl in *; ff
    end;
    try (match goal with
    | e : EvidenceT |- _ => 
      induction e; simpl in *; 
      repeat find_injection; eauto; ffa; fail
    end).
    eapply invoke_APPR_respects_events in H4; ff.
  - ff; invc H0; cvm_monad_unfold; ff;
    find_eapply_lem_hyp events_events_fix_eq;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff;
    assert (length rem_evs = n) by (
      find_eapply_lem_hyp events_fix_range;
      eapply events_size_plc_irrel; eauto);
    ff;
    repeat rewrite <- app_assoc; eauto.
    eapply do_remote_res_axiom in Heqr1; eauto;
    break_exists; destruct_conjs;
    eapply cvm_evidence_type in H0; ff;
    repeat find_rewrite; eauto.
    Unshelve. all: try eapply (st_config st); try eapply 0; try eapply sc'.

  - ff; cvm_monad_unfold; ff.
    match goal with
    | H : events _ _ _ _ |- _ => invc H; ff
    end; cvm_monad_unfold; ff;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff;
    eapply IHt1 in Heqp as ?; eauto;
    eapply build_cvm_config_immut in Heqp as ?; subst.
    eapply cvm_evidence_type in Heqp as ?; ff; repeat find_reverse_rewrite; ff.
    eapply IHt2 in H4; try eapply H11; simpl in *; eauto; ff.
    * repeat rewrite app_assoc; eauto.
    * eapply cvm_spans; ff;
      repeat find_rewrite; eauto;
      eapply events_range; eauto.
  - ffa; 
    match goal with
    | H : events _ _ _ _ |- _ => invc H; ff
    end; cvm_monad_unfold; ff;
    cvm_monad_unfold; ffa;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff.
    eapply IHt1 in Heqp as ?; eauto;
    try (destruct s, s, s0; ff; fail);
    eapply build_cvm_config_immut in Heqp as ?;
    eapply cvm_spans in Heqp as ?; eauto; ff;
    try (repeat find_rewrite; simpl in *;
      destruct s, s, s0; simpl in *; 
      eapply events_range; eauto; ff; fail);
    repeat find_rewrite;
    eapply IHt2 in Heqp0 as ?; try eapply H11;
    eapply build_cvm_config_immut in Heqp0 as ?;
    simpl in *; eauto; ff;
    try (destruct s, s, s0; ff; fail).
    eapply cvm_spans in Heqp0; simpl in *; eauto;
    repeat find_rewrite;
    repeat rewrite <- app_assoc; eauto;
    try reflexivity;
    destruct s, s, s0; ff;
    eapply events_range; eauto; ff.
  - ffa; invc H0; ffa;
    cvm_monad_unfold; ffa;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff.
    eapply IHt1 in Heqp as ?; try (destruct s, s, s0; ff; fail); eauto; ff; try lia.
    eapply build_cvm_config_immut in Heqp as ?;
    eapply cvm_spans in Heqp as ?; eauto; ff;
    try (repeat find_rewrite; simpl in *;
      destruct s, s, s0; simpl in *; 
      eapply events_range; eauto; ff; fail);
    repeat find_rewrite; try lia.
    repeat rewrite <- app_assoc; simpl in *; ff.
    repeat find_rewrite; repeat find_injection; eauto.
    assert (st_evid st + 2 + length evs1 = st_evid st + 1 + 1 + length evs1) by lia.
    ff.
    repeat find_rewrite_lem events_events_fix_eq; ff.
    assert (n = length evs2) by (
      repeat find_eapply_lem_hyp events_fix_range; eauto; ff;
      destruct s, s, s0; simpl in *; ff).
    ff.
    destruct s, s, s0; simpl in *; ff.
Qed.

Corollary cvm_trace_respects_events_default : forall G,
  well_formed_context G ->
  forall t st st' i p e evs sc sc' e',
  st_trace st = nil ->
  st_evid st = i ->
  session_plc sc = p ->
  session_context sc = G ->
  
  events G (cop_phrase p (get_et e) t) i evs ->

  build_cvm e t st sc = (resultC e', st', sc') ->
  st_trace st' = evs.
Proof.
  intros.
  eapply cvm_trace_respects_events in H5; eauto;
  simpl in *; ff.
Qed.

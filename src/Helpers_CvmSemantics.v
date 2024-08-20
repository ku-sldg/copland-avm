(*
Helper lemmas for proofs about the CVM semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Cvm_Monad Cvm_Impl Term_Defs Auto Attestation_Session StructTactics AutoApp.
Require Import Coq.Program.Tactics.

Import ListNotations.

Lemma sc_immut_peel_n_rawev : forall n r st res st',
  peel_n_rawev n r st = (res, st') ->
  st_config st = st_config st'.
Proof.
  induction n; simpl in *; intuition; cvm_monad_unfold;
  ff.
Qed.

Lemma peel_n_rawev_deterministic : forall n r st1 st2 res1 res2 st1' st2',
  st_config st1 = st_config st2 ->
  peel_n_rawev n r st1 = (res1, st1') ->
  peel_n_rawev n r st2 = (res2, st2') ->
  res1 = res2 /\ st1 = st1' /\ st2 = st2'.
Proof.
  induction n; simpl in *; intuition;
  cvm_monad_unfold; ffa;
  eapply IHn in Heqp0; try eapply Heqp; intuition; eauto; 
  try congruence.
Qed.

Lemma sc_immut_split_evidence : forall r et1 et2 st res st',
  split_evidence r et1 et2 st = (res, st') ->
  st_config st = st_config st'.
Proof.
  intros.
  unfold split_evidence in *.
  destruct st; ff; cvm_monad_unfold; ff;
  repeat (find_eapply_lem_hyp sc_immut_peel_n_rawev;
  simpl in *; ff).
Qed.

Lemma split_evidence_determinisitic : forall r et1 et2 st1 st2 res1 res2 st1' st2',
  st_config st1 = st_config st2 ->
  split_evidence r et1 et2 st1 = (res1, st1') ->
  split_evidence r et1 et2 st2 = (res2, st2') ->
  res1 = res2 /\ st1 = st1' /\ st2 = st2'.
Proof.
  intros.
  unfold split_evidence in *; 
  destruct st1, st2; simpl in *;
  ff; cvm_monad_unfold; ff;
  repeat match goal with
  | H : peel_n_rawev ?n ?r _ = (_, _),
    H1 : peel_n_rawev ?n ?r _ = (_, _) |- _ =>
      eapply peel_n_rawev_deterministic in H;
      [ | | eapply H1 ]; [ | simpl in *; ff ];
      intuition; clear H1;
      try congruence; repeat find_injection
  end.
Qed.

Lemma sc_immut_invoke_APPR : forall et st r st',
  invoke_APPR et st = (r, st') ->
  st_config st = st_config st'.
Proof.
  induction et; simpl in *; intuition; ffa using cvm_monad_unfold;
  find_apply_lem_hyp sc_immut_split_evidence;
  simpl in *; ff.
Qed.

Lemma sc_immut_better : forall t st r st',
  build_cvm t st = (r, st') ->
  st_config st = st_config st'.
Proof.
  induction t; repeat (cvm_monad_unfold; simpl in *); intuition;
  ffa using cvm_monad_unfold;
  find_apply_lem_hyp sc_immut_invoke_APPR; ff.
Qed.

Ltac monad_simp := 
  repeat (cvm_monad_unfold; simpl in *; eauto).

Lemma check_cvm_policy_preserves_state : forall t p evt st1 st1' r,
  check_cvm_policy t p evt st1 = (r, st1') ->
  st1 = st1'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using cvm_monad_unfold.
Qed.
Global Hint Resolve check_cvm_policy_preserves_state : core.

Lemma check_cvm_policy_same_outputs : forall t p evt st1 st1' r1 st2 st2' r2,
  check_cvm_policy t p evt st1 = (r1, st1') ->
  check_cvm_policy t p evt st2 = (r2, st2') ->
  (policy (st_config st1) = policy (st_config st2)) ->
  r1 = r2 /\ st1 = st1' /\ st2 = st2'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using cvm_monad_unfold.
Qed.
Global Hint Resolve check_cvm_policy_same_outputs : core.

Lemma invoke_APPR_deterministic : forall e st1 st2 st1' st2' res1 res2,
  st_ev st1 = st_ev st2 ->
  st_evid st1 = st_evid st2 ->
  st_config st1 = st_config st2 ->
  invoke_APPR e st1 = (res1, st1') ->
  invoke_APPR e st2 = (res2, st2') ->
  res1 = res2 /\ st_ev st1' = st_ev st2' /\ 
  st_evid st1' = st_evid st2' /\ st_config st1' = st_config st2'.
Proof.
  induction e; simpl in *; intros;
  try (cvm_monad_unfold; intuition; repeat find_injection; eauto; fail).
  - cvm_monad_unfold; repeat find_rewrite.
    repeat (
      break_match;
      simpl in *;
      repeat find_injection; simpl in *; eauto; try congruence
    ).
  - cvm_monad_unfold; destruct a; repeat find_rewrite;
    destruct (Maps.map_get (asp_comps (session_context (st_config st2))) a) eqn:?;
    simpl in *; repeat find_rewrite; repeat find_injection; eauto;
    ff. 
  - cvm_monad_unfold; repeat find_rewrite; repeat find_injection; eauto;
    repeat break_match; repeat find_injection;
    repeat (match goal with
      | H1 : split_evidence _ _ _ _ = _,
        H2 : split_evidence _ _ _ _ = _ |- _ =>
        eapply split_evidence_determinisitic in H1;
        [ | | eapply H2]; clear H2; simpl in *; eauto;
        destruct_conjs; repeat find_injection; eauto; try congruence
      | H1 : invoke_APPR ?e _ = _,
        H2 : invoke_APPR ?e _ = _,
        IH : context[invoke_APPR ?e _ = _ -> _] |- _ =>
        eapply IH in H1;
        [ | | | | eapply H2]; clear H2 IH; simpl in *; eauto;
        destruct_conjs; repeat find_injection; eauto; try congruence
      end);
    repeat find_rewrite; eauto.
Qed.

(* Theorem EvidenceT_deterministic_output_on_results : forall t e tr1 tr2 i1 i2 ac st1 st2,
  build_cvm t {| st_ev := e; st_trace := tr1; st_evid := i1; st_config := ac |} = (resultC tt, st1) ->
  build_cvm t {| st_ev := e; st_trace := tr2; st_evid := i2; st_config := ac |} = (resultC tt, st2) ->
  st1.(st_ev) = st2.(st_ev).
Proof.
  induction t; intros; monad_simp; ffa using cvm_monad_unfold;
  repeat match goal with
  | u : unit |- _ => destruct u
  | st : cvm_st |- _ => destruct st
  | H1 : build_cvm ?t ?st1 = (?res1, ?st1'),
    H2 : build_cvm ?t ?st2 = (?res2, ?st2'),
    IH : context[build_cvm ?t _ = _ -> _] |- _ =>
      assert (Cvm_St.st_config st1 = Cvm_St.st_config st1') by (
        eapply sc_immut_better in H1; ffa);
      assert (Cvm_St.st_config st2 = Cvm_St.st_config st2') by (
        eapply sc_immut_better in H2; ffa);
      eapply IH in H1; [ | eapply H2]; ffa
  end.
  - destruct e; simpl in *.
  - find_rewrite; find_injection.
    unfold Evidence_Bundlers.ss_cons; ff.
  
    * destruct s; simpl in *.
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite;
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite;
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite;
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite;
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite;
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite;
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite;
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite;
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite;
      break_match; simpl in *; try congruence;
      repeat find_injection; repeat find_rewrite.
      ff.
    destruct s.
    break_match; simpl in *.
  ff.
Qed. *)

Lemma cvm_deterministic :  forall t st1 st2 r1 r2 st1' st2',
  st_config st1 = st_config st2 ->
  st_ev st1 = st_ev st2 ->
  st_evid st1 = st_evid st2 ->
  build_cvm t st1 = (r1, st1') ->
  build_cvm t st2 = (r2, st2') ->
  (
    (r1 = r2) /\ 
    (st_ev st1' = st_ev st2') /\
    (st_evid st1' = st_evid st2') /\
    (st_config st1' = st_config st2')
  ).
Proof.
  induction t; intros;
  try (simpl in *; cvm_monad_unfold; ff;
  repeat match goal with
  | u : unit |- _ => destruct u
  | H1 : build_cvm ?t _ = _,
    H2 : build_cvm ?t _ = _,
    IH : context[build_cvm ?t _ = _ -> _] |- _ =>
      eapply IH in H1; try (eapply H2);
      clear IH H2; try (intuition; congruence)
  end; intuition; symmetry; ff).
  - simpl in *; cvm_monad_unfold;
    destruct a; simpl in *;
    try (repeat find_injection;
      simpl in *; intuition; fail);
    try destruct s; simpl in *;
    repeat find_rewrite; try ff;
    find_eapply_lem_hyp invoke_APPR_deterministic; eauto;
    intuition; eauto; try congruence;
    destruct u; eauto.
Qed.

(* Lemma stating the following:  If all starting parameters to the cvm_st are the same, except 
   for possibly the trace, then all of those final parameters should also be equal. *)
Lemma st_trace_irrel : forall t e e' e'' x x' y y' i i' i'' ac ac' ac'' res,
    build_cvm t {| st_ev := e; st_trace := x; st_evid := i; st_config := ac |} =
    (res, {| st_ev := e'; st_trace := x'; st_evid := i'; st_config := ac' |}) ->
    build_cvm t {| st_ev := e; st_trace := y; st_evid := i; st_config := ac |} =
    (res, {| st_ev := e''; st_trace := y'; st_evid := i''; st_config := ac'' |}) ->
    (e' = e'' /\ i' = i'' /\ ac' = ac'').
Proof.
  intros; find_eapply_lem_hyp cvm_deterministic; 
  try eapply H; simpl in *; intuition; eauto.
Qed.

Ltac do_st_trace :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_evid := ?i; st_config := ?ac |}]
     |- context[?tr]] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_evid := i; st_config := ac |} )
      tauto
  end.

Ltac do_st_trace_assumps :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_evid := ?i; st_config := ?ac |}]
     |- _] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_evid := i; st_config := ac |} )
      tauto
  end.

Ltac find_rw_in_goal :=
  match goal with
  | [H': context[?x = _]
     |- context[?x]] =>
    rewrite H'; clear H'
  end.


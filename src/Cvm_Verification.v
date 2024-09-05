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

(* 
Lemma sc_immut_peel_n_rawev : forall n r st res st',
  peel_n_rawev n r st = (res, st') ->
  st_config st = st_config st'.
Proof.
  induction n; simpl in *; intuition; cvm_monad_unfold; ff.
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
*)

Lemma sc_immut_split_evidence : forall st res st',
  split_evidence st = (res, st') ->
  st_config st = st_config st'.
Proof.
  unfold split_evidence in *; cvm_monad_unfold; ff.
Qed.

Lemma split_evidence_determinisitic : forall st1 st2 res1 res2 st1' st2',
  st_config st1 = st_config st2 ->
  st_ev st1 = st_ev st2 ->
  split_evidence st1 = (res1, st1') ->
  split_evidence st2 = (res2, st2') ->
  res1 = res2.
Proof.
  intros.
  unfold split_evidence in *.
  cvm_monad_unfold; repeat find_rewrite; ff.
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

Lemma split_evidence_state_immut : forall res st st',
  split_evidence st = (res, st') ->
  st = st'.
Proof.
  unfold split_evidence in *; cvm_monad_unfold; ff.
Qed.

Lemma sc_immut_invoke_APPR : forall et st r st',
  invoke_APPR et st = (r, st') ->
  st_config st = st_config st'.
Proof.
  induction et; simpl in *; intuition; ffa using cvm_monad_unfold;
  try (find_apply_lem_hyp sc_immut_split_evidence;
  simpl in *; ff).
Qed.

Lemma sc_immut_better : forall t st r st',
  build_cvm t st = (r, st') ->
  st_config st = st_config st'.
Proof.
  induction t; repeat (cvm_monad_unfold; simpl in *); intuition;
  ffa using cvm_monad_unfold;
  try (find_apply_lem_hyp sc_immut_invoke_APPR; ff; fail).
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
  - cvm_monad_unfold;
    repeat (break_match; repeat find_rewrite; repeat find_injection;
      simpl in *; eauto; try congruence; eauto;
      let n := numgoals in guard n <= 1).
    break_match.
    * ff.
    * ff; eapply IHe in H2; try eapply H3; ff.
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
      | H1 : invoke_APPR ?e _ = _,
        H2 : invoke_APPR ?e _ = _,
        IH : context[invoke_APPR ?e _ = _ -> _] |- _ =>
        eapply IH in H1; try eapply H2; ff
      end.
  - cvm_monad_unfold; repeat find_rewrite; repeat find_injection; eauto;
    repeat break_match; repeat find_injection;
    match goal with
    | H1 : split_evidence _ = _,
      H2 : split_evidence _ = _ |- _ =>
      eapply split_evidence_state_immut in H1 as ?;
      eapply split_evidence_state_immut in H2 as ?;
      eapply split_evidence_determinisitic in H1;
      [ | | | eapply H2]; clear H2; simpl in *; eauto;
      destruct_conjs; repeat find_injection; eauto; try congruence
    end; 
    repeat (match goal with
    | H1 : split_evidence _ _ _ _ = _,
      H2 : split_evidence _ _ _ _ = _ |- _ =>
      eapply split_evidence_determinisitic in H1;
      [ | | eapply H2]; clear H2; simpl in *; eauto;
      destruct_conjs; repeat find_injection; eauto; try congruence
    | H1 : invoke_APPR ?e _ = _,
      H2 : invoke_APPR ?e _ = _,
      IH : context[invoke_APPR ?e _ = _ -> _] |- _ =>
      eapply IH in H1; [ | | | | eapply H2]; clear H2 IH; simpl in *; eauto;
      destruct_conjs; repeat find_injection; eauto; try congruence
    end);
    repeat find_rewrite; eauto; ff.
Qed.

Theorem invoke_APPR_deterministic_Evidence : forall et st1 st2 r1 r2 st1' st2',
  st_config st1 = st_config st2 ->
  st_ev st1 = st_ev st2 ->
  invoke_APPR et st1 = (r1, st1') ->
  invoke_APPR et st2 = (r2, st2') ->
  r1 = r2 /\ st_ev st1' = st_ev st2'.
Proof.
  induction et; ff; cvm_monad_unfold; ff;
  repeat match goal with
  | H1 : split_evidence _ = _,
    H2 : split_evidence _ = _ |- _ =>
    let H' := fresh in
    eapply split_evidence_determinisitic in H1 as H';
    try eapply H2; ff; 
    eapply split_evidence_state_immut in H1;
    eapply split_evidence_state_immut in H2;
    simpl in *; ff
  end;
  match goal with
  | H1 : invoke_APPR ?e _ = _,
    H2 : invoke_APPR ?e _ = _,
    IH : context[invoke_APPR ?e _ = _ -> _] |- _ =>
    eapply IH in H1; try eapply H2; ff
  end;
  try (repeat find_eapply_lem_hyp sc_immut_invoke_APPR; ff; fail).
  eapply IHet1 in Heqp3; try eapply Heqp0; ff.
Qed.

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
  induction t; simpl in *; cvm_monad_unfold; ff;
  try (repeat match goal with
  | u : unit |- _ => destruct u
  | H1 : build_cvm ?t _ = _,
    H2 : build_cvm ?t _ = _,
    IH : context[build_cvm ?t _ = _ -> _] |- _ =>
      eapply IH in H1; try (eapply H2);
      clear IH H2; try (intuition; congruence)
  end; fail);
  find_eapply_lem_hyp invoke_APPR_deterministic; ff;
  try congruence;
  match goal with
  | u : unit |- _ => destruct u
  end; eauto.
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
    eapply events_fix_errs_deterministic in H1; try eapply H2; ff; fail
  end.
  destruct a; simpl in *;
  try (destruct e; simpl in *; congruence);
  find_eapply_lem_hyp appr_events'_errs_deterministic; 
  unfold appr_events in *; ff.
Qed.

Theorem cvm_deterministic_Evidence : forall t st1 st2 r1 r2 st1' st2',
  st_config st1 = st_config st2 ->
  st_ev st1 = st_ev st2 ->
  build_cvm t st1 = (r1, st1') ->
  build_cvm t st2 = (r2, st2') ->
  r1 = r2 /\ st_ev st1' = st_ev st2'.
Proof.
  induction t; simpl in *; cvm_monad_unfold.
  - ff;
    match goal with
    | H1 : invoke_APPR _ _ = _,
      H2 : invoke_APPR _ _ = _ |- _ =>
      eapply invoke_APPR_deterministic_Evidence in H1;
      try eapply H2; ff
    end.
  - ff; (* NOTE: Why dont we need the remote axiom here!? *)
    match goal with
    | H1 : events_fix _ _ _ ?t _ = _,
      H2 : events_fix _ _ _ ?t _ = _ |- _ =>
      try (eapply events_fix_only_one_error in H1; try eapply H2; ff; fail);
      try (eapply events_fix_errs_deterministic in H1; try eapply H2; ff; fail)
    end.
  - ff; repeat match goal with
    | u : unit |- _ => destruct u
    | H1 : build_cvm ?t _ = _,
      H2 : build_cvm ?t _ = _,
      IH : context[build_cvm ?t _ = _ -> _] |- _ =>
        eapply sc_immut_better in H1 as ?;
        eapply sc_immut_better in H2 as ?;
        simpl in *; ff;
        eapply IH in H1; try (eapply H2);
        clear IH H2; try (intuition; congruence)
    end.
  - ff; repeat match goal with
    | u : unit |- _ => destruct u
    | H1 : build_cvm ?t _ = _,
      H2 : build_cvm ?t _ = _,
      IH : context[build_cvm ?t _ = _ -> _] |- _ =>
        eapply sc_immut_better in H1 as ?;
        eapply sc_immut_better in H2 as ?;
        simpl in *; ff;
        eapply IH in H1; try (eapply H2);
        clear IH H2; try (intuition; congruence)
    end.
  - ff; simpl in *; 
    repeat match goal with
    | u : unit |- _ => destruct u
    | H : parallel_vm_thread _ _ _ _ = resultC _ |- _ => 
      eapply parallel_vm_thread_res_axiom in H;
      try reflexivity; break_exists
    | H : parallel_vm_thread _ _ _ _ = errC _ |- _ => 
      eapply parallel_vm_thread_err_axiom in H;
      try reflexivity; break_exists
    | H1 : build_cvm ?t _ = _,
      H2 : build_cvm ?t _ = _,
      IH : context[build_cvm ?t _ = _ -> _] |- _ =>
        eapply sc_immut_better in H1 as ?;
        eapply sc_immut_better in H2 as ?;
        simpl in *; ff;
        eapply IH in H1; try (eapply H2);
        clear IH H2; try (intuition; congruence)
    end;
    match goal with
    | H1 : events_fix _ _ _ ?t _ = _,
      H2 : events_fix _ _ _ ?t _ = _ |- _ =>
      try (eapply events_fix_only_one_error in H1; try eapply H2; ff; fail);
      try (eapply events_fix_errs_deterministic in H1; try eapply H2; ff; fail)
    end.
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
  try eapply H; ff.
Qed.

Lemma invoke_APPR_spans : forall et u c i st,
  invoke_APPR et st = (resultC u, c) ->
  forall G,
  G = session_context (st_config st) ->
  appr_events_size G et = resultC i ->
  st_evid c = st_evid st + i.
Proof.
  induction et; ffa using (try cvm_monad_unfold; try result_monad_unfold);
  repeat match goal with
  | H : split_evidence _ = _ |- _ =>
    eapply split_evidence_state_immut in H as ?; ff;
    clear H
  | H : Nat.eqb _ _ = _ |- _ => 
    try (erewrite PeanoNat.Nat.eqb_eq in H);
    try (erewrite PeanoNat.Nat.eqb_neq in H);
    ff; try lia
  | H : invoke_APPR ?e _ = _,
    IH : context[invoke_APPR ?e _ = _ -> _] |- _ =>
    eapply sc_immut_invoke_APPR in H as ?; ff;
    let numgoals := numgoals in
    eapply IH in H; ff; try lia;
    let numgoals' := numgoals in
    guard numgoals' <= numgoals
  end.
Qed.

Inductive et_same_asps : EvidenceT -> EvidenceT -> Prop :=
(* | et_same_asps_refl : forall e, et_same_asps e e *)
(* | et_same_asps_symm : forall e1 e2, et_same_asps e1 e2 -> et_same_asps e2 e1 *)
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

Theorem invoke_appr_evidence : forall st st' u et e,
  invoke_APPR et st = (resultC u, st') ->
  appr_procedure' (session_context (st_config st)) 
    (session_plc (st_config st)) et (get_et (st_ev st)) = resultC e ->
  get_et (st_ev st') = e.
Proof.
  destruct st; simpl in *; destruct st_ev; 
  simpl in *; ff.
  generalizeEverythingElse et.
  induction et; ff;
  cvm_monad_unfold; result_monad_unfold; ff.
  - eapply IHet in Heqp2; ff.
  - eapply IHet in Heqp2; ff.
  - eapply IHet in Heqp2; ff.
  - unfold split_evidence in *; cvm_monad_unfold; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    repeat match goal with
    | H : invoke_APPR ?e _ = _,
      H1 : appr_procedure' _ _ ?e _ = _,
      IH : context[invoke_APPR ?e _ = _ -> _] |- _ =>
      eapply sc_immut_invoke_APPR in H as ?;
      eapply IH in H; [ | eapply H1 ]; ff
    end; ff. 
Qed.

(* 
Theorem invoke_appr_evidence : forall st st' u et e,
  invoke_APPR et st = (resultC u, st') ->
  appr_procedure' (session_context (st_config st)) 
    (session_plc (st_config st)) et (get_et (st_ev st)) = resultC e ->
  get_et (st_ev st') = e.
Proof.
  destruct st; simpl in *; destruct st_ev; simpl in *;
  ff.
  generalizeEverythingElse et.
  induction et; ff; try (cvm_monad_unfold; result_monad_unfold; ff; fail).
  - result_monad_unfold; ff. 
    cvm_monad_unfold; ff; admit.
  - cvm_monad_unfold; result_monad_unfold; ff.
    unfold split_evidence in *; cvm_monad_unfold; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff.
    Search "split_evidence".
    find_eapply_lem_hyp split_evidence_res_spec.
    find_eapply_lem_hyp split_evidence_res_spec. 
  - eapply peel_n_rawev_state_immut in Heqp0 as ?; ff.  
    eapply peel_n_rawev_result_spec in Heqp0; ff.
    unfold ss_cons; ff.
    eapply IHet in Heqp2; ff.
    ff.
  - cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff. 
  - cvm_monad_unfold; ff. 
    * result_monad_unfold; ff.
      eapply peel_n_rawev_state_immut in Heqp0 as ?; ff.
      eapply peel_n_rawev_result_spec in Heqp0; ff.
      unfold ss_cons; ff.
      eapply IHet in Heqp2; ff.
      find_eapply_lem_hyp peel_n_rawev_result_spec; ff.
    * admit. 
    *  

Theorem invoke_appr_evidence : forall st st' u e,
  (* well_formed_context (session_context (st_config st)) -> *)
  invoke_APPR (get_et (st_ev st)) st = (resultC u, st') ->
  appr_procedure (session_context (st_config st)) 
    (session_plc (st_config st)) (get_et (st_ev st)) = resultC e ->
  get_et (st_ev st') = e.
Proof.
  intros;
  destruct st; simpl in *; destruct st_ev; simpl in *.
  unfold appr_procedure in *.
  generalizeEverythingElse e0;
  induction e0; simpl in *; intuition; ff.
  - cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff. 
  - cvm_monad_unfold; ff.
    * find_eapply_lem_hyp IHe0.
    unfold well_formed_context in *; ff.
  destruct_conjs; ff.
Qed.
*)

Theorem cvm_evidence_type : forall t st u st' e,
  build_cvm t st = (resultC u, st') ->
  eval (session_context (st_config st)) (session_plc (st_config st)) 
    (get_et (st_ev st)) t = resultC e ->
  get_et (st_ev st') = e.
Proof.
  induction t; simpl in *; intuition.
  - cvm_monad_unfold; destruct a; simpl in *;
    repeat find_injection; simpl in *; try congruence;
    unfold well_formed_context in *; simpl in *; destruct_conjs;
    ff; repeat find_rewrite; simpl in *; eauto.
    eapply invoke_appr_evidence in Heqp0; ff.
  - cvm_monad_unfold; ffa;
    find_eapply_lem_hyp do_remote_res_axiom; ff;
    find_eapply_lem_hyp IHt; ff.
    Unshelve. all: eauto; try eapply (st_config st).
  - ffa using (try cvm_monad_unfold; try result_monad_unfold);
    match goal with
    | H1 : build_cvm ?t1 _ = _,
      H2 : build_cvm ?t2 _ = _,
      IH1 : context[build_cvm ?t1 _ = _ -> _],
      IH2 : context[build_cvm ?t2 _ = _ -> _] |- _ =>
      eapply IH1 in H1 as ?; ff;
      eapply sc_immut_better in H1; 
      eapply IH2 in H2; ff
    end.
  - ffa using (try cvm_monad_unfold; try result_monad_unfold);
    destruct s, s, s0; simpl in *;
    eapply IHt1 in Heqp as ?; ff;
    eapply sc_immut_better in Heqp; simpl in *; ff;
    eapply IHt2 in Heqp0 as ?; simpl in *;
    eapply sc_immut_better in Heqp0; simpl in *; try (find_higher_order_rewrite; ff; fail);
    ff; find_higher_order_rewrite; eauto.
  - ffa using (try cvm_monad_unfold; try result_monad_unfold);
    destruct s, s, s0; simpl in *;
    eapply IHt1 in Heqp as ?; ff;
    eapply sc_immut_better in Heqp; simpl in *; ff;
    find_eapply_lem_hyp parallel_vm_thread_res_axiom; eauto;
    break_exists; destruct_conjs; find_eapply_lem_hyp IHt2; ff;
    repeat find_rewrite; try unfold mt_evc; simpl in *; ff.
Qed.

(** * Lemma:  CVM increases event IDs according to event_id_span' denotation. *)
Lemma cvm_spans: forall t st u e st' sc i,
  st_config st = sc ->
  well_formed_context (session_context sc) ->
  get_et (st_ev st) = e ->
  build_cvm t st = (resultC u, st') ->
  events_size (session_context sc) (session_plc sc) e t = resultC i ->
  st_evid st' = st_evid st + i.
Proof.
  induction t; simpl in *; intuition.
  - cvm_monad_unfold; ff;
    find_eapply_lem_hyp invoke_APPR_spans; ff. 
  - cvm_monad_unfold; ff; result_monad_unfold; 
    ff; find_eapply_lem_hyp events_size_plc_irrel;
    try eapply Heqr; ff; lia.
  - cvm_monad_unfold; result_monad_unfold; ff.
    repeat match goal with
    | H : build_cvm ?t _ = _,
      H1 : events_size _ _ _ ?t = _,
      IH : context[build_cvm ?t _ = _ -> _] |- _ => 
      eapply sc_immut_better in H as ?;
      eapply IH in H as ?; try eapply H1;
      simpl in *; ff; [
        try (eapply cvm_evidence_type in H as ?; ff; [])
      ]; clear H IH
    end; lia.
  - cvm_monad_unfold; result_monad_unfold; ff;
    repeat match goal with
    | st : cvm_st |- _ => destruct st; simpl in *; ff
    | s : Split |- _ => destruct s as [s1 s2]; simpl in *; ff
    | H : build_cvm ?t _ = _,
      IH : context[build_cvm ?t _ _ = _ -> _] |- _ => 
      eapply sc_immut_better in H as ?;
      eapply IH in H; simpl in *; ff
    end; 
    try (repeat match goal with
    | H1 : build_cvm ?t _ = _,
      H2 : events_size _ _ _ ?t = _,
      IH : context[build_cvm ?t _ = _ -> _] |- _ => 
      eapply IH in H1 as ?;
      try eapply H2; simpl in *;
      eapply sc_immut_better in H1; simpl in *; eauto; ff; []
    end; lia).
  - ffa using (try result_monad_unfold; try cvm_monad_unfold).
    eapply sc_immut_better in Heqp as ?;
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
  rewrite app_length; ff.
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

Lemma split_evidence_res_spec : forall r et1 et2 st st' e1 e2,
  evc r (split_evt et1 et2) = st_ev st ->
  split_evidence st = (resultC (e1, e2), st') ->
  exists r1 r2, (e1,e2) = (evc r1 et1, evc r2 et2).
Proof.
  intros.
  destruct st; simpl in *; ff.
  unfold split_evidence in *;
  cvm_monad_unfold; ff.
Qed.

Lemma wf_Evidence_split_evidence : forall r et1 et2 st st' G r1 r2,
  wf_Evidence G (evc r (split_evt et1 et2)) ->
  session_context (st_config st) = G ->
  split_evidence st = (resultC (r1, r2), st') ->
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

Lemma wf_Evidence_split_unfold : forall G r e1 e2,
  wf_Evidence G (evc r (split_evt e1 e2)) ->
  (exists r1, wf_Evidence G (evc r1 e1)) /\ (exists r2, wf_Evidence G (evc r2 e2)).
Proof.
  intros.
  prep_induction H;
  induction H; ff; result_monad_unfold; ff;
  break_and_goal; eapply wf_Evidence_exists; ff.
Qed.

Lemma wf_Evidence_invoke_APPR : forall e st u st',
  wf_Evidence (session_context (st_config st)) e -> 
  wf_Evidence (session_context (st_config st)) (st_ev st) -> 
  (* (st_ev st) -> *)
  invoke_APPR (get_et e) st = (resultC u, st') ->
  wf_Evidence (session_context (st_config st)) (st_ev st').
Proof.
  destruct e.
  generalizeEverythingElse e.
  induction e; simpl in *; intuition; cvm_monad_unfold.
  - repeat find_injection; eapply wf_Evidence_mt_evc. 
  - ff;
    eapply wf_Evidence_impl_et_size_res in H as ?;
    eapply wf_Evidence_impl_et_size_res in H0 as ?;
    invc H; invc H0; ff;
    rewrite PeanoNat.Nat.eqb_eq in *;
    econstructor; ff;
    result_monad_unfold; ff;
    rewrite app_length; ff.
  - ff; rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat rewrite app_length in *; ff;
    try (econstructor; invc H; invc H0; 
      repeat rewrite app_length in *; ff; fail);
    try (eapply wf_Evidence_asp_unfold in H as ?;
      ff; eapply IHe in H1; simpl in *; eauto;
      try (econstructor; invc H; invc H0; 
      repeat rewrite app_length in *; ff; fail); fail).
    all: admit.

  - ff.
    find_copy_eapply_lem_hyp wf_Evidence_split_evidence; ff.
    unfold split_evidence in *; cvm_monad_unfold; ff.
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec;
    ff; rewrite app_nil_r in *; ff.
    eapply wf_Evidence_split in H; ff.
    eapply split_evidence_res_spec in Heqp; simpl in *.
    find_copy_eapply_lem_hyp split_evidence_res_spec; eauto.
    find_copy_eapply_lem_hyp split_evidence_state_immut; ff;
    find_eapply_lem_hyp wf_Evidence_split_evidence; ff.
    * 
      eapply IHe in Heqp2; simpl in *.

      eapply wf_Evidence_asp_unfold in H as ?; ff.
      eapply IHe in Heqp2; simpl in *; eauto;
      try (econstructor; invc H; invc H0; 
      repeat rewrite app_length in *; ff; fail).
    * eapply wf_Evidence_asp_unfold in H as ?;
      ff; eapply IHe in H1; simpl in *; eauto;
      try (econstructor; invc H; invc H0; 
      repeat rewrite app_length in *; ff; fail).
      ff.
      break_exists; ff.
      find_eapply_lem_hyp wf_Evidence_asp_unfold; ff.
      eapply H.
      eapply wf_Evidence_asp_unfold.


  destruct st, st_ev; simpl in *;
  generalizeEverythingElse e;
  induction e; simpl in *; intuition;
  cvm_monad_unfold.
  - find_injection; eapply wf_Evidence_mt_evc. 
  - ff; invc H; simpl in *;
    rewrite PeanoNat.Nat.eqb_eq in *;
    econstructor; ff;
    rewrite app_length; ff.
  - ff; rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat rewrite app_length in *; ff;
    try (econstructor; invc H; repeat rewrite app_length in *; ff; fail).
    * admit.
    *  
    all: admit.
  - ff. 
    find_copy_eapply_lem_hyp split_evidence_state_immut; ff;
    find_copy_eapply_lem_hyp split_evidence_res_spec; ff.
    eapply wf_Evidence_split_evidence in H; try eapply Heqp;
    ff.
    eapply sc_immut_invoke_APPR in Heqp0 as ?;
    eapply sc_immut_invoke_APPR in Heqp1 as ?;
    simpl in *; ff.
    eapply IHe1 in Heqp0; eauto.
    eapply IHe2 in Heqp1; eauto;
    ff;
    invc Heqp0; invc Heqp1; econstructor;
    repeat rewrite app_length; ff. 
    find_copy_eapply_lem_hyp sc_immut_invoke_APPR;
    find_eapply_lem_hyp IHe1; ff;
    find_copy_eapply_lem_hyp sc_immut_invoke_APPR;
    find_eapply_lem_hyp IHe2; ff.
    find_eapply_lem_hyp IHe1; ff.
    find_eapply_lem_hyp wf_Evidence_split_evidence; ff.
    eapply wf_Evidence_split_evidence in H
    * eapply IHe in H.
    try (econstructor; ff; result_monad_unfold; ff;
      find_copy_eapply_lem_hyp wf_Evidence_impl_et_size_res; ff;
      rewrite PeanoNat.Nat.eqb_eq in *; ff; fail);
    try (invc H; 
      rewrite PeanoNat.Nat.eqb_eq in *;
      econstructor; try rewrite app_length; ff).
      ff.
      rewrite 
    ff; result_monad_unfold; ff.
    econstructor; ff.
    *  
  try eapply wf_Evidence_mt_evc.
  - econstructor; ff. 


  repeat find_injection; simpl in *;
  try eapply wf_Evidence_mt_evc;
  ff;
  try match goal with
  | H : Nat.eqb _ _ = true |- _ =>
    rewrite PeanoNat.Nat.eqb_eq in H
  end;
  try (econstructor; simpl in *; ff; fail).
  try (invc H;
    econstructor; ff;
    repeat find_rewrite;
    repeat find_injection;
    result_monad_unfold; ff;
    repeat rewrite app_length;
    f_equal; lia).
  eapply split_evidence_state_immut in Heqp as ?;
  eapply wf_Evidence_split_evidence in Heqp as ?;
  eapply split_evidence_res_spec in Heqp;
  break_exists; ff; destruct_conjs;
  eapply sc_immut_invoke_APPR in Heqp0 as ?;
  eapply IHe1 in Heqp0; eauto;
  eapply sc_immut_invoke_APPR in Heqp1 as ?;
  eapply IHe2 in Heqp1; ff;
  simpl in *; repeat find_rewrite.
  eapply wf_Evidence_ss_cons; 
  simpl in *; eauto.
  Unshelve. all: eapply 0.
Qed.


(** * Theorem:  CVM execution preserves well-formedness of Evidence bundles 
      (EvidenceT Type of sufficient length for raw EvidenceT). *)
Theorem cvm_preserves_wf_Evidence : forall t st st' e e' u,
  wf_Evidence (session_context (st_config st)) e ->
  st_ev st = e ->
  build_cvm t st = (resultC u, st') ->
  st_ev st' = e' ->
  wf_Evidence (session_context (st_config st)) e'.
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
      repeat rewrite app_length;
      f_equal; lia);
    eapply wf_Evidence_invoke_APPR; eauto.
  - ff;
    find_eapply_lem_hyp do_remote_res_axiom; eauto;
    break_exists; destruct_conjs;
    eapply IHt in H0; eauto;
    destruct x, st_ev; simpl in *; ff.
    Unshelve. eapply 0.
  - ff;
    repeat match goal with
    | H1 : build_cvm ?t1 _ = _,
      IH : context[build_cvm ?t1 _ = _ -> _]
      |- _ =>
      eapply sc_immut_better in H1 as ?;
      eapply IH in H1; simpl in *;
      try reflexivity; ff; check_num_goals_le 1
    end.
  - ffa; simpl in *;
    eapply wf_Evidence_ss_cons; [ 
      eapply IHt1 in Heqp; simpl in *; try reflexivity;
      eauto with wf_Evidence |
      eapply sc_immut_better in Heqp; simpl in *;
      eapply IHt2 in Heqp0; simpl in *; try reflexivity;
      repeat find_rewrite; eauto with wf_Evidence ].
  - ffa; simpl in *;
    eapply wf_Evidence_ss_cons; [
      eapply IHt1 in Heqp; simpl in *; try reflexivity;
      eauto with wf_Evidence | ];
    find_eapply_lem_hyp parallel_vm_thread_res_axiom;
    simpl in *; try reflexivity;
    break_exists; destruct_conjs;
    eapply sc_immut_better in Heqp;
    eapply IHt2 in H0;
    simpl in *; try reflexivity;
    repeat find_rewrite; ff;
    eauto with wf_Evidence.
Qed.

(** * Main Theorem: CVM traces are respected the reference "events"
      semantics. *)
Theorem cvm_trace_respects_events : forall t st m st' i p e G evs u,
  well_formed_context G ->
  events G (cop_phrase p e t) i evs ->
  st_trace st = m ->
  st_evid st = i ->
  session_plc (st_config st) = p ->
  get_et (st_ev st) = e ->
  session_context (st_config st) = G ->
  build_cvm t st = (resultC u, st') ->
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
    generalizeEverythingElse e0.
    induction e0; simpl in *; intros; cvm_monad_unfold; ffa.
    * rewrite app_nil_r; eauto. 
    * result_monad_unfold; simpl in *; ffa;
      eapply split_evidence_state_immut in Heqp as ?;
      eapply split_evidence_res_spec in Heqp as ?;
      clear Heqp;
      break_exists; repeat find_injection;
      simpl in *;
      repeat match goal with
      | st : cvm_st |- _ => destruct st; simpl in *; ff
      | e : Evidence |- _ => destruct e; simpl in *; ff
      end;
      repeat find_rewrite; repeat find_injection;
      eapply IHe0_1 in Heqp1 as ?; ff;
      eapply sc_immut_invoke_APPR in Heqp1 as ?; simpl in *;
      eapply invoke_APPR_spans in Heqp1; simpl in *;
      try eapply asp_appr_events_size_works; eauto; ff;
      unfold ss_cons in *; ff; simpl in *;
      eapply IHe0_2 in Heqp2 as ?; try ff;
      eapply sc_immut_invoke_APPR in Heqp2 as ?; simpl in *;
      eapply invoke_APPR_spans in Heqp2; simpl in *;
      try eapply asp_appr_events_size_works; eauto; ff;
      repeat find_rewrite;
      repeat rewrite <- app_assoc; ff.
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
    Unshelve. all: try eapply (st_config st); try eapply 0.

  - ff; invc H0; cvm_monad_unfold; ff;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff;
    eapply IHt1 in Heqp as ?; eauto;
    eapply sc_immut_better in Heqp as ?;
    eapply IHt2 in H6; try eapply H11;
    simpl in *; eauto; ff.
    * repeat rewrite app_assoc; eauto.
    * eapply cvm_spans; ff;
      repeat find_rewrite; eauto;
      eapply events_range; eauto.
    * eapply cvm_evidence_type; try eapply Heqp; ff.
  - ffa; invc H0; ffa;
    cvm_monad_unfold; ffa;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff.
    eapply IHt1 in Heqp as ?; eauto;
    try (destruct s, s, s0; ff; fail);
    eapply sc_immut_better in Heqp as ?;
    eapply cvm_spans in Heqp as ?; eauto; ff;
    try (repeat find_rewrite; simpl in *;
      destruct s, s, s0; simpl in *; 
      eapply events_range; eauto; ff; fail);
    repeat find_rewrite;
    eapply IHt2 in Heqp0 as ?; try eapply H11;
    eapply sc_immut_better in Heqp0 as ?;
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
    eapply IHt1 in Heqp as ?; eauto;
    try (destruct s, s, s0; ff; fail);
    eapply sc_immut_better in Heqp as ?;
    eapply cvm_spans in Heqp as ?; eauto; ff;
    try (repeat find_rewrite; simpl in *;
      destruct s, s, s0; simpl in *; 
      eapply events_range; eauto; ff; fail);
    repeat find_rewrite; try lia.
    repeat rewrite <- app_assoc; simpl in *;
    destruct s, s, s0; simpl in *;
    repeat find_rewrite; repeat find_injection; eauto;
    assert (st_evid st + 2 + length evs1 = st_evid st + 1 + 1 + length evs1) by lia; repeat find_rewrite;
    erewrite events_events_fix_eq in H13;
    repeat find_rewrite; find_injection;
    simpl in *; ff;
    repeat find_eapply_lem_hyp events_fix_range; eauto;
    ff. 
Qed.

Corollary cvm_trace_respects_events_default : forall G,
  well_formed_context G ->
  forall t st st' i p e evs,
  st_trace st = nil ->
  st_evid st = i ->
  session_plc (st_config st) = p ->
  get_et (st_ev st) = e ->
  session_context (st_config st) = G ->
  
  events G (cop_phrase p e t) i evs ->

  build_cvm t st = (resultC tt, st') ->
  st_trace st' = evs.
Proof.
  intros.
  eapply cvm_trace_respects_events in H6; eauto;
  simpl in *; eauto.
Qed.

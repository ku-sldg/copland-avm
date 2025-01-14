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
Import ListNotations ResultNotation.

Require Import Lia Coq.Program.Tactics.

Lemma invoke_ASP_config_immut : forall par e st sc res st' sc',
  invoke_ASP e par st sc = (res, st', sc') ->
  sc = sc'.
Proof.
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

Require Import String ErrorStringConstants.

(*
Lemma invoke_APPR_config_immut : forall et r st sc res st' sc' out_et,
  invoke_APPR' r et out_et st sc = (res, st', sc') ->
  sc = sc'.
Proof.
  induction et using EvidenceT_triple_ind; intros.
  - (* mt *)
    repeat cvm_monad_unfold; ff.
  - (* nonce_evt *)
    repeat cvm_monad_unfold.
    target_break_match H.
  - (* asp (mt) *)
    repeat cvm_monad_unfold.
    target_break_match H.
  - (* asp (nonce) *)
    repeat cvm_monad_unfold.
    target_break_match H.
  - (* asp (asp (mt)) *)
    repeat cvm_monad_unfold.
    target_break_match H.
  - (* asp (asp (nonce)) *)
    repeat cvm_monad_unfold.
    target_break_match H.
  - (* asp (asp (asp))*)
    repeat cvm_monad_unfold.
    admit.
  - (* asp (asp (left))*)
    repeat cvm_monad_unfold.
    target_break_match H;
    rewrite PeanoNat.Nat.eqb_eq in *; subst;
    try (eapply IHet; 
      lazymatch goal with
      | H : apply_to_left_evt _ _ _ = _ |- _ => 
        rewrite H
      end; eauto; fail).
    * eapply IHet.
      result_monad_unfold.
      target_break_match Hbm12.
      assert (apply_to_left_evt (session_context s1)
(apply_to_asp_under_wrap (session_context s1) a
(fun e : EvidenceT =>
invoke_APPR' r1 e (asp_evt p' (asp_paramsC a a3 p2 t0) (left_evt et))))
et = apply_to_left_evt (session_context s1)
(fun e : EvidenceT => invoke_APPR' ?r e ?out_et) et). 
      find_rewrite.
    eauto.





  induction et using EvidenceT_triple_ind; simpl in *; cvm_monad_unfold;
  intros; try find_injection; try simple congruence 1.
  all: eauto 2.
  all: try (timeout 5 (target_break_match H; subst; eapply IHet; try find_rewrite; eauto; fail)).
  (* try (timeout 10 (eauto 2; target_break_match H; subst; eapply IHet; rewrite Hbm0; eauto; fail)). *)
  - target_break_match H.
  - target_break_match H.
  - admit.
  - break_match.
    break_match.
    break_match.
    break_match; subst; try simple congruence 1.
    * break_match; subst; try simple congruence 1.
    * admit.
  - break_match.
    break_match.
    target_break_match Heqp1.
    break_match.
    target_break_match Heqp1.
    break_match.
    break_match; subst.
    * timeout 10 (target_break_match H).
    * timeout 10 (target_break_match H).
    * timeout 10 (target_break_match H).
    * 
  - (* asp (asp et') case *)
    target_break_match H; try rewrite PeanoNat.Nat.eqb_eq in *.
    all: subst.
    all: eauto 2.
    all: try (timeout 5 (result_monad_unfold; ff; fail)).
    (* * rewrite String.eqb_eq in *; subst; repeat find_rewrite. *)
      (* cvm_monad_unfold.
      eapply IHet; clear IHet.
      repeat find_rewrite.
      target_break_match Heqp4; try rewrite PeanoNat.Nat.eqb_eq in *;
      subst; eauto 2; try (timeout 5 (result_monad_unfold; ff; fail)).
      all: repeat find_injection.
      eapply IHet; clear IHet; ff.
      eapply IHet; eauto. *)
    all: admit.
    (* * rewrite String.eqb_eq in *; subst.
      eapply IHet; clear IHet.
      simpl in *; cvm_monad_unfold.
      repeat find_rewrite.
      break_match.
      break_match.
      break_match.

      simpl in *; cvm_monad_unfold.
      eapply IHet; ff. *)
  - target_break_match H; try rewrite PeanoNat.Nat.eqb_eq in *;
    subst; eauto 2; try (timeout 10 (result_monad_unfold; ff;
      eapply IHet; find_higher_order_rewrite; eauto; fail)).
    * result_monad_unfold; ff.
      eapply IHet.
      admit.
  - target_break_match H; try rewrite PeanoNat.Nat.eqb_eq in *;
    subst; eauto 2; result_monad_unfold; ff;
    try (timeout 10 (eapply IHet; find_higher_order_rewrite; eauto)).
    * result_monad_unfold; ff.
      admit.
  - target_break_match H; try rewrite PeanoNat.Nat.eqb_eq in *;
    subst; eauto 2;
    try (timeout 10 (result_monad_unfold; ff;
      repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
      find_eapply_lem_hyp IHet1; subst; eauto)).
  - target_break_match H; subst;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    find_eapply_lem_hyp IHet1; subst; eauto.
Qed.
Admitted.
*)

Lemma invoke_APPR_config_immut : forall G et r st sc res st' sc' out_et,
  G = session_context sc ->
  invoke_APPR' r et out_et st sc = (res, st', sc') ->
  sc = sc'.
Proof.
  intros G.
  induction et using (Evidence_subterm_path_Ind_special G);
  simpl in *; intros;
  cvm_monad_unfold.
  - ff.
  - target_break_match H0.
  - target_break_match H2; ffa.
  - target_break_match H2.
    ateb_unpack Hbm3; ffa.
  - target_break_match H1.
  - target_break_match H1; ateb_unpack Hbm0; ffa.
  - target_break_match H1; ateb_unpack Hbm0; ffa.
  - target_break_match H0; ffa.
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

(* 
Lemma split_evidence_determinisitic : forall e st1 st2 res1 res2 st1' st2' et1 et2 sc sc1' sc2',
  split_evidence e et1 et2 st1 sc = (res1, st1', sc1') ->
  split_evidence e et1 et2 st2 sc = (res2, st2', sc2') ->
  res1 = res2.
Proof.
  intros.
  unfold split_evidence in *.
  cvm_monad_unfold; ff.
Qed.
*)

(* 
Lemma split_evidence_state_immut : forall e sc sc' res st st' et1 et2,
  split_evidence e et1 et2 st sc = (res, st', sc') ->
  st = st' /\ sc = sc'.
Proof.
  unfold split_evidence in *; cvm_monad_unfold; ff.
Qed.
*)

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

Lemma invoke_APPR_deterministic : forall G e sc sc1' sc2' st1 st2 st1' st2' res1 res2 r oe,
  G = session_context sc ->
  st_evid st1 = st_evid st2 ->
  invoke_APPR' r e oe st1 sc = (res1, st1', sc1') ->
  invoke_APPR' r e oe st2 sc = (res2, st2', sc2') ->
  res1 = res2 /\ st_evid st1' = st_evid st2' /\ 
  sc1' = sc2'.
Proof.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G);
  simpl in *; intros;
  try (cvm_monad_unfold; intuition; repeat find_injection; eauto; fail).
  - cvm_monad_unfold; ff.
  - cvm_monad_unfold.
    target_break_match H3;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    try target_break_match H4;
    match goal with
    | H1 : invoke_APPR' _ ?e _ _ _ = _,
      H2 : invoke_APPR' _ ?e _ _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; ff
    end.
  - cvm_monad_unfold;
    target_break_match H3;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto.
    ateb_unpack Hbm3; ffa.
  - cvm_monad_unfold;
    target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto.
  - cvm_monad_unfold;
    target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    ateb_unpack Hbm0; ffa.
  - cvm_monad_unfold;
    target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    ateb_unpack Hbm0; ffa.
  - cvm_monad_unfold;
    target_break_match H1;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    try target_break_match H2. 
    all: repeat match goal with
      | H1 : invoke_APPR' _ ?e _ _ _ = _,
        H2 : invoke_APPR' _ ?e _ _ _ = _,
        IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
        eapply invoke_APPR_config_immut in H1 as ?; try reflexivity;
        eapply IH in H1; [ | | | eapply H2]; ff
      end.
Qed.

Theorem invoke_APPR_deterministic_Evidence : forall G et st1 st2 r1 r2 st1' st2' r sc sc1' sc2' eo,
  G = session_context sc ->
  invoke_APPR' r et eo st1 sc = (r1, st1', sc1') ->
  invoke_APPR' r et eo st2 sc = (r2, st2', sc2') ->
  r1 = r2.
Proof.
  intros G.
  induction et using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; subst; cvm_monad_unfold.
  - ff.
  - target_break_match H0.
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    try target_break_match H3;
    match goal with
    | H1 : invoke_APPR' _ ?e _ _ _ = _,
      H2 : invoke_APPR' _ ?e _ _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; ff
    end.
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    try target_break_match H3.
    ateb_unpack Hbm3; ffa.
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    try target_break_match H3;
    match goal with
    | H1 : invoke_APPR' _ ?e _ _ _ = _,
      H2 : invoke_APPR' _ ?e _ _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; ff
    end.
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    try target_break_match H3;
    ateb_unpack Hbm0; ffa.
  - target_break_match H2;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    try target_break_match H3;
    ateb_unpack Hbm0; ffa.
  - target_break_match H0;
    repeat find_injection;
    repeat find_rewrite;
    subst; try simple congruence 3;
    eauto;
    try target_break_match H1.
    all: 
    repeat match goal with
    | H1 : invoke_APPR' _ ?e _ _ _ = _,
      H2 : invoke_APPR' _ ?e _ _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply invoke_APPR_config_immut in H1 as ?; [ | reflexivity ];
      eapply invoke_APPR_config_immut in H2 as ?; [ | reflexivity ];
      eapply IH in H1; [ | | eapply H2]; clear IH; ff
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
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; ffa using result_monad_unfold;
  try (find_eapply_lem_hyp IHe; ff; fail);
  try (find_eapply_lem_hyp IHe1; ff);
  try (find_eapply_lem_hyp IHe2; ff).
  all: try (ateb_errs_same; eauto; fail).
  all: try (ateb_diff).
  all: try ateb_same; ffa.
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

Lemma invoke_APPR'_spans : forall G' et r e' sc c i st sc' eo,
  G' = session_context sc ->
  invoke_APPR' r et eo st sc = (resultC e', c, sc') ->
  forall G,
  G = session_context sc ->
  appr_events_size G et = resultC i ->
  st_evid c = st_evid st + i.
Proof.
  intros G'.
  induction et using (Evidence_subterm_path_Ind_special G');
  ffa using (try cvm_monad_unfold; try result_monad_unfold);
  repeat match goal with
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
  all: try ateb_same; ffa.
Qed.

Inductive et_same_asps : EvidenceT -> EvidenceT -> Prop :=
| et_same_asps_mt : et_same_asps mt_evt mt_evt
| et_same_asps_nonce : forall n1 n2, et_same_asps (nonce_evt n1) (nonce_evt n2)
| et_same_asps_asp : forall p1 p2 e1 e2 aid args1 args2 targp1 targp2 targ1 targ2,
    et_same_asps e1 e2 ->
    et_same_asps 
      (asp_evt p1 (asp_paramsC aid args1 targp1 targ1) e1) 
      (asp_evt p2 (asp_paramsC aid args2 targp2 targ2) e2)
| et_same_asps_left : forall e1 e2,
    et_same_asps e1 e2 ->
    et_same_asps (left_evt e1) (left_evt e2)
| et_same_asps_right : forall e1 e2,
    et_same_asps e1 e2 ->
    et_same_asps (right_evt e1) (right_evt e2)
| et_same_asps_split : forall e1 e2 e1' e2',
    et_same_asps e1 e2 ->
    et_same_asps e1' e2' ->
    et_same_asps (split_evt e1 e1') (split_evt e2 e2').
Local Hint Constructors et_same_asps : et_same_asps_db.

Lemma et_same_asps_refl : forall e,
  et_same_asps e e.
Proof.
  induction e; eauto using et_same_asps;
  repeat match goal with
  | a : ASP_PARAMS |- _ => destruct a; eauto using et_same_asps
  end.
Qed.

Lemma et_same_asps_symm : forall e1 e2,
  et_same_asps e1 e2 -> et_same_asps e2 e1.
Proof.
  intros.
  prep_induction H.
  induction H; eauto using et_same_asps.
Qed.
Local Hint Resolve et_same_asps_symm : et_same_asps_db.

Lemma ev_subterm_path_et_same_asps : forall G e1 e2 e1' e2' l,
  et_same_asps e1 e2 ->
  Evidence_Subterm_path G e1' l e1 ->
  Evidence_Subterm_path G e2' l e2 ->
  et_same_asps e1' e2'.
Proof.
  intros.
  prep_induction H.
  induction H; intros; simpl in *;
  try (invc H0; invc H1; eauto using et_same_asps; fail).
  - invc H0; invc H1; try congruence; eauto using et_same_asps.
  - invc H0; invc H1; try congruence; eauto using et_same_asps.
  - invc H0; invc H1; try congruence; eauto using et_same_asps.
  - invc H1; invc H2; try congruence; eauto using et_same_asps.
Qed.
Local Hint Resolve ev_subterm_path_et_same_asps : et_same_asps_db.

Lemma et_same_asps_ateb_errs_det : forall {A} G (f : _ -> A) e1 e2 l r1 r2,
  et_same_asps e1 e2 ->
  apply_to_evidence_below G f l e1 = errC r1 ->
  apply_to_evidence_below G f l e2 = errC r2 ->
  r1 = r2.
Proof.
  induction e1; simpl in *; ff;
  try (invc H; simpl in *; ff; fail).
Qed.

Lemma et_same_asps_ateb_errs_only : forall {A} G (f : _ -> A) e1 e2 l r1 r2,
  et_same_asps e1 e2 ->
  apply_to_evidence_below G f l e1 = errC r1 ->
  apply_to_evidence_below G f l e2 = resultC r2 ->
  False.
Proof.
  induction e1; simpl in *; ff;
  try (invc H; simpl in *; ff; fail).
Qed.

Lemma et_same_asps_impl_same_size : forall G e1 e2,
  et_same_asps e1 e2 ->
  et_size G e1 = et_size G e2.
Proof.
  intros G.
  induction e1 using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; ff; eauto;
  try (invc H; ff; fail);
  try (invc H1; ff; result_monad_unfold; ffa; fail).
  - invc H1; ff; result_monad_unfold; ffa.
    * eapply et_same_asps_ateb_errs_det in Heqr0; ff; ff.
    * eapply et_same_asps_ateb_errs_only in Heqr0; ff; exfalso; eauto.
    * eapply et_same_asps_ateb_errs_only in Heqr0; ff; 
      try eapply et_same_asps_symm; eauto; exfalso; eauto.
    * ateb_unpack Heqr; ffa;
      ateb_unpack Heqr0; ffa;
      eapply H0; ffa;
      eapply ev_subterm_path_et_same_asps; ffa.
  - invc H0; ff; result_monad_unfold; ffa.
  - invc H0; ff; result_monad_unfold; ffa.
    * eapply et_same_asps_ateb_errs_det in Heqr0; ff; ff.
    * eapply et_same_asps_ateb_errs_only in Heqr0; ff; exfalso; eauto.
    * eapply et_same_asps_ateb_errs_only in Heqr0; ff; 
      try eapply et_same_asps_symm; eauto; exfalso; eauto.
    * ateb_unpack Heqr; ffa;
      ateb_unpack Heqr0; ffa;
      eapply H; ffa;
      eapply ev_subterm_path_et_same_asps; ffa.
  - invc H0; ff; result_monad_unfold; ffa.
    * eapply et_same_asps_ateb_errs_det in Heqr0; ff; ff.
    * eapply et_same_asps_ateb_errs_only in Heqr0; ff; exfalso; eauto.
    * eapply et_same_asps_ateb_errs_only in Heqr0; ff; 
      try eapply et_same_asps_symm; eauto; exfalso; eauto.
    * ateb_unpack Heqr; ffa;
      ateb_unpack Heqr0; ffa;
      eapply H; ffa;
      eapply ev_subterm_path_et_same_asps; ffa.
  - result_monad_unfold; ff; invc H; ffa; result_monad_unfold;
    ffa.
Qed.
Local Hint Resolve et_same_asps_impl_same_size : et_same_asps_db.

Lemma et_same_asps_asp_dir : forall e1 e2 asp_id args1 args2 targ_plc1 targ_plc2 targ1 targ2 p1 p2 par1 par2,
  et_same_asps e1 e2 ->
  par1 = (asp_paramsC asp_id args1 targ_plc1 targ1) ->
  par2 = (asp_paramsC asp_id args2 targ_plc2 targ2) ->
  et_same_asps (asp_evt p1 par1 e1) (asp_evt p2 par2 e2).
Proof.
  intros.
  prep_induction H.
  induction H; intros; subst_max; eauto using et_same_asps;
  try (econstructor; eapply et_same_asps_refl; fail).
Qed.
Local Hint Resolve et_same_asps_asp_dir : et_same_asps_db.

Lemma equiv_EvidenceT_impl_et_size_same : forall G e1 e2,
  equiv_EvidenceT G e1 e2 = true ->
  et_size G e1 = et_size G e2.
Proof.
  intros.
  unfold equiv_EvidenceT in *.
  ff; rewrite PeanoNat.Nat.eqb_eq in *; ff.
Qed.

Lemma et_same_asps_appr_procedure : forall G e1 e1' e2 e2' p1 p2 e1o e2o,
  et_same_asps e1 e2 ->
  et_same_asps e1o e2o ->
  appr_procedure' G p1 e1 e1o = resultC e1' ->
  appr_procedure' G p2 e2 e2o = resultC e2' ->
  et_same_asps e1' e2'.
Proof.
  intros G.
  induction e1 using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; cvm_monad_unfold.
  - invc H; simpl in *; ff; econstructor; eauto.
  - invc H; simpl in *; ff; econstructor; eauto.
  - inv H1; simpl in *; ff.
    * econstructor; eauto.
    * eapply IHe1 in H4; ff; econstructor; eauto.
    * result_monad_unfold; ff;
      econstructor; eauto.
      econstructor; eauto.
  - inv H1; simpl in *; ff.
    result_monad_unfold; ff.
    ateb_unpack Heqr0;
    ateb_unpack Heqr.
    eapply H0 in Hf0; try eapply Hf; ff.
    eapply ev_subterm_path_et_same_asps; ff.
  - inv H1; simpl in *; ff.
  - inv H0; simpl in *; ff;
    result_monad_unfold; ff.
    ateb_unpack Heqr0;
    ateb_unpack Heqr.
    eapply H in Hf0; try eapply Hf; ff.
    eapply ev_subterm_path_et_same_asps; ff.
  - inv H0; simpl in *; ff;
    result_monad_unfold; ff.
    ateb_unpack Heqr0;
    ateb_unpack Heqr.
    eapply H in Hf0; try eapply Hf; ff.
    eapply ev_subterm_path_et_same_asps; ff.
  - inv H; simpl in *; ff;
    result_monad_unfold; ff.
    eapply IHe1_1 in Heqr; try eapply Heqr1; eauto;
    try (econstructor; eauto; fail).
    eapply IHe1_2 in Heqr0; try eapply Heqr2; eauto;
    try (econstructor; eauto; fail).
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
  intros G.
  induction e1 using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; result_monad_unfold; ff;
  try (invc H; ff; fail);
  try (invc H1; ffa using result_monad_unfold; fail).
  - invc H1; ff; result_monad_unfold; ff;
    ateb_unpack Heqr; ateb_unpack Heqr0.
    eapply H0; ff; eapply ev_subterm_path_et_same_asps; eauto.
  - invc H0; ff; result_monad_unfold; ff;
    ateb_unpack Heqr; ateb_unpack Heqr0.
    eapply H; ff; eapply ev_subterm_path_et_same_asps; eauto.
  - invc H0; ff; result_monad_unfold; ff;
    ateb_unpack Heqr; ateb_unpack Heqr0.
    eapply H; ff; eapply ev_subterm_path_et_same_asps; eauto.
  - invc H; simpl in *; result_monad_unfold; ff.
    eapply IHe1_1 in Heqr1; try reflexivity; subst; ff.
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

Require Import EqClass.

Fixpoint eqb_asp_args `{EqClass string, EqClass bool} (js1 js2:ASP_ARGS) : bool := 
  match js1, js2 with
  | JSON_Object m1, JSON_Object m2 => map_eqb_eqb eqb_asp_args m1 m2
  | JSON_Array ls1, JSON_Array ls2 => list_eqb_eqb eqb_asp_args ls1 ls2
  | JSON_String s1, JSON_String s2 => eqb s1 s2
  | JSON_Boolean b1, JSON_Boolean b2 => eqb b1 b2
  | _, _ => false
  end.

Theorem eqb_json_eq : forall `{EqClass string, EqClass bool} js1 js2, 
eqb_asp_args js1 js2 = true <-> js1 = js2.
Proof.
  induction js1 using JSON_ind_better;
  destruct js2; simpl in *; try (split; intros; congruence).
  - erewrite map_eqb_eq; eauto; split; intros; subst; try congruence.
  - erewrite list_eqb_eq; eauto; split; intros; congruence.
  - rewrite eqb_eq; intuition; subst; eauto; inversion H1; eauto.
  - rewrite eqb_eq; intuition; subst; eauto; inversion H1; eauto.
Qed.

Global Instance EqClass_ASP_ARGS `{EqClass string, EqClass bool} : EqClass ASP_ARGS := 
{
  eqb := eqb_asp_args;
  eqb_eq := eqb_json_eq;
}.

Lemma eqb_ASP_PARAMS_eq `{EqClass ASP_ARGS} : forall a1 a2,
  eqb_ASP_PARAMS a1 a2 = true <-> a1 = a2.
Proof.
  induction a1; destruct a2; ff;
  repeat rewrite Bool.andb_true_iff in *; ff;
  repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
  repeat rewrite String.eqb_eq in *; ff;
  repeat rewrite EqClass.general_list_eqb_eq in *; ff.

  destruct H.
  apply eqb_eq in H3.
  subst.
  ff.
  rewrite eqb_eq in *.
  ff.
Qed.

Lemma eqb_EvidenceT_eq `{EqClass ASP_PARAMS} : forall e1 e2,
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
  rewrite eqb_eq in *.
  ff.
  rewrite eqb_eq in *.
  ff.
Qed.

Lemma invoke_ASP_evidence : forall e par st sc e' st' sc',
  invoke_ASP e par st sc = (resultC e', st', sc') ->
  get_et e' = asp_evt (session_plc sc) par (get_et e).
Proof.
  cvm_monad_unfold; ff.
Qed.

(* Lemma split_evidence_res_spec : forall e st st' et1 et2 e1 e2 sc sc',
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
Qed. *)

Theorem invoke_APPR'_evidence : forall G et st r sc sc' st' e' e eo,
  G = session_context sc ->
  invoke_APPR' r et eo st sc = (resultC e', st', sc') ->
  appr_procedure' (session_context sc) (session_plc sc) et eo = resultC e ->
  get_et e' = e.
Proof.
  intros G.
  induction et using (Evidence_subterm_path_Ind_special G);
  intuition; simpl in *.
  - simpl in *; cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; result_monad_unfold; ff;
    cvm_monad_unfold; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff.
    * find_eapply_lem_hyp IHet; ff; simpl in *; ff.
    * find_eapply_lem_hyp IHet; ff; simpl in *; ff.
    * find_eapply_lem_hyp IHet; ff; simpl in *; ff.
    * find_eapply_lem_hyp IHet; ff; simpl in *; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; result_monad_unfold; ff;
    cvm_monad_unfold; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff.
    ateb_same.
    find_eapply_lem_hyp H0; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; result_monad_unfold; ff;
    cvm_monad_unfold; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; result_monad_unfold; ff;
    cvm_monad_unfold; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    ateb_same; find_eapply_lem_hyp H; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; result_monad_unfold; ff;
    cvm_monad_unfold; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    ateb_same; find_eapply_lem_hyp H; ff.
  - cvm_monad_unfold; ff; cvm_monad_unfold; result_monad_unfold; ff;
    cvm_monad_unfold; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ffa.
    
    repeat match goal with
    | H1 : invoke_APPR' _ ?e ?o _ _ = _,
      H2 : appr_procedure' _ _ ?e ?o = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply invoke_APPR_config_immut in H1 as ?; try reflexivity;
      eapply IH in H1; [ | | eapply H2 ]; ff
      (* eapply IH in H1; [ | | eapply H2 ]; ff *)
    end.
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

(* Lemma wf_Evidence_split_evidence : forall e et1 et2 st st' G r1 r2 sc sc',
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
Qed. *)

Fixpoint meta_machinery_pad_n (n : nat) (e : RawEv) : RawEv :=
  match n with
  | 0 => e
  | S n' => passed_bs :: meta_machinery_pad_n n' e
  end.

Lemma meta_machinery_pad_n_size : forall n e,
  List.length (meta_machinery_pad_n n e) = n + List.length e.
Proof.
  induction n; ff.
Qed.

Lemma wf_Evidence_exists : forall G e n,
  et_size G e = resultC n ->
  exists r, wf_Evidence G (evc r e).
Proof.
  intros G; induction e using (Evidence_subterm_path_Ind_special G); ff;
  try (exists (meta_machinery_pad_n n nil); econstructor; eauto;
    result_monad_unfold; ff; 
    rewrite meta_machinery_pad_n_size; ff; fail).
  - eexists; eapply wf_Evidence_mt_evc. 
  - exists [passed_bs]; econstructor; eauto.
Qed.

(* Lemma wf_Evidence_asp_unfold : forall G r p ps e,
  wf_Evidence G (evc r (asp_evt p ps e)) ->
  exists r', wf_Evidence G (evc r' e).
Proof.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G);
  intros; try (invc H); simpl in *; ff;
  try (exists nil; econstructor; simpl in *; eauto; fail);
  try (exists [passed_bs]; econstructor; simpl in *; eauto; fail).
  - 
  try (eexists; econstructor; ff).
  prep_induction H.
  induction H; ff; result_monad_unfold; ff.
  eapply wf_Evidence_exists.
  eapply wf_Evidence_exists; ff.
Qed. *)

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
  List.length r = n + n'.
Proof.
  intros.
  prep_induction H; ff; invc H; ff.
Qed.

(* Lemma wf_Evidence_invoke_ASP : forall G ps st e e' st' sc sc',
  G = session_context sc ->
  wf_Evidence (session_context sc) e ->
  invoke_ASP e ps st sc = (resultC e', st', sc') ->
  wf_Evidence (session_context sc) e'.
Proof.
  destruct e.
  generalizeEverythingElse e.
  intros G.
  induction e using (Evidence_subterm_path_Ind_special G);
  intros; simpl in *; destruct e'; simpl in *; cvm_monad_unfold.
  - ff; repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    econstructor; simpl in *; ff;
    invc H0; simpl in *; ff;
    rewrite app_length; ff.
  - ff; repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    econstructor; simpl in *; ff;
    invc H0; simpl in *; ff;
    rewrite app_length; ff.
  - ff; repeat rewrite PeanoNat.Nat.eqb_eq in *; ff.
    * econstructor; ff.
    * econstructor; ff.
    * econstructor; ff; repeat rewrite app_length in *; ff; invc H2; ff.
    * econstructor; ff; repeat rewrite app_length in *; ff; invc H2; ff;
      result_monad_unfold; ff.
      ** destruct e; simpl in *; ff.
      ** repeat find_eapply_lem_hyp apply_to_evidence_below_nil; ffa;
        unfold id in *; ff;
        rewrite String.eqb_eq in *; ff.
        admit.
        admit.
  - ff; repeat rewrite PeanoNat.Nat.eqb_eq in *; ff.
    * econstructor; ff.
    * econstructor; ff.
    * econstructor; ff; repeat rewrite app_length in *; ff; invc H2; ff.
    * econstructor; ff; repeat rewrite app_length in *; ff; invc H2; ff;
      result_monad_unfold; ff.
      ** destruct e; simpl in *; ff.
      ** repeat find_eapply_lem_hyp apply_to_evidence_below_nil; ffa;
        unfold id in *; ff;
        rewrite String.eqb_eq in *; ff.
        admit.
        admit.
  - 

    econstructor; simpl in *; ff;
    invc H0; simpl in *; ff;
    rewrite app_length; ff.
  - 
    * econstructor; simpl in *; ff.
  - invc H0; simpl in *.
    destruct e'.
    econstructor; cvm_monad_unfold; ff.
    econstructor; ff.
    eapply wf_Evidence_c.
    econstructor.


  destruct st; simpl in *; ff.
  prep_induction H.
  induction H; cvm_monad_unfold; ff;
  econstructor; ff;
  rewrite PeanoNat.Nat.eqb_eq in *; ff;
  try rewrite app_length in *; ff.

  result_monad_unfold; ffa.
  - ateb_diff.
  - eapply apply_to_evidence_below_res_spec in Heqr2 as ?; ff.
    ateb_same; unfold id in *; ff.
    * eapply Evidence_Subterm_path_same in H; try eapply Hesp0; subst;
      simpl in *; ff.
      admit.
    * eapply Evidence_Subterm_path_same in H; try eapply Hesp0; subst;
      simpl in *; ff.
    eapply apply_to_evidence_below_res_spec in Heqr0.
Qed. *)

(* 
Lemma et_size_invoke_APPR : forall e st e' st' n,
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
    econstructor; ff; result_monad_unfold; repeat rewrite app_length; ff;
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

Lemma wf_Evidence_invoke_APPR : forall G et r eo st e' st' sc sc',
  G = session_context sc ->
  wf_Evidence (session_context sc) (evc r et) ->
  wf_Evidence (session_context sc) (evc r eo) ->
  invoke_APPR' r et eo st sc = (resultC e', st', sc') ->
  wf_Evidence (session_context sc) e'.
Proof.
  intros G.
  induction et using (Evidence_subterm_path_Ind_special G); intuition.
  - ff; cvm_monad_unfold; ff; eapply wf_Evidence_mt_evc.
  - ff; cvm_monad_unfold; ff;
    rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat match goal with
    | H : wf_Evidence _ _ |- _ => invc H; ff
    end; try (econstructor; ff; repeat rewrite app_length; ff;
    result_monad_unfold; ff; try ateb_diff; fail).

  - simpl in *; result_monad_unfold; cvm_monad_unfold; ff;
    rewrite PeanoNat.Nat.eqb_eq in *; ff.
    all: try (repeat match goal with
      | H : wf_Evidence _ _ |- _ => invc H; ff
      end; econstructor; ff; result_monad_unfold; repeat rewrite app_length in *; ff; fail).
    all: try (result_monad_unfold; ff; eapply IHet in H1; eauto; econstructor; 
      repeat rewrite app_length in *; ff;
      repeat match goal with
      | H : wf_Evidence _ _ |- _ => invc H; ff
      end; fail).
    all: try (find_eapply_lem_hyp peel_n_rawev_result_spec; ff);
      result_monad_unfold;
      try (find_eapply_lem_hyp IHet; ff);
      econstructor; repeat rewrite app_length in *; ff;
      result_monad_unfold; ff;
      repeat match goal with
      | H : wf_Evidence _ _ |- _ => invc H; 
        result_monad_unfold; ff
      end; result_monad_unfold; ff;
      repeat rewrite app_length in *; ff;
      f_equal; try lia.
  - repeat cvm_monad_unfold; ff.
    ateb_unpack Heqr0; ff.
    eapply H0 in H4; ff.
    invc H2; ff; result_monad_unfold; ff;
    ateb_unpack Heqr0.
    eapply Evidence_Subterm_path_same in Hesp; try eapply Hesp0;
    ff; econstructor; ff.
  - repeat cvm_monad_unfold; ff.
  - repeat cvm_monad_unfold; ff.
    ateb_unpack Heqr0; ffa.
    eapply H in H3; ff.
    invc H1; simpl in *; result_monad_unfold; ff;
    ateb_unpack Heqr0.
    eapply Evidence_Subterm_path_same in Hesp;
    try eapply Hesp0; subst.
    econstructor; ff.
  - repeat cvm_monad_unfold; ff.
    ateb_unpack Heqr0; ffa.
    eapply H in H3; ff.
    invc H1; simpl in *; result_monad_unfold; ff;
    ateb_unpack Heqr0.
    eapply Evidence_Subterm_path_same in Hesp;
    try eapply Hesp0; subst.
    econstructor; ff.
  - simpl in *; ff; cvm_monad_unfold; ff.
    (* unfold split_evidence in *; cvm_monad_unfold; ff; *)
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    repeat rewrite eqb_EvidenceT_eq in *; ff;
    repeat rewrite app_nil_r in *; ff.
    eapply invoke_APPR_config_immut in Heqp1 as ?; ff.
    eapply invoke_APPR_config_immut in Heqp2 as ?; ff.
    eapply IHet1 in Heqp1; try reflexivity.
    * eapply IHet2 in Heqp2; try reflexivity;
      econstructor; repeat rewrite app_length in *; ff;
      result_monad_unfold; ff;
      repeat match goal with
      | H : wf_Evidence _ _ |- _ => invc H; ff
      end; result_monad_unfold; ff;
      repeat rewrite app_length in *; ff;
      repeat find_eapply_lem_hyp equiv_EvidenceT_impl_et_size_same; ff.
    * econstructor; repeat rewrite app_length in *; ff;
      result_monad_unfold; ff;
      repeat match goal with
      | H : wf_Evidence _ _ |- _ => invc H; ff
      end; result_monad_unfold; ff;
      repeat rewrite app_length in *; ff;
      repeat find_eapply_lem_hyp equiv_EvidenceT_impl_et_size_same; ff.
    * econstructor; repeat rewrite app_length in *; ff;
      result_monad_unfold; ff;
      repeat match goal with
      | H : wf_Evidence _ _ |- _ => invc H; ff
      end; result_monad_unfold; ff;
      repeat rewrite app_length in *; ff;
      repeat find_eapply_lem_hyp equiv_EvidenceT_impl_et_size_same; ff. 
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
      repeat rewrite app_length;
      f_equal; lia).
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

Theorem invoke_APPR_respects_events : forall G et r eo st sc st' sc' e' i m evs,
  G = session_context sc ->
  well_formed_context (session_context sc) ->
  st_evid st = i ->
  st_trace st = m ->
  invoke_APPR' r et eo st sc = (resultC e', st', sc') ->
  appr_events' (session_context sc) (session_plc sc) et eo i = resultC evs ->
  st_trace st' = m ++ evs.
Proof.
  intros G.
  induction et using (Evidence_subterm_path_Ind_special G);
  simpl in *; intros; cvm_monad_unfold.
  - ff; rewrite app_nil_r; ff.
  - ff. 
  - ff; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    try (match goal with
    | H : invoke_APPR' _ ?e _ _ _ = _,
      H2 : appr_events' _ _ ?e _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply invoke_APPR'_spans in H as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff;
      eapply invoke_APPR_config_immut in H as ?; ff;
      eapply IH in H; [ | | | | | eapply H2 ]; 
      simpl in *; try reflexivity; try lia; ff
    end; 
    assert (st_evid st + 1 + 1 = st_evid st + 2) by lia; ff;
    repeat rewrite <- app_assoc; ff).
  - ff; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    try (match goal with
    | H : invoke_APPR' _ ?e _ _ _ = _,
      H2 : appr_events' _ _ ?e _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply invoke_APPR'_spans in H as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff;
      eapply invoke_APPR_config_immut in H as ?; ff;
      eapply IH in H; [ | | | | | eapply H2 ]; 
      simpl in *; try reflexivity; try lia; ff
    end; 
    assert (st_evid st + 1 + 1 = st_evid st + 2) by lia; ff;
    repeat rewrite <- app_assoc; ff).
    ateb_same; ffa.
  - ff; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    try (match goal with
    | H : invoke_APPR' _ ?e _ _ _ = _,
      H2 : appr_events' _ _ ?e _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply invoke_APPR'_spans in H as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff;
      eapply invoke_APPR_config_immut in H as ?; ff;
      eapply IH in H; [ | | | | | eapply H2 ]; 
      simpl in *; try reflexivity; try lia; ff
    end; 
    assert (st_evid st + 1 + 1 = st_evid st + 2) by lia; ff;
    repeat rewrite <- app_assoc; ff).
  - ff; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    try (match goal with
    | H : invoke_APPR' _ ?e _ _ _ = _,
      H2 : appr_events' _ _ ?e _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply invoke_APPR'_spans in H as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff;
      eapply invoke_APPR_config_immut in H as ?; ff;
      eapply IH in H; [ | | | | | eapply H2 ]; 
      simpl in *; try reflexivity; try lia; ff
    end; 
    assert (st_evid st + 1 + 1 = st_evid st + 2) by lia; ff;
    repeat rewrite <- app_assoc; ff);
    ateb_same; ffa.
  - ff; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff;
    try (match goal with
    | H : invoke_APPR' _ ?e _ _ _ = _,
      H2 : appr_events' _ _ ?e _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply invoke_APPR'_spans in H as ?; try reflexivity; ff;
      try (eapply appr_events'_size_works; eauto; ff); ff;
      eapply invoke_APPR_config_immut in H as ?; ff;
      eapply IH in H; [ | | | | | eapply H2 ]; 
      simpl in *; try reflexivity; try lia; ff
    end; 
    assert (st_evid st + 1 + 1 = st_evid st + 2) by lia; ff;
    repeat rewrite <- app_assoc; ff);
    ateb_same; ffa.
  - ff; result_monad_unfold; ff;
    repeat rewrite PeanoNat.Nat.eqb_eq in *; ff;
    repeat find_eapply_lem_hyp peel_n_rawev_result_spec; ff.

    repeat match goal with
    | H : invoke_APPR' _ ?e _ _ _ = _,
      H2 : appr_events' _ _ ?e _ _ = _,
      IH : context[invoke_APPR' _ ?e _ _ _ = _ -> _] |- _ =>
      eapply invoke_APPR'_spans in H as ?; try reflexivity; 
      try (eapply appr_events'_size_works; eauto; ff); ff;
      eapply invoke_APPR_config_immut in H as ?; ff; [ ];
      eapply IH in H; [ | | | | | eapply H2 ];
      simpl in *; try reflexivity; try lia; ff
    end;
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
    assert (List.length rem_evs = n) by (
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
    assert (st_evid st + 2 + List.length evs1 = st_evid st + 1 + 1 + List.length evs1) by lia.
    ff.
    repeat find_rewrite_lem events_events_fix_eq; ff.
    assert (n = List.length evs2) by (
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

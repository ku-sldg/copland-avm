(*
Helper lemmas for proofs about the CVM semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Cvm_Monad Cvm_Impl Term_Defs Auto Attestation_Session StructTactics AutoApp.
Require Import Coq.Program.Tactics.

Import ListNotations.

Lemma sc_immut_split_evidence : forall r et1 et2 st res st',
  split_evidence r et1 et2 st = (res, st') ->
  st_config st = st_config st'.
Proof.

Lemma sc_immut_invoke_APPR : forall et st r st',
  invoke_APPR et st = (r, st') ->
  st_config st = st_config st'.
Proof.
  induction et; simpl in *; intuition; ffa using cvm_monad_unfold.
  unfold split_evidence in *; ffa using cvm_monad_unfold.

Lemma sc_immut_better : forall t st r st',
  build_cvm t st = (r, st') ->
  st_config st = st_config st'.
Proof.
  induction t; repeat (cvm_monad_unfold; simpl in *); intuition;
  ffa using cvm_monad_unfold.
  - fold invoke_APPR.
    simpl in *.
    destruct st_ev; simpl in *; destruct e; ff;
    unfold split_evidence in *; cvm_monad_unfold; ff;
    unfold peel_n_rawev in *; cvm_monad_unfold; ff.
Qed.

(* Hack to apply a specific induction hypothesis in some proofs *)
Ltac anhl :=
  annogo;
  match goal with
  | [H2: build_cvm ?a _ = _,
     H3: build_cvm ?a _ = _,
     IH: context[ _ -> _] |- _] =>
    edestruct IH;
    [ apply H2 | apply H3 | idtac]; clear H2; clear H3;
    destruct_conjs; subst
  end.

Ltac monad_simp := 
  repeat (cvm_monad_unfold; simpl in *; eauto).

Lemma check_cvm_policy_preserves_state : forall t p evt st1 st1' r,
  check_cvm_policy t p evt st1 = (r, st1') ->
  st1 = st1'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using cvm_monad_unfold.
Qed.
Global Hint Resolve check_cvm_policy_preserves_state : core.

(* Lemma policy_list_not_disclosed_same_outputs : forall a p evt pol1 pol2 r1 r2,
  policy_list_not_disclosed a p evt pol1 = r1 ->
  policy_list_not_disclosed a p evt pol2 = r2 ->
  r1 = r2.
Proof.
  induction pol1; intuition; eauto; simpl in *; subst.
  - induction pol2; simpl in *; intuition; eauto;
    right; intros HC; invc HC. 
  - induction pol2; simpl in *; intuition; eauto;
    try (right; intros HC; invc HC; congruence).
    * repeat find_rewrite; simpl in *;
      destEq a1 a2; try (right; intros HC; invc HC; congruence).
      destEq b b0; try (right; intros HC; invc HC; congruence).
      destruct (term_discloses_aspid_to_remote_enc_bool a p evt a2 b0) eqn:E;
      simpl in *; intuition; eauto.
    * repeat find_rewrite; simpl in *;
      destEq a1 a2; try (right; intros HC; invc HC; congruence).
      destEq b b0; try (right; intros HC; invc HC; congruence).
      destruct (term_discloses_aspid_to_remote_enc_bool a p evt a2 b0) eqn:E;
      simpl in *; intuition; eauto.
      destruct (policy_list_not_disclosed a p evt pol1) eqn:E1,
        (policy_list_not_disclosed a p evt pol2) eqn:E2;
      intuition; eauto.
      ** eapply  
      intuition; eauto.
    *  
  simpl in *; subst; eauto.
  destruct pol2; simpl  *)

Lemma check_cvm_policy_same_outputs : forall t p evt st1 st1' r1 st2 st2' r2,
  check_cvm_policy t p evt st1 = (r1, st1') ->
  check_cvm_policy t p evt st2 = (r2, st2') ->
  (policy (st_config st1) = policy (st_config st2)) ->
  r1 = r2 /\ st1 = st1' /\ st2 = st2'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using cvm_monad_unfold.
Qed.
Global Hint Resolve check_cvm_policy_same_outputs : core.

Theorem EvidenceT_deterministic_output_on_results : forall t e tr1 tr2 i1 i2 ac st1 st2,
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
Qed.

Lemma cvm_errors_deterministic :  forall t e tr1 tr2 i ac r1 r2 st1 st2,
  build_cvm t
    {|
      st_ev := e;
      st_trace := tr1;
      st_evid := i;
      st_config := ac
    |} =
  (r1, st1) -> 

  build_cvm t
    {|
      st_ev := e;
      st_trace := tr2;
      st_evid := i;
      st_config := ac
    |} =
  (r2, st2) -> 

  (r1 = r2 /\ st1.(st_ev) = st2.(st_ev) /\ st1.(st_config) = st2.(st_config) /\
    st1.(st_evid) = st2.(st_evid)).
Proof.
  induction t; intros; monad_simp.
  - ffa.
  - ffa using cvm_monad_unfold.

  - ff; eauto;
    repeat match goal with
    | x : cvm_st |- _ => destruct x
    | H1 : build_cvm t1 _ = (_, _), H2 : build_cvm t1 _ = (_, _) |- _ =>
      eapply IHt1 in H1; eauto; simpl in *; intuition; subst; try congruence; eauto
    | H1 : build_cvm t2 _ = (_, _), H2 : build_cvm t2 _ = (_, _) |- _ =>
      eapply IHt2 in H1; eauto; simpl in *; intuition; subst; try congruence; eauto
    end.
  - ff; eauto;
    repeat match goal with
    | x : cvm_st |- _ => destruct x
    | H1 : build_cvm t1 _ = (_, _), H2 : build_cvm t1 _ = (_, _) |- _ =>
      eapply IHt1 in H1; eauto; simpl in *; intuition; subst; try congruence; eauto
    | H1 : build_cvm t2 _ = (_, _), H2 : build_cvm t2 _ = (_, _) |- _ =>
      eapply IHt2 in H1; eauto; simpl in *; intuition; subst; try congruence; eauto
    end.
  - ff; eauto;
    repeat match goal with
    | x : cvm_st |- _ => destruct x
    | H1 : build_cvm t1 _ = (_, _), H2 : build_cvm t1 _ = (_, _) |- _ =>
      eapply IHt1 in H1; eauto; simpl in *; intuition; subst; try congruence; eauto
    | H1 : build_cvm t2 _ = (_, _), H2 : build_cvm t2 _ = (_, _) |- _ =>
      eapply IHt2 in H1; eauto; simpl in *; intuition; subst; try congruence; eauto
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
  intros; find_eapply_lem_hyp cvm_errors_deterministic; 
  [ | eapply H]; intuition; simpl in *; eauto.
Qed.


Ltac dohi'' :=
  annogo;
  let tac H H' := eapply st_trace_irrel; [apply H | apply H'] in
  match goal with
  | [H : build_cvm ?t1 {| st_ev := ?e; st_trace := _; st_evid := ?i; st_config := ?ac |} =
         (?opt, {| st_ev := ?e'; st_trace := _; st_evid := ?i'; st_config := ?ac' |}),
         H' : build_cvm ?t1 {| st_ev := ?e; st_trace := _; st_evid := ?i; st_config := ?ac |} =
              (?opt, {| st_ev := ?e''; st_trace := _; st_evid := ?i''; st_config := ?ac'' |})
     |- _] =>
    assert_new_proof_by (e' = e'' /\ i' = i'' /\ ac' = ac'') ltac:(tac H H')
  end.

Ltac dohi :=
  do 2 (repeat dohi''; destruct_conjs; subst);
  repeat clear_triv.

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

Inductive build_cvmP :
  Core_Term -> cvm_st -> (ResultT unit CVM_Error) -> cvm_st ->  Prop :=
| ccp: forall t st st' res,
    build_cvm t st = (res, st') ->
    build_cvmP t st res st'.

Lemma ccp_implies_cc: forall t st st' res,
  build_cvmP t st res st' ->
  build_cvm t st = (res,st').
Proof.
  intros.
  solve_by_inversion.
Qed.

Lemma cc_implies_ccp: forall t st st' res,
  build_cvm t st = (res,st') -> 
  build_cvmP t st res st'.
Proof.
  intros.
  econstructor.
  tauto.
Qed.

Lemma ccp_iff_cc: forall t st st' res,
  build_cvm t st = (res,st') <-> 
  build_cvmP t st res st'.
Proof.
  intros.
  split; intros;
    try (eapply cc_implies_ccp; eauto);
    try (eapply ccp_implies_cc; eauto).
Qed.

Ltac inv_term_coreP :=
  match goal with
  | [H: term_to_coreP _ _ (* ?t (?c _) *)
     |- _ ] =>
    inversion H; subst
  end.

Lemma term_to_coreP_redo: forall t t',
    copland_compile t = t' ->
    term_to_coreP t t'.
Proof.
  intros.
  econstructor.
  eauto.
Qed.

Ltac do_term_to_core_redo :=
  match goal with
  | [H: copland_compile ?t = ?t'
     |- _ ] =>
    eapply term_to_coreP_redo in H
  end.

Lemma annoP_redo: forall t annt n n',
    anno t n = (n', annt) ->
    (exists n n', anno t n = (n',annt)).
Proof.
  intros.
  econstructor.
  eexists.
  jkjke.
Qed.

Ltac do_anno_redo :=
  match goal with
  | [H: anno ?t ?n = (_,?annt)
     |- _ ] =>
    eapply annoP_redo in H
  end.

Ltac inv_annoP :=
  match goal with
  | [H: (exists n n', anno _ n = (n',_)) (*_ (?c _) *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Lemma annoP_indexed_redo: forall t annt n n',
    anno t n = (n', annt) ->
    anno t n = (n', annt).
Proof.
  intros.
  econstructor.
  jkjke.
Qed.

Ltac do_anno_indexed_redo :=
  match goal with
  | [H: anno _ _ = (_,_)
     |- _ ] =>
    eapply annoP_indexed_redo in H
  end.

Ltac inv_annoP_indexed :=
  match goal with
  | [H: annoP_indexed _ _ _ _(*_ (?c _) _*)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Ltac wrap_annopar :=
  inv_term_coreP;
  dd;
  repeat do_term_to_core_redo.

Ltac wrap_anno :=
  inv_annoP;
  dd;
  repeat do_anno_redo.

Ltac wrap_anno_indexed :=
  inv_annoP_indexed;
  dd;
  repeat do_anno_indexed_redo.

Ltac wrap_ccp :=
  
  try rewrite <- ccp_iff_cc in *;
  dd;
  try rewrite ccp_iff_cc in *.

Ltac wrap_ccp_anno :=
  
  try rewrite <- ccp_iff_cc in *;
  try wrap_annopar;
  try wrap_anno;
  try wrap_anno_indexed;
  cvm_monad_unfold;
  dd;
  try rewrite ccp_iff_cc in *.

Ltac cumul_ih :=
  match goal with
  | [H: context[(st_trace _ = _ ++ st_trace _)],
        H': build_cvmP ?t1 {| st_ev := _; st_trace := ?m ++ ?k; st_evid := _; st_config := _ |}
                             (?res)
                             ?v_full,
            H'': build_cvmP ?t1 {| st_ev := _; st_trace := ?k; st_evid := _; st_config := _ |}
                                  (?res)
                                  ?v_suffix
     |- _] =>
    assert_new_proof_by (st_trace v_full = m ++ st_trace v_suffix) eauto
  end.

Ltac wrap_ccp_dohi :=
  rewrite <- ccp_iff_cc in *;
  dd;
  dohi;
  rewrite ccp_iff_cc in *.

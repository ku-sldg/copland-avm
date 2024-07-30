(*
Helper lemmas for proofs about the CVM semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Anno_Term_Defs Cvm_Monad Cvm_Impl Term_Defs Auto StructTactics AutoApp Attestation_Session ResultT.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Lemma sc_immut : forall t e tr i ac,
  st_config 
    (execErr 
      (build_cvm t)
      {|
        st_ev := e;
        st_trace := tr;
        st_evid := i;
        st_config := ac
      |}) = ac.
Proof.
  induction t; repeat (monad_unfold; simpl in *); intuition.
  - destruct a; monad_unfold; eauto;
    destruct (aspCb ac a (get_bits e)) eqn:E1; simpl in *; eauto.
    repeat ff.

  - (* at case *)
    repeat ff;
    unfold doRemote_session' in *;
    repeat ff.

  - pose proof (IHt1 e tr i ac).
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr; st_evid := i; st_config := ac |}) eqn:C1;
    simpl in *; eauto;
    destruct r; simpl in *; intuition; eauto.
    destruct c; simpl in *.
    pose proof (IHt2 st_ev st_trace st_evid st_config).
    destruct (build_cvm t2 {| st_ev := st_ev; st_trace := st_trace; st_evid := st_evid; st_config := st_config |}) eqn:C2;
    simpl in *; subst; eauto.
  - 
    monad_unfold; simpl in *.
    pose proof (IHt1 e (tr ++ [Term_Defs.split i (session_plc ac)]) (i + 1) ac).
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr ++ [Term_Defs.split i (session_plc ac) ]; st_evid := (i + 1); st_config := ac |}) eqn:C1;
    simpl in *; eauto;
    destruct r; simpl in *; intuition; eauto.
    destruct c; simpl in *.
    pose proof (IHt2 e st_trace st_evid st_config).
    destruct (build_cvm t2 {| st_ev := e; st_trace := st_trace; st_evid := st_evid; st_config := st_config |}) eqn:C2;
    simpl in *; subst; eauto;
    destruct r; simpl in *; eauto.
  - monad_unfold; simpl in *.
    pose proof (IHt1 e ((tr ++ [Term_Defs.split i (session_plc ac)]) ++ [cvm_thread_start l (session_plc ac) t2 (get_et e)]) (i + 1) ac).
    destruct (build_cvm t1 {| st_ev := e; st_trace := (tr ++ [Term_Defs.split i (session_plc ac)]) ++ [cvm_thread_start l (session_plc ac) t2 (get_et e)]; st_evid := (i + 1); st_config := ac |}) eqn:C1;
    simpl in *; eauto;
    destruct r; simpl in *; intuition; eauto.
Qed.

Lemma sc_immut_better : forall t st r st',
  build_cvm t st = (r, st') ->
  st_config st = st_config st'.
Proof.
  intuition.
  pose proof (sc_immut t (st_ev st) (st_trace st) (st_evid st) (st_config st)).
  unfold execErr in *.
  simpl in *.
  destruct st; simpl in *.
  find_rewrite; simpl in *; eauto.
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
  repeat (monad_unfold; simpl in *; eauto).

Lemma check_cvm_policy_preserves_state : forall t p evt st1 st1' r,
  check_cvm_policy t p evt st1 = (r, st1') ->
  st1 = st1'.
Proof.
  induction t; simpl in *; intuition; eauto; ff;
  break_match; repeat find_injection; eauto.
Qed.
Global Hint Resolve check_cvm_policy_preserves_state : core.

Require Import EqClass.

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
  induction t; simpl in *; intuition; eauto;
  unfold check_cvm_policy in *; monad_simp; eauto;
  repeat (break_match; repeat find_rewrite; repeat find_injection; 
    simpl in *; eauto).
Qed.
Global Hint Resolve check_cvm_policy_same_outputs : core.

Theorem evidence_deterministic_output_on_results : forall t e tr1 tr2 i1 i2 ac st1 st2,
  build_cvm t {| st_ev := e; st_trace := tr1; st_evid := i1; st_config := ac |} = (resultC tt, st1) ->
  build_cvm t {| st_ev := e; st_trace := tr2; st_evid := i2; st_config := ac |} = (resultC tt, st2) ->
  st1.(st_ev) = st2.(st_ev).
Proof.
  induction t; intros; monad_simp.
  - destruct a; monad_simp; invc H; invc H0; eauto;
    destruct (aspCb ac a (get_bits e)); 
    simpl in *; invc H1; invc H2; eauto.
    repeat ff.
  - ff;
    unfold doRemote_session' in *;
    repeat (break_match; try monad_unfold; repeat find_rewrite; repeat find_injection; try congruence; eauto);
    repeat find_eapply_lem_hyp check_cvm_policy_preserves_state;
    subst; simpl in *; repeat find_rewrite; repeat find_injection; eauto.
  - destruct (build_cvm t1 {| st_ev := e; st_trace := tr1; st_evid := i1; st_config := ac |}) eqn:E1;
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr2; st_evid := i2; st_config := ac |}) eqn:E2;
    destruct r, r0; invc H; invc H0; destruct u, u0, c, c0.
    pose proof (IHt1 _ _ _ _ _ _ _ _ E1 E2); simpl in *; subst.
    assert (st_config = st_config0). {
      pose proof (sc_immut t1 e tr2 i2 ac); monad_unfold;
      pose proof (sc_immut t1 e tr1 i1 ac); monad_unfold.
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    subst; clear E1 E2.
    destruct (build_cvm t2 {| st_ev := st_ev0; st_trace := st_trace; st_evid := st_evid; st_config := st_config0 |}) eqn:E1;
    destruct (build_cvm t2 {| st_ev := st_ev0; st_trace := st_trace0; st_evid := st_evid0; st_config := st_config0 |}) eqn:E2;
    invc H1; invc H2; simpl in *; eauto.
  - destruct (build_cvm t1 {| st_ev := e; st_trace := tr1 ++ [Term_Defs.split i1 (session_plc ac)]; st_evid := i1 + 1; st_config := ac |}) eqn:E1;
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr2 ++ [Term_Defs.split i2 (session_plc ac)]; st_evid := i2 + 1; st_config := ac |}) eqn:E2;
    destruct r, r0; invc H; invc H0; destruct u, u0, c, c0.
    pose proof (IHt1 _ _ _ _ _ _ _ _ E1 E2); simpl in *; subst.
    assert (st_config = st_config0). {
      pose proof (sc_immut t1 e (tr2 ++ [Term_Defs.split i2 (session_plc ac)]) (i2 + 1) ac); monad_unfold;
      pose proof (sc_immut t1 e (tr1 ++ [Term_Defs.split i1 (session_plc ac)]) (i1 + 1) ac); monad_unfold;
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    subst; clear E1 E2.
    destruct (build_cvm t2 {| st_ev := e; st_trace := st_trace; st_evid := st_evid; st_config := st_config0 |}) eqn:E1;
    destruct (build_cvm t2 {| st_ev := e; st_trace := st_trace0; st_evid := st_evid0; st_config := st_config0 |}) eqn:E2;
    destruct r0, r;
    invc H1; invc H2; simpl in *;
    destruct u, u0.
    pose proof (IHt2 _ _ _ _ _ _ _ _ E1 E2); simpl in *; subst; 
    rewrite H; eauto.
  - destruct (build_cvm t1 {| st_ev := e; st_trace := (tr1 ++ [Term_Defs.split i1 (session_plc ac)]) ++ [cvm_thread_start l (session_plc ac) t2 (get_et e)]; st_evid := i1 + 1; st_config := ac |}) eqn:E1;
    destruct (build_cvm t1 {| st_ev := e; st_trace := (tr2 ++ [Term_Defs.split i2 (session_plc ac)]) ++ [cvm_thread_start l (session_plc ac) t2 (get_et e)]; st_evid := i2 + 1; st_config := ac |}) eqn:E2;
    destruct r, r0; invc H; invc H0; destruct u, u0, c, c0.
    pose proof (IHt1 _ _ _ _ _ _ _ _ E1 E2); simpl in *; subst.
    assert (st_config = st_config0). {
      pose proof (sc_immut t1 e ((tr1 ++ [Term_Defs.split i1 (session_plc ac)]) ++ [cvm_thread_start l (session_plc ac) t2 (get_et e)]) (i1 + 1) ac); monad_unfold;
      pose proof (sc_immut t1 e ((tr2 ++ [Term_Defs.split i2 (session_plc ac)]) ++ [cvm_thread_start l (session_plc ac) t2 (get_et e)]) (i2 + 1) ac); monad_unfold.
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    subst; clear E1 E2; eauto.
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
  - destruct a; monad_simp; invc H; invc H0; 
    simpl in *; intuition;
    try (rewrite H; eauto);
    try (invc H; eauto);
    destruct (aspCb ac a (get_bits e)); 
    monad_simp; invc H1; invc H2; eauto; simpl in *;
    try (rewrite H3; eauto);
    repeat ff.
  - ff; unfold doRemote_session' in *; 
    repeat (break_match; try monad_unfold; repeat find_rewrite; repeat find_injection; try congruence; eauto);
    match goal with
    | H1 : check_cvm_policy _ _ _ _ = _,
      H2 : check_cvm_policy _ _ _ _ = _ |- _ =>
        eapply check_cvm_policy_same_outputs in H1; try eapply H2; eauto;
        intuition; subst; simpl in *; subst; repeat find_rewrite;
        repeat find_injection; eauto; try congruence
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

(* States that the resulting evidence (st_ev) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_ev : forall t tr1 tr1' tr2 e e' i i' ac ac' res,
    build_cvm t
           {| st_ev := e; st_trace := tr1; st_evid := i; st_config := ac |} =
    (res, {| st_ev := e'; st_trace := tr1'; st_evid := i'; st_config := ac' |}) ->
    
    st_ev
      (execErr (build_cvm t)
           {| st_ev := e; st_trace := tr2; st_evid := i; st_config := ac |}) = e'.
Proof.

intros.
destruct (build_cvm t {| st_ev := e; st_trace := tr2; st_evid := i; st_config := ac |}) eqn:ff.
simpl.
vmsts.
simpl.
subst.
dohi.
df.
edestruct st_trace_irrel.
apply H. 

assert (r = res).
{
  eapply cvm_errors_deterministic.
  apply Heqp.
  apply H.
}
subst.

apply Heqp.
intuition. 
Qed.

(* States that the resulting event id counter (st_evid) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_evid : forall t tr1 tr1' tr2 e e' i i' ac ac' res,
    build_cvm t
           {| st_ev := e; st_trace := tr1; st_evid := i; st_config := ac|} =
    (res, {| st_ev := e'; st_trace := tr1'; st_evid := i'; st_config := ac' |}) ->
    
    st_evid
      (execErr (build_cvm t)
           {| st_ev := e; st_trace := tr2; st_evid := i; st_config := ac |}) = i'.
Proof.

intros.
destruct (build_cvm t {| st_ev := e; st_trace := tr2; st_evid := i; st_config := ac |}) eqn:ff.
simpl.
vmsts.
simpl.
subst.
dohi.
df.
edestruct st_trace_irrel.
apply H. 

assert (r = res).
{
  eapply cvm_errors_deterministic.
  apply Heqp.
  apply H.
}
subst.

apply Heqp.
intuition. 
Qed.


(* States that the resulting evidence (st_ev) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_ac : forall t tr1 tr1' tr2 e e' i i' ac ac' res,
    build_cvm t
           {| st_ev := e; st_trace := tr1; st_evid := i; st_config := ac |} =
    (res, {| st_ev := e'; st_trace := tr1'; st_evid := i'; st_config := ac' |}) ->
    
    st_config
      (execErr (build_cvm t)
           {| st_ev := e; st_trace := tr2; st_evid := i; st_config := ac |}) = ac'.
Proof.
  intros.
  destruct (build_cvm t {| st_ev := e; st_trace := tr2; st_evid := i; st_config := ac |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  subst.
  dohi.
  df.
  edestruct st_trace_irrel.
  apply H. 

  assert (r = res).
  {
    eapply cvm_errors_deterministic.
    apply Heqp.
    apply H.
  }
  subst.

  apply Heqp.
  intuition. 
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
    annoP annt t.
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
  | [H: annoP _ _ (*_ (?c _) *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Lemma annoP_indexed_redo: forall t annt n n',
    anno t n = (n', annt) ->
    annoP_indexed annt t n n'.
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
  try (unfold OptMonad_Coq.ret in * );
  try (unfold OptMonad_Coq.bind in * );
  try (unfold ErrorStMonad_Coq.bind in * );
  try (unfold ErrorStMonad_Coq.ret in * );
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

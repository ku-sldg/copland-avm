(* Definitions, properties, and associated automation related to 
    Appraisal and EvidenceT examination/reconstruction.

    Also included:  properties about CVM internal EvidenceT and Event handling.  
    TODO:  This file has become quite bloated.  May need to refactor/decompose.  *)

Require Import AutoApp Defs StructTactics OptMonad_Coq Cvm_Impl Cvm_St ResultT Axioms_Io Attestation_Session Helpers_CvmSemantics Cvm_Monad More_lists Auto Term_Defs Evidence_Bundlers.

Require Import List.
Import ListNotations OptNotation.

Require Import Lia Coq.Program.Tactics.

Lemma firstn_long: forall (e:list BS) x,
  length e >= x ->
  length (firstn x e) = x.
Proof.
  intros.
  eapply firstn_length_le.
  lia.
Qed.

Lemma skipn_long: forall (e:list BS) x y,
  length e = x + y ->
  length (skipn x e) = y.
Proof.
  intros.
  assert (length (skipn x e) = length e - x).
  { eapply skipn_length. }
  lia.
Qed.

Lemma peel_n_rawev_result_spec : forall n ls ls1 ls2 st st',
  (peel_n_rawev n ls) st = (resultC (ls1, ls2), st') ->
  ls = ls1 ++ ls2 /\ length ls1 = n.
Proof.
  induction n; intuition; repeat ff; subst;
  err_monad_unfold; ffa.
Qed.

Lemma peel_n_none_spec : forall n ls e st st',
  (peel_n_rawev n ls) st = (errC e, st') ->
  length ls < n.
Proof.
  induction n; intuition; repeat ff;
  err_monad_unfold; ffa; try lia.
Qed.

Lemma peel_n_rawev_state_immut : forall n r st res st',
  peel_n_rawev n r st = (res, st') ->
  st = st'.
Proof.
  induction n; simpl in *; intros; cvm_monad_unfold; ff.
Qed.

Lemma split_evidence_state_immut : forall r et1 et2 res st st',
  split_evidence r et1 et2 st = (res, st') ->
  st = st'.
Proof.
  intros.
  unfold split_evidence in *; cvm_monad_unfold; ff;
  repeat find_eapply_lem_hyp peel_n_rawev_state_immut; ff.
Qed.

Lemma invoke_APPR_spans : forall G et u c i st,
  invoke_APPR et st = (resultC u, c) ->
  appr_events_size G et = resultC i ->
  st_evid c = st_evid st + i.
Proof.
  induction et; simpl in *; intuition; cvm_monad_unfold;
  ff; result_monad_unfold; ff.
  eapply IHet1 in Heqp0; simpl in *; eauto;
  eapply IHet2 in Heqp1; simpl in *; eauto;
  repeat find_rewrite;
  find_eapply_lem_hyp split_evidence_state_immut; ff; lia.
Qed.

Require Import Maps.

Inductive et_same_asps : EvidenceT -> EvidenceT -> Prop :=
| et_same_asps_refl : forall e, et_same_asps e e
| et_same_asps_symm : forall e1 e2, et_same_asps e1 e2 -> et_same_asps e2 e1
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

Lemma et_same_asps_impl_same_size : forall G e1 e2,
  et_same_asps e1 e2 ->
  et_size G e1 = et_size G e2.
Proof.
  intros.
  induction H; simpl in *; ffa using result_monad_unfold.
Qed.
Local Hint Resolve et_same_asps_impl_same_size : core.

Lemma et_same_asps_appr_procedure : forall G e1 e1' e2 e2' p1 p2,
  et_same_asps e1 e2 ->
  appr_procedure G p1 e1 = resultC e1' ->
  appr_procedure G p2 e2 = resultC e2' ->
  et_same_asps e1' e2'.
Proof.
  intros.
  generalizeEverythingElse H.
  induction H; simpl in *; intuition; repeat find_injection; eauto;
  try (econstructor; fail).
  - generalizeEverythingElse e;
    induction e; intros; simpl in *; ff; try (econstructor; fail);
    try (repeat eapply et_same_asps_asp; try econstructor; eauto);
    result_monad_unfold; ff;
    repeat match goal with
    | H1 : appr_procedure _ _ ?e1 = resultC ?e1',
      H2 : appr_procedure _ _ ?e2 = resultC ?e2',
      IH : context[appr_procedure _ _ ?e1 = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; 
      clear H2; eauto
    end; eapply et_same_asps_split; eauto.
  - eapply et_same_asps_symm; ffa.
  - eapply et_same_asps_asp; eapply et_same_asps_nonce.
  - ff; eapply et_same_asps_asp; eapply et_same_asps_asp; eauto. 
  - result_monad_unfold; ff;
    repeat match goal with
    | H1 : appr_procedure _ _ ?e1 = resultC ?e1',
      H2 : appr_procedure _ _ ?e2 = resultC ?e2',
      IH : context[appr_procedure _ _ ?e1 = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; 
      clear H2; eauto
    end; eapply et_same_asps_split; eauto.
Qed.
Local Hint Resolve et_same_asps_appr_procedure : core.

Lemma et_same_asps_eval_same_asps : forall G t p1 p2 e1 e1' e2 e2',
  et_same_asps e1 e2 ->
  eval G p1 e1 t = resultC e1' ->
  eval G p2 e2 t = resultC e2' ->
  et_same_asps e1' e2'.
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a; simpl in *; ff; eauto;
    try (econstructor; fail);
    try (eapply et_same_asps_asp; eauto);
    try (destruct s; simpl in *; eauto; try econstructor; fail);
    eapply et_same_asps_appr_procedure; eauto.
  - result_monad_unfold; ffa.
  - result_monad_unfold; ffa;
    destruct s, s, s0; simpl in *;
    repeat match goal with
    | H1 : eval _ ?p1 ?e1 ?t = resultC ?e1',
      H2 : eval _ ?p2 ?e2 ?t = resultC ?e2',
      IH : context[eval _ _ _ ?t = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; 
      clear H2; eauto;
      try (eapply et_same_asps_symm; eauto; fail);
      try (eapply et_same_asps_refl; fail)
    end;
    eapply et_same_asps_split; econstructor; eauto.
  - result_monad_unfold; ffa;
    destruct s, s, s0; simpl in *;
    repeat match goal with
    | H1 : eval _ ?p1 ?e1 ?t = resultC ?e1',
      H2 : eval _ ?p2 ?e2 ?t = resultC ?e2',
      IH : context[eval _ _ _ ?t = _ -> _] |- _ =>
      eapply IH in H1; try eapply H2; 
      clear H2; eauto;
      try (eapply et_same_asps_symm; eauto; fail);
      try (eapply et_same_asps_refl; fail)
    end;
    eapply et_same_asps_split; econstructor; eauto.
Qed.
Local Hint Resolve et_same_asps_eval_same_asps : core.

Lemma appr_procedure_et_size_plc_irrel : forall G e1 e1' e2 e2' p1 p2,
  et_same_asps e1 e2 ->
  appr_procedure G p1 e1 = resultC e1' ->
  appr_procedure G p2 e2 = resultC e2' ->
  et_size G e1' = et_size G e2'.
Proof.
  eauto.
Qed.

Lemma eval_et_size_plc_irrel : forall G t p1 p2 e1 e1' e2 e2',
  et_same_asps e1 e2 ->
  eval G p1 e1 t = resultC e1' ->
  eval G p2 e2 t = resultC e2' ->
  et_size G e1' = et_size G e2'.
Proof.
  intros.
  eauto.
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

Lemma events_size_eval_res_irrel : forall G t1 t p1 p2 et e1 e2 n1 n2,
  eval G p1 et t1 = resultC e1 ->
  eval G p2 et t1 = resultC e2 ->
  events_size G p1 e1 t = resultC n1 ->
  events_size G p2 e2 t = resultC n2 ->
  n1 = n2.
Proof.
  intros.
  assert (et_same_asps e1 e2) by (
    assert (et_same_asps et et) by econstructor;
    eauto
  );
  clear H H0 et.
  generalizeEverythingElse t.
  induction t; simpl in *; intuition; ffa using result_monad_unfold.
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

(* Axiom the_remote_axiom : forall sc q ev t rawEv st u st',
  do_remote sc q ev t = resultC rawEv ->
  build_cvm t st = (resultC u, st') /\ get_bits (st_ev st') = rawEv. *)

(* : forall plc_map p uuid sc my_plc e t resp_js ev req success st u st',
  map_get plc_map p = Some uuid ->
  req = (mkPRReq sc my_plc e t) ->
  make_JSON_Network_Request uuid (to_JSON req) = resultC resp_js ->
  from_JSON resp_js = resultC (mkPRResp success ev) ->
  build_cvm t st = (resultC u, st') /\ get_bits (st_ev st') = ev. *)

Axiom parallel_vm_thread_axiom : forall i t e e' p,
  parallel_vm_thread i p e t = e' ->
  forall st sc,
    st = {| st_ev := e; st_trace := nil; st_evid := i; st_config := sc |} ->
    session_plc sc = p ->
    exists st' u,
      build_cvm t st = (resultC u, st') /\ st_ev st' = e'.

Definition well_formed_context (G : GlobalContext) : Prop :=
  map_get (asp_types G) sig_aspid = Some (EXTD 1) /\
  map_get (asp_types G) hsh_aspid = Some COMP /\
  map_get (asp_types G) enc_aspid = Some ENCR /\
  map_get (asp_types G) enc_aspid = Some (EXTD 1).

Theorem invoke_appr_evidence : forall st st' u e,
  well_formed_context (session_context (st_config st)) ->
  invoke_APPR (get_et (st_ev st)) st = (resultC u, st') ->
  appr_procedure (session_context (st_config st)) 
    (session_plc (st_config st)) (get_et (st_ev st)) = resultC e ->
  get_et (st_ev st) = e.
Proof.
  intros;
  destruct st; simpl in *; destruct st_ev; simpl in *;
  generalizeEverythingElse e0;
  induction e0; simpl in *; intuition; ff;
  cvm_monad_unfold; unfold well_formed_context in *;
  destruct_conjs; ff.
Qed.

Theorem cvm_evidence_type : forall t st u st' e,
  well_formed_context (session_context (st_config st)) ->
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
  (* cvm_monad_unfold; simpl in *; ff; repeat find_rewrite;
    simpl in *; eauto. *)
  - cvm_monad_unfold; ff. 
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
    eapply sc_immut_better in Heqp; simpl in *;
    unfold Evidence_Bundlers.ss_cons; simpl in *; ff;
    eapply IHt2 in Heqp0 as ?; simpl in *;
    eapply sc_immut_better in Heqp0; simpl in *; try (rw; ff; fail);
    ff; rw; eauto.
  - ffa using (try cvm_monad_unfold; try result_monad_unfold);
    destruct s, s, s0; simpl in *;
    eapply IHt1 in Heqp as ?; ff;
    eapply sc_immut_better in Heqp; simpl in *; ff;
    unfold Evidence_Bundlers.ss_cons; simpl in *; ff;
    find_eapply_lem_hyp parallel_vm_thread_axiom; eauto;
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
        try (eapply cvm_evidence_type in H as ?; eauto; [])
      ]; clear H
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
  - result_monad_unfold.
    cvm_monad_unfold.
    repeat break_match; try congruence.
    repeat find_injection.
    eapply sc_immut_better in Heqp as ?;
    repeat find_rewrite;
    eapply IHt1 in Heqp; try eapply Heqr;
    simpl in *; eauto; ff;
    destruct s, s, s0; simpl in *; ff; try lia;
    repeat find_rewrite; repeat find_injection; try lia.
Qed.

(* 
(** * CVM event ID span same as annotated term range *)
Lemma span_cvm: forall atp t annt i j e e' tr tr' i' ac ac',
    build_cvmP
      atp
      {| st_ev := e;
         st_trace := tr;
         st_evid := i;
         st_config := ac |} 
      (resultC tt)
      {| st_ev := e';
         st_trace := tr';
         st_evid := i';
         st_config := ac' |} ->
    
    term_to_coreP t atp -> 
    anno t i = (j, annt) ->
    j = i'.
Proof.
  intros.
  assert (j = i + event_id_span' t).
  {
    assert (j - i = event_id_span' t).
    {
      symmetry.
      eapply span_range.
      eauto.
    }
    rewrite <- H2.
    assert (j > i).
    {
      eapply anno_mono; eauto.
    }
    lia.
  }
  subst.
  symmetry.
  eapply cvm_spans; eauto.
Qed.


(** * Propositional version of span_cvm *)
Lemma anno_span_cvm: forall t pt annt i i' e e' tr tr' st_evid1 ac ac',
    anno t i = (i', annt) ->
    term_to_coreP t pt ->
    build_cvmP pt
                     {|
                       st_ev := e ;
                       st_trace := tr ;
                       st_evid := i;
                       st_config := ac
                     |} (resultC tt)
                     {|
                       st_ev := e';
                       st_trace := tr';
                       st_evid := st_evid1;
                       st_config := ac'
                     |} ->
    i' = st_evid1.
Proof.
  intros.
  invc H.
  eapply span_cvm; eauto.
Qed.
*)


Lemma wf_Evidence_firstn: forall G e0 e1 e2 n,
  wf_Evidence G (evc e0 e1) ->
  et_size G e1 = resultC n ->
  firstn n (e0 ++ e2) = e0.
Proof.
  intros; invc H; find_rewrite;
  find_injection; eapply firstn_append.
Qed.

Lemma wf_Evidence_skipn: forall G e0 e1 e2 n,
  wf_Evidence G (evc e0 e1) ->
  et_size G e1 = resultC n ->
  skipn n (e0 ++ e2) = e2.
Proof.
  intros; invc H; find_rewrite;
  find_injection; eapply skipn_append.
Qed.

(* Lemma wf_Evidence_preserved_par : forall G loc t r et e' p,
  wf_Evidence G (evc r et) ->
  parallel_vm_thread loc p (evc r et) t = e' ->
  wf_Evidence G e'.
Proof.
  intros.
  eapply parallel_vm_thread_axiom in H0.
  intros. *)

Axiom remote_axiom : forall sc p e t e',
  (* make_JSON_Network_Request uuid (to_JSON req) = resultC js_resp ->
  from_JSON js_resp = resultC resp ->
  prresp_rawev resp = r -> *)

  do_remote sc p e t = resultC e' ->
  forall st sc i,
    (* NOTE: This is maybe a bit stronger than we want!
    we really need to be looking at the NEW session config that was
    created via the passed session *)
    st = {| st_ev := e; st_trace := nil; st_evid := i; st_config := sc |} ->
    exists st' u,
      build_cvm t st = (resultC u, st') /\ get_bits (st_ev st') = e' /\
      eval (session_context sc) p (get_et e) t = resultC (get_et (st_ev st')).

Lemma wf_Evidence_ss_cons : forall G e1 e2,
  wf_Evidence G e1 ->
  wf_Evidence G e2 ->
  wf_Evidence G (ss_cons e1 e2).
Proof.
  intros; invc H; invc H0;
  econstructor; simpl in *;
  result_monad_unfold;
  ff; rewrite app_length; eauto.
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
  split_evidence r et1 et2 st = (resultC (e1, e2), st') ->
  exists r1 r2, (e1,e2) = (evc r1 et1, evc r2 et2).
Proof.
  intros.
  unfold split_evidence in *.
  cvm_monad_unfold; ff.
Qed.

Lemma wf_Evidence_split_evidence : forall r et1 et2 st st' G r1 r2,
  wf_Evidence G (evc r (split_evt et1 et2)) ->
  session_context (st_config st) = G ->
  split_evidence r et1 et2 st = (resultC (r1, r2), st') ->
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

Lemma wf_Evidence_invoke_APPR : forall st u st',
  wf_Evidence (session_context (st_config st)) (st_ev st) ->
  invoke_APPR (get_et (st_ev st)) st = (resultC u, st') ->
  wf_Evidence (session_context (st_config st)) (st_ev st').
Proof.
  destruct st, st_ev; simpl in *;
  generalizeEverythingElse e;
  induction e; simpl in *; intuition;
  cvm_monad_unfold;
  repeat find_injection; simpl in *;
  try eapply wf_Evidence_mt_evc;
  ff;
  try match goal with
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


(** * Lemma:  CVM execution preserves well-formedness of Evidence bundles 
      (EvidenceT Type of sufficient length for raw EvidenceT). *)
Lemma wf_Evidence_preserved_by_cvm : forall t st st' e e' u,
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
    find_eapply_lem_hyp remote_axiom; eauto;
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
      try reflexivity; ff; []
    end; repeat find_rewrite; ff.
  - ffa; simpl in *.
    eapply wf_Evidence_ss_cons.
    * eapply IHt1 in Heqp; simpl in *; try reflexivity;
      eauto with wf_Evidence.
    * eapply sc_immut_better in Heqp; simpl in *.
      eapply IHt2 in Heqp0; simpl in *; try reflexivity;
      repeat find_rewrite; eauto with wf_Evidence.
  - ffa; simpl in *.
    eapply wf_Evidence_ss_cons.
    * eapply IHt1 in Heqp; simpl in *; try reflexivity;
      eauto with wf_Evidence.
    * eapply sc_immut_better in Heqp; simpl in *.
      destruct (parallel_vm_thread (st_evid st + 1) (session_plc (st_config c1)) (splitEv_r s (st_ev st)) t2) eqn:?;
      find_eapply_lem_hyp parallel_vm_thread_axiom;
      try reflexivity;
      break_exists; destruct_conjs.
      eapply IHt2 in H0;
      simpl in *; try reflexivity;
      repeat find_rewrite;
      ff;
      eauto with wf_Evidence.
Qed.

Require Import Term.

(** * Helper Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. *)
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
    * result_monad_unfold; simpl in *; ffa.
      eapply split_evidence_state_immut in Heqp as ?;
      eapply split_evidence_res_spec in Heqp as ?;
      clear Heqp;
      break_exists; repeat find_injection;
      simpl in *;
      repeat match goal with
      | st : cvm_st |- _ => destruct st; simpl in *; ff
      | e : Evidence |- _ => destruct e; simpl in *; ff
      end.
      repeat find_rewrite; repeat find_injection;
      eapply IHe0_1 in Heqp1 as ?; ff;
      eapply sc_immut_invoke_APPR in Heqp1 as ?; simpl in *;
      eapply invoke_APPR_spans in Heqp1; simpl in *;
      try eapply asp_appr_events_size_works; eauto; ff;
      unfold ss_cons in *; ff; simpl in *;
      eapply IHe0_2 in Heqp2 as ?; try ff;
      eapply sc_immut_invoke_APPR in Heqp2 as ?; simpl in *;
      eapply invoke_APPR_spans in Heqp2; simpl in *;
      try eapply asp_appr_events_size_works; eauto; ff.
      repeat find_rewrite.
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
  - ff; invc H0; cvm_monad_unfold; ff;
    simpl in *; repeat find_rewrite;
    repeat find_injection; ff.
    eapply IHt1 in Heqp as ?; eauto;
    eapply sc_immut_better in Heqp as ?.
    eapply IHt2 in H6; try eapply H11;
    simpl in *; eauto; ff.
    * repeat rewrite app_assoc; eauto.
    * eapply cvm_spans; ff;
      repeat find_rewrite; eauto;
      eapply events_range; eauto.
    * eapply cvm_evidence_type; eauto.
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

(* 

(** * Lemma stating: CVM traces are "cumulative" (or monotonic).  
      Traces are only ever extended--prefixes are maintained. 
      TODO:  rename to st_trace_cumul 
*) 
Lemma suffix_prop : forall t e e' tr tr' i i' ac ac' res,
    build_cvmP t
           {| st_ev := e;
              st_trace := tr;
              st_evid := i; st_config := ac |}
           (res)
           {|
             st_ev := e';
             st_trace := tr';
             st_evid := i'; st_config := ac' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.

  do_exists_some_cc t {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}.
  wrap_ccp.
  (*

  rewrite ccp_iff_cc in *. *)

  repeat do_st_trace_assumps.
  repeat find_rw_in_goal.
  eexists.

  erewrite st_trace_cumul''.
  3: {
    eassumption.
  }
  simpl.
  tauto.
  rewrite app_nil_r.
  ff.
  destruct H1; destruct res; ff.
  +
    assert (c = c0).
    {
      edestruct cvm_errors_deterministic; ffa.
      invc H2; ffa.
      invc H; ffa.
      simpl in *; ffa.
    }
    subst.
    eassumption.
  +
  assert (errC c = resultC tt).
  {
    wrap_ccp_dohi. ff.
    invc H2. invc H.
    edestruct cvm_errors_deterministic.
    apply H0.
    apply H1.
    ff.
  }
solve_by_inversion.
  +
  assert (errC c = resultC tt).
  {
    wrap_ccp_dohi. ff.
    invc H2. invc H.
    edestruct cvm_errors_deterministic.
    apply H0.
    apply H1.
    ff.
  }
solve_by_inversion.
  +
    wrap_ccp_dohi.
    eassumption.
Qed.

Ltac do_suffix name :=
  match goal with
  | [H': build_cvmP ?t
         {| st_ev := _; st_trace := ?tr; st_evid := _; st_config := _ |}
         (_)
         {| st_ev := _; st_trace := ?tr'; st_evid := _; st_config := _ |}
         (*H2: well_formed_r ?t*) |- _] =>
    fail_if_in_hyps_type (exists l, tr' = tr ++ l);
    assert (exists l, tr' = tr ++ l) as name by (eapply suffix_prop; [apply H'])
  end.

(** * Structural Lemma:   Decomposes the CVM trace for the lseq phrase into the appending of the two traces
      computed by its subterms, where each subterm starts from the empty trace.

      Useful for leveraging induction hypotheses in the lseq case of induction that require empty traces in the 
      initial CVM state. *)
Lemma alseq_decomp : forall t1' t2' e e'' tr i i'' ac ac'',
    build_cvmP
      (lseqc t1' t2')
      {| st_ev := e;
         st_trace := [];
         st_evid := i; st_config := ac |}
      (resultC tt)
      {| st_ev := e'';
         st_trace := tr;
         st_evid := i''; st_config := ac'' |} ->

    exists e' tr' i' ac',
      build_cvmP
        t1'
        {| st_ev := e;
           st_trace := [];
           st_evid := i; st_config := ac |}
        (resultC  tt)
        {| st_ev := e';
           st_trace := tr';
           st_evid := i'; st_config := ac' |} /\
      exists tr'',
        build_cvmP
          t2'
          {| st_ev := e';
             st_trace := [];
             st_evid := i'; st_config := ac' |}
          (resultC tt)
          {| st_ev := e'';
             st_trace := tr'';
             st_evid := i''; st_config := ac'' |} /\
        tr = tr' ++ tr''.     
Proof.
  intros.
  wrap_ccp_dohi.
  repeat ff.
  wrap_ccp_dohi.
  
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.

  split.
  - rewrite <- ccp_iff_cc in *.
    eassumption.
  -
    do_exists_some_cc t2' {| st_ev := st_ev0; st_trace := []; st_evid := st_evid0; st_config := st_config0 |}.
    vmsts.
    repeat ff.
    destruct H0; ff.
    +
    assert (errC c = resultC tt).
    {
      wrap_ccp_dohi. ff.
      rewrite <- ccp_iff_cc in *.
      eapply cvm_errors_deterministic; eauto.
    }
  solve_by_inversion.
    +
    ff.

    eexists.

    wrap_ccp_dohi.

    split.
    ++
      eassumption.
    ++
      repeat do_st_trace.
      repeat find_rw_in_goal.
      eapply st_trace_cumul'; 
        eassumption.
Qed.


(** Structural convenience lemma:  reconfigures CVM execution to use an empty initial trace *)
Lemma restl : forall t e e' x tr i i' ac ac' res,
    build_cvmP t
      {| st_ev := e; st_trace := x; st_evid := i; st_config := ac|}
      (res)
      {| st_ev := e'; st_trace := x ++ tr; st_evid := i'; st_config := ac' |} ->

    build_cvmP t
      {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}
      (res)
      {| st_ev := e'; st_trace := tr; st_evid := i'; st_config := ac' |}.
Proof.
  intros.

  do_exists_some_cc t  {| st_ev := e; st_trace := []; st_evid := i; st_config := ac |}.
  wrap_ccp_dohi.

  assert (res = H1).
  {
    wrap_ccp_dohi.
    eapply cvm_errors_deterministic.
    invc H.
    apply H0.
    invc H2.
    eassumption.
  }
  subst.

  assert (st_trace = tr).
  {
    do_st_trace.
    rewrite H0; clear H0.
    assert (tr = st_trace).
    {
      assert (Cvm_St.st_trace {| st_ev := st_ev; st_trace := x ++ tr; st_evid := st_evid; st_config := st_config|} =
              x ++ Cvm_St.st_trace {| st_ev := st_ev; st_trace := st_trace; st_evid := st_evid; st_config := st_config |}).
      {
        eapply st_trace_cumul'; eauto.
        wrap_ccp_dohi.
        eassumption.
      }
      simpl in *.
      eapply app_inv_head; eauto.
    }
    jkjke.
  }

  wrap_ccp_dohi.
  congruence.
Qed.

Ltac do_restl :=
  match goal with
  | [H: build_cvmP ?t
        {| st_ev := ?e; st_trace := ?tr; st_evid := ?i; st_config := ?ac |}
        ?res
        {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_evid := ?i'; st_config := ?ac' |}
        (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_by
      (build_cvmP t
        {| st_ev := e; st_trace := []; st_evid := i; st_config := ac|}
        ?res
        {| st_ev := e'; st_trace := x; st_evid := i'; st_config := ac' |})
      ltac:(eapply restl; [apply H])
  end.

(** * Lemma:  EvidenceT semantics same for annotated and un-annotated terms *)
Lemma eval_aeval': forall t1 p et,
    eval (unanno t1) p et = aeval t1 p et.
Proof.
  induction t1; intros;
    repeat ff;
    repeat jkjke.
Qed.

Axiom cvm_EvidenceT_correct_type : forall t p e e',
  cvm_EvidenceT t p e = e' -> 
  get_et e' = eval t p (get_et e).


(** * Lemma:  parallel CVM threads preserve the reference EvidenceT Type semantics (eval). *)
Lemma par_EvidenceT_r: forall l p bits bits' et et' t2,
    parallel_vm_thread l (copland_compile t2) p (evc bits et) = evc bits' et' ->
    et' = eval t2 p et.
Proof.
  intros.
  rewrite par_EvidenceT in H.
  assert (get_et (evc bits' et') = eval t2 p (get_et (evc bits et))).
  {
    eapply cvm_EvidenceT_correct_type; eauto.
  }
  ff.
Qed.
         
(** * Axiom about "simulated" parallel semantics of CVM execution:
      Executing a "CLEAR" before a term is the same as executing that term with mt_evtinitial EvidenceT.
      TODO:  can we use existing axioms to prove this? *)
Axiom par_EvidenceT_clear: forall l p bits et t2,
    parallel_vm_thread l (lseqc (aspc CLEAR) t2) p (evc bits et) =
    parallel_vm_thread l t2 p mt_evc.

Lemma doRemote_session'_sc_immut : forall t st st' res p ev,
    doRemote_session' t p ev st = (res, st') ->
    st_config st = st_config st'.
Proof.
  unfold doRemote_session'.
  intuition.
  cvm_monad_unfold.
  ff.
Qed.

Lemma build_cvm_sc_immut : forall t st st' res,
    build_cvm t st = (res, st') ->
    st_config st = st_config st'.
Proof.
  induction t; simpl in *; intuition; eauto; ffa using cvm_monad_unfold.
Qed.

Lemma build_cvmP_sc_immut : forall t st st' res,
    build_cvmP t st res st' ->
    st_config st = st_config st'.
Proof.
  setoid_rewrite <- ccp_iff_cc.
  eapply build_cvm_sc_immut.
Qed.

(** * Main Lemma:  CVM execution maintains the EvidenceT Type reference semantics (eval) for 
      its internal EvidenceT bundle. *)
Lemma cvm_refines_lts_EvidenceT' : forall t tr tr' bits bits' et et' i i' ac ac',
    build_cvmP (copland_compile t)
        (mk_st (evc bits et) tr i ac)
        (resultC tt)
        (mk_st (evc bits' et') tr' i' ac') ->
    et' = (Term_Defs.eval t (session_plc ac) et).
Proof.
  intuition.
  eapply build_cvmP_sc_immut in H as H'.
  simpl in *; subst.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.
    ffa.  
    destruct a; (try dd; eauto); ffa using cvm_monad_unfold.
      

  - (* at case *)
    rewrite <- ccp_iff_cc in *.
    dd.
    repeat ffa.

  - (* alseq case *)
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eapply restl.
    eassumption.
    fold copland_compile in *.
    destruct_conjs.
    repeat match goal with
    | x : Evidence |- _ =>
      destruct x
    | H : build_cvmP (copland_compile t1) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt1 in H as Ho;
      simpl in *; subst; clear H
    | H2 : build_cvmP (copland_compile t2) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H2 as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt2 in H2 as Ho;
      simpl in *; subst; clear H2
    end; eauto.
    
  - (* abseq case *)
    simpl in *; repeat ff; subst;
    wrap_ccp; cbn in *; repeat ff; cbn in *;
    repeat match goal with
    | x : Evidence |- _ =>
      destruct x
    | u : unit |- _ =>
      destruct u
    | H : build_cvmP (copland_compile t1) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt1 in H as Ho;
      simpl in *; subst; clear H
    | H2 : build_cvmP (copland_compile t2) _ _ _ |- _ =>
      let AC := fresh "AC" in
      let Ho := fresh "Ho" in
      eapply build_cvmP_sc_immut in H2 as AC;
      simpl in *; try rewrite AC in *; clear AC;
      eapply IHt2 in H2 as Ho;
      simpl in *; subst; clear H2
    end; eauto.

   - (* abpar case *)

    destruct s; repeat ffa;
    wrap_ccp; cbn in *; repeat ff; cbn in *;
    repeat (ffa; match goal with
    | u : unit |- _ =>
      destruct u
    end).
    +
      assert (e0 = eval t2 (session_plc ac') et).
      {
        eapply par_EvidenceT_r; eauto.
      }
      ffa.
      
    +
      find_apply_hyp_hyp.

      assert (e0 = eval t2 (session_plc ac') mt_evt).
      {
        rewrite par_EvidenceT_clear in *.
        eapply par_EvidenceT_r; eauto.
      }
      congruence.
    +
      wrap_ccp.
      ffa.
      assert (e0 = eval t2 (session_plc ac') et).
      {
        eapply par_EvidenceT_r; eauto.
      }
      congruence.
    +
      wrap_ccp.
      ffa.
      assert (e0 = eval t2 (session_plc ac') mt_evt).
      {
        rewrite par_EvidenceT_clear in *.

        eapply par_EvidenceT_r; eauto.
      }
      congruence.
Qed.

(** * Propositional version of CVM EvidenceT Type preservation. *)
Lemma cvm_refines_lts_EvidenceT :
  forall t t' tr tr' bits bits' et et' i i' ac ac',
    term_to_coreP t t' ->
    build_cvmP t'
      (mk_st (evc bits et) tr i ac)
      (resultC tt)
      (mk_st (evc bits' et') tr' i' ac') ->
    et' = (Term_Defs.eval t (session_plc ac) et).
Proof.
  intros.
  invc H.
  eapply cvm_refines_lts_EvidenceT'.
  eauto.
Qed.


(** BEGIN Deprecated parallel annotated term stuff *)

(*
Lemma anno_parP_redo: forall t pt loc loc',
    anno_par_list' t loc = Some (loc', pt) ->
    anno_parP pt t.
Proof.
  intros.
  econstructor.
  eexists.
  jkjke.
Qed.

(*
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par t loc = (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Qed.
 *)
Lemma anno_parPloc_redo: forall t pt loc loc',
    anno_par_list' t loc = Some (loc', pt) ->
    anno_parPloc pt t loc.
Proof.
  intros.
  econstructor.
  jkjke.
Qed.

 *)

(*

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac do_annopar_loc_redo :=
  match goal with
  | [H: anno_par ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parPloc_redo in H
  end.
 *)


(*

Ltac do_annopar_redo :=
  match goal with
  | [H: anno_par_list' ?t ?loc = Some (_,?pt)
     |- _ ] =>
    eapply anno_parP_redo in H
  end.

Ltac do_annopar_loc_redo :=
  match goal with
  | [H: anno_par_list' ?t ?loc = (_,?pt)
     |- _ ] =>
    eapply anno_parPloc_redo in H
  end.



Ltac inv_annoparP :=
  match goal with
  | [H: anno_parP _ _ (* ?t (?c _) *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Ltac inv_annoparPloc :=
  match goal with
  | [H: anno_parPloc _ _ _(*?t (?c _) _ *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.
 *)


(*
Ltac wrap_annopar :=
  inv_annoparP;
  dd;
  repeat do_annopar_redo.

Ltac wrap_annoparloc :=
  inv_annoparPloc;
  dd;
  repeat do_annopar_loc_redo.
 *)


(** END Deprecated parallel annotated term stuff *)

*)
(*  Primary results of Manifest Compiler Soundnesplit_evt (for Attestation).
      Namely, that the compiler outputs a collection of manifests that support 
      execution of the input protocols.  *)

Require Import Manifest Manifest_Generator
  Maps Term_Defs Cvm_Impl Cvm_Axioms
  Cvm_Monad AM_Manager EqClass.
Require Import Manifest_Generator_Facts Attestation_Session.

Require Import Manifest_Generator_Helpers Session_Config_Compiler ManCompSoundness_Helpers Manifest_Generator_Union.
Require Import Coq.Program.Tactics StructTactics.

Import ListNotations.

Definition session_config_subset (sc1 sc2 : Session_Config) : Prop :=
  (session_context sc1) = (session_context sc2) /\
  (forall aid l targ targid ev, 
      (forall res, 
      sc1.(aspCb) (asp_paramsC aid l targ targid) ev = resultC res ->
      sc2.(aspCb) (asp_paramsC aid l targ targid) ev = resultC res)) /\
  (forall p, (forall res, 
      map_get p (sc1.(plc_map)) = Some res ->
      map_get p (sc2.(plc_map)) = Some res)) /\
  (forall p, (forall res, 
      map_get p (sc1.(pubkey_map)) = Some res ->
      map_get p (sc2.(pubkey_map)) = Some res)) /\
  (forall aid l targ targid ev errStr,
      sc1.(aspCb) (asp_paramsC aid l targ targid) ev = errC (Runtime errStr) ->
      sc2.(aspCb) (asp_paramsC aid l targ targid) ev = errC (Runtime errStr)) 
  /\
  (forall p,
      map_get p (sc1.(plc_map)) = None ->
      map_get p (sc2.(plc_map)) = None) /\
  (forall p, 
      map_get p (sc1.(pubkey_map)) = None ->
      map_get p (sc2.(pubkey_map)) = None).

Theorem session_config_subset_refl : forall sc1,
  session_config_subset sc1 sc1.
Proof.
  unfold session_config_subset; intuition.
Qed.

Theorem session_config_subset_trans : forall sc1 sc2 sc3,
  session_config_subset sc1 sc2 ->
  session_config_subset sc2 sc3 ->
  session_config_subset sc1 sc3.
Proof.
  unfold session_config_subset; intuition; ff.
Qed.

Import ResultNotation.

Fixpoint session_config_support_exec_appr (p : Plc) (e : EvidenceT) 
    (sc : Session_Config) : Prop :=
  match e with
  | mt_evt => True
  | nonce_evt _ => 
    forall ev,
    ((exists res, 
    sc.(aspCb) check_nonce_params ev = resultC res) \/ 
    (exists errStr, sc.(aspCb) check_nonce_params ev = errC (Runtime errStr)))
  | asp_evt p' par e' =>
    let '(asp_paramsC aspid l targ targid) := par in
    match (map_get aspid (asp_comps sc.(session_context))) with
    | None => False
    | Some appr_aspid =>
      forall l targ targid ev,
      ((exists res, 
      sc.(aspCb) (asp_paramsC appr_aspid l targ targid) ev = resultC res) \/ 
      (exists errStr, sc.(aspCb) (asp_paramsC appr_aspid l targ targid) ev = errC (Runtime errStr)))
    end
  | left_evt e' => 
    match apply_to_evidence_below (session_context sc) (fun e' => session_config_support_exec_appr p e' sc) [Trail_LEFT] e' with
    | resultC P => P
    | errC _ => False
    end
  | right_evt e' => 
    match apply_to_evidence_below (session_context sc) (fun e' => session_config_support_exec_appr p e' sc) [Trail_RIGHT] e' with
    | resultC P => P
    | errC _ => False
    end
  | split_evt e1 e2 =>
    (session_config_support_exec_appr p e1 sc) /\
    (session_config_support_exec_appr p e2 sc)
  end.

Fixpoint session_config_supports_exec (p : Plc) (e : EvidenceT) (t : Term) 
    (sc : Session_Config) : Prop :=
  match t with
  | asp a =>
      match a with
      | NULL => True
      | SIG => 
          forall ev,
          ((exists res, 
          sc.(aspCb) sig_params ev = resultC res) \/ 
          (exists errStr, sc.(aspCb) sig_params ev = errC (Runtime errStr)))
      | HSH =>
          forall ev,
          ((exists res, 
          sc.(aspCb) hsh_params ev = resultC res) \/ 
          (exists errStr, sc.(aspCb) hsh_params ev = errC (Runtime errStr)))
      | ENC p =>
          (forall ev,
          ((exists res, 
          sc.(aspCb) (enc_params p) ev = resultC res) \/ 
          (exists errStr, sc.(aspCb) (enc_params p) ev = errC (Runtime errStr)))) /\
          ((exists res, 
            map_get p (sc.(pubkey_map)) = Some res))
      | ASPC (asp_paramsC aspid _ _ _) =>
          (forall l targ targid ev,
          ((exists res, 
          sc.(aspCb) (asp_paramsC aspid l targ targid) ev = resultC res) \/ 
          (exists errStr, sc.(aspCb) (asp_paramsC aspid l targ targid) ev = errC (Runtime errStr))))
      | APPR => session_config_support_exec_appr p e sc
      end
  | att p' t' => 
      (* We only care that we can dispatch it *)
      ((exists res, map_get p' (sc.(plc_map)) = Some res))
  | lseq t1 t2 =>
      exists sc1 sc2 e',
      (session_config_supports_exec p e t1 sc1) /\
      (eval (session_context sc) p e t1 = resultC e') /\
      (session_config_supports_exec p e' t2 sc2) /\
      session_config_subset sc1 sc /\
      session_config_subset sc2 sc
  | bseq s t1 t2 =>
      exists sc1 sc2,
      (session_config_supports_exec p (splitEv_T_l s e) t1 sc1) /\
      (session_config_supports_exec p (splitEv_T_r s e) t2 sc2) /\
      session_config_subset sc1 sc /\
      session_config_subset sc2 sc
  | bpar s t1 t2 =>
      exists sc1 sc2,
      (session_config_supports_exec p (splitEv_T_l s e) t1 sc1) /\
      (session_config_supports_exec p (splitEv_T_r s e) t2 sc2) /\
      session_config_subset sc1 sc /\
      session_config_subset sc2 sc
  end.

Ltac unfolds :=
  (* repeat cvm_monad_unfold; *)
  repeat unfold manifest_generator, generate_ASP_dispatcher, 
    aspid_manifest_update,
    sig_params, hsh_params, enc_params in *;
  simpl in *; 
  repeat (match goal with
      | x : cvm_st |- _ => destruct x
      | x : Session_Config |- _ => destruct x
      | x : Attestation_Session |- _ => destruct x
      | x : CallBackErrors |- _ => destruct x
  end; simpl in *; eauto);
  intuition.

Theorem man_gen_aspid_in : forall a m,
  In_set a (asps (aspid_manifest_update a m)).
Proof.
  induction m; simpl in *; eauto.
  eapply manadd_In_add.
Qed.
Global Hint Resolve man_gen_aspid_in : core.


      (* 
      In t' (place_terms t tp p) -> 
      run_cvm_w_config t 
      (
        (exists st', 
          build_cvm (copland_compile t') st = 
            (resultC tt, st')) 
        \/
        (exists st' errStr,
          build_cvm (copland_compile t') st = 
            (errC (dispatch_error (Runtime errStr)), st'))
      )
    ). *)

(* Theorem filter_resolver : forall {A B} `{EqClass A} (m : Map A B) a (filt : A -> bool),
  (exists x, map_get m a = Some x) ->
  filt a = true ->
  exists x, map_get (minify_mapC m filt) a = Some x.
Proof.
  induction m; intuition; simpl in *;
  destruct (eqb a a0) eqn:E.
  - rewrite eqb_eq in E; subst. rewrite H1; simpl in *; rewrite eqb_refl; eauto.
  - repeat break_match; simpl in *; 
    try (pose proof eqb_symm; congruence);
    simpl in *; eauto.
    rewrite eqb_symm; rewrite E; eauto.
Qed.

Theorem filter_resolver_mapd : forall {A B} `{EqClass A, EqClass B} (m : Map A B) a (filt : A -> bool),
  (exists x, map_get m a = Some x) ->
  filt a = true ->
  exists x, map_get (minify_mapD m filt) a = Some x.
Proof.
  induction m; intuition; simpl in *;
  destruct (eqb a a0) eqn:E.
  - rewrite eqb_eq in E; subst; destruct H1; simpl in *; 
    repeat find_injection; rewrite H2; simpl in *; rewrite eqb_refl; eauto.
  - repeat break_match; simpl in *; 
    try (pose proof eqb_symm; congruence);
    simpl in *; eauto;
    repeat (find_rewrite; intuition; eauto; try congruence).
    rewrite eqb_symm in E; congruence.
Qed.

Global Hint Resolve filter_resolver : core.
Global Hint Resolve filter_resolver_mapd : core.

Lemma in_dec_helper : forall {A B} `{EqClass A} X l l' a (c : B),
  map_get (minify_mapC l (fun x : A => if in_dec X x l' then true else false)) a = Some c ->
  In a l'.
Proof.
  induction l; simpl in *; intuition; try congruence;
  repeat break_if; eauto; simpl in *; 
  repeat break_if; eauto; try rewrite eqb_eq in Heqb1; 
  subst; eauto; congruence.
Qed.

Global Hint Resolve filter_resolver : core.
*)


Ltac kill_map_none :=
  match goal with
  | H1 : In_set ?x ?l,
    H3 : map_get ?x ?l' = None,
    H4 : forall _ : _, In_set _ ?l -> _
      |- _ => 
    let H' := fresh "H'" in
    let H'' := fresh "H'" in
    let H''' := fresh "H'" in
    eapply H4 in H1 as H';
    destruct H'; find_rewrite; congruence
  end.

Local Hint Resolve session_config_subset_refl : core.
Local Hint Resolve session_config_subset_trans : core.

Require Import Cvm_Verification.

Lemma well_formed_context_subset : forall sc1 sc2,
  session_config_subset sc1 sc2 ->
  well_formed_context (session_context sc1) ->
  well_formed_context (session_context sc2).
Proof.
  intuition; unfold session_config_subset in *; intuition; ff.
Qed.
Local Hint Resolve well_formed_context_subset : core.

Lemma session_config_supports_exec_appr_subset : forall sc1 sc2,
  session_config_subset sc1 sc2 ->
  forall p e,
  session_config_support_exec_appr p e sc1 ->
  session_config_support_exec_appr p e sc2.
Proof.
  intros.
  generalizeEverythingElse e.
  intros sc1.
  induction e using (Evidence_subterm_path_Ind_special (session_context sc1));
  simpl in *; intuition; ff;
  repeat unfold session_config_subset, check_nonce_params, hsh_params, sig_params, enc_params in *; intuition; ff.
  all: try (match goal with
    | H : context[ aspCb _ _ _ = _] |- context[aspCb _ (asp_paramsC ?a ?l ?t ?tid) ?ev = _] =>
      pose proof (H l t tid ev); ff
    end; fail).
  all: try (match goal with
    | H : context[ aspCb _ _ _ = _] |- context[aspCb _ (asp_paramsC ?a ?l ?t ?tid) ?ev = _] =>
      pose proof (H ev); ff
    end; fail).
  - ateb_diff.
  - ateb_same; ffa; eapply H in H1; ff; intuition.
  - ateb_diff. 
  - ateb_same; ffa; eapply H in H1; ff; intuition.
Qed.

Lemma session_config_supports_exec_subset : forall sc1 sc2,
  session_config_subset sc1 sc2 ->
  forall t p e,
  session_config_supports_exec p e t sc1 ->
  session_config_supports_exec p e t sc2.
Proof.
  induction t; ffa; try (unfold session_config_subset in *; ff;
  try unfold hsh_params, sig_params, enc_params in *; intuition; ffa;
    try (match goal with
    | H : context[ aspCb _ _ _ = _] |- context[aspCb _ (asp_paramsC ?a ?l ?t ?tid) ?ev = _] =>
      pose proof (H l t tid ev); ff
    end; fail);
    try (match goal with
    | H : context[ aspCb _ _ _ = _] |- context[aspCb _ (asp_paramsC ?a ?l ?t ?tid) ?ev = _] =>
      pose proof (H ev); ff
    end; fail); fail).
  - eapply session_config_supports_exec_appr_subset; ff.
  - exists x, x0, x1; intuition.
    * invc H; ff.
    * eapply session_config_subset_trans; ff.
    * eapply session_config_subset_trans; ff.
  - exists x, x0; intuition; eapply session_config_subset_trans; ff.
  - exists x, x0; intuition; eapply session_config_subset_trans; ff.
Qed.

Theorem well_formed_am_config_impl_executable : forall t p e sc,
  well_formed_context (session_context sc) ->
  session_config_supports_exec p e t sc ->
  forall st,
  session_plc sc = p ->
  (exists st', 
    build_cvm e t st sc = (resultC tt, st')) \/
  (exists st' errStr, 
    build_cvm e t st sc = (errC (dispatch_error (Runtime errStr)), st')).
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a;
    try (simpl in *; cvm_monad_unfold; eauto; fail); (* NULL, CPY *)
    subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      try break_match;
      try cvm_monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    try (unfold session_config_subset, sig_params, enc_params, hsh_params in *; intuition;

    try (match goal with
    | H1 : forall _, _,
      H2 : aspCb _ (asp_paramsC ?a ?l ?targ ?tid) ?ev' = _,
      H3 : context[ aspCb _ _ _ = errC (Runtime _) -> _],
      H4 : context[ aspCb _ _ _ = resultC _ -> _]
      |- _ =>
        let H := fresh "H" in
        let H'' := fresh "Hx" in
        let res := fresh "res" in
        edestruct H1 with (ev := ev') as [[ res H''] | [res H'']]
        ; 
        [
          (* result side *)
          eapply H4 in H''; erewrite H'' in *;
          try congruence; repeat find_injection; eauto; ff
          (* erewrite H' in *; eauto; congruence *)
          |
          (* err side *)
          eapply H3 in H''; erewrite H'' in *;
          try congruence; repeat find_injection; eauto; ff
          (* pose proof (H3 a l targ tid ev errStr) as H';
          intuition; find_rewrite; find_injection; eauto *)
        ]
    end); fail).
    destruct st, st_ev; simpl in *;
    generalizeEverythingElse e.
    induction e; simpl in *; intuition; eauto; ffa using cvm_monad_unfold;
    try (invc H3; intuition; repeat find_rewrite;
    repeat find_injection; ff; unfold check_nonce_params in *;
    try (match goal with
    | H1 : forall _, _,
      H2 : aspCb _ (asp_paramsC ?a ?l ?targ ?tid) ?ev' = _,
      H3 : context[ aspCb _ _ _ = errC (Runtime _) -> _],
      H4 : context[ aspCb _ _ _ = resultC _ -> _]
      |- _ =>
        let H := fresh "H" in
        let H'' := fresh "Hx" in
        let res := fresh "res" in
        edestruct H1 with (ev := ev') as [[ res H''] | [res H'']]
        ; 
        [
          (* result side *)
          eapply H4 in H''; erewrite H'' in *;
          try congruence; repeat find_injection; eauto; ff
          (* erewrite H' in *; eauto; congruence *)
          |
          (* err side *)
          eapply H3 in H''; erewrite H'' in *;
          try congruence; repeat find_injection; eauto; ff
          (* pose proof (H3 a l targ tid ev errStr) as H';
          intuition; find_rewrite; find_injection; eauto *)
        ]
    end); fail);
    try (find_eapply_lem_hyp split_evidence_fail_runtime; break_exists; ff; fail).
    * eapply split_evidence_res_spec in Heqp as ?;
      eapply split_evidence_state_immut in Heqp;
      break_exists; ff;
      eapply IHe1 in Heqp1; eauto; simpl in *; ff.
    * eapply split_evidence_res_spec in Heqp as ?;
      eapply split_evidence_state_immut in Heqp;
      break_exists; ff.
      eapply sc_immut_invoke_APPR in Heqp1;
      eapply sc_immut_invoke_APPR in Heqp2 as ?;
      ff;
      eapply IHe2 in Heqp2; eauto; simpl in *; ff.

  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      unfold remote_session, doRemote, doRemote_session', do_remote, check_cvm_policy in *;
      try break_match;
      try cvm_monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    unfold session_config_subset in *; intuition.
    * break_exists;  
      repeat find_apply_hyp_hyp; repeat find_rewrite; congruence.
  - break_exists; intuition.
    cvm_monad_unfold; ff.
    * find_eapply_lem_hyp IHt1; ff; ff.
      inversion H6; ff.
    * find_eapply_lem_hyp IHt1; ff; ff;
      try (inversion H6; ff; fail). 
      eapply sc_immut_better in Heqp0 as ?; ff.
      eapply cvm_evidence_type in Heqp0; ff;
      try (inversion H3; ff; fail);
      eapply IHt2; ff.
      eapply session_config_supports_exec_subset; ff.
  - break_exists; intuition;
    cvm_monad_unfold; ff;
    destruct s; simpl in *; ff;
    match goal with
    | H : build_cvm t1 ?st' = _,
      H1 : session_config_supports_exec _ _ t1 ?x,
      H2 : session_config_subset ?x _ |- _ =>
      eapply IHt1 with (st := st') in H1; ff;
      try (inversion H2; ff; fail); ff
    end;
    match goal with
    | H : build_cvm t1 _ = _ |- _ =>
      eapply sc_immut_better in H
    end;
    match goal with
    | H : build_cvm t2 ?st' = _,
      H1 : session_config_supports_exec _ _ t2 ?x,
      H2 : session_config_subset ?x _ |- _ =>
      eapply IHt2 with (st := st') in H1; ff;
      try (inversion H2; ff; fail); ff
    end.
  - break_exists; intuition;
    cvm_monad_unfold; ff;
    destruct s; simpl in *; ff;
    match goal with
    | H : build_cvm t1 ?st' = _,
      H1 : session_config_supports_exec _ _ t1 ?x,
      H2 : session_config_subset ?x _ |- _ =>
      eapply IHt1 with (st := st') in H1; ff;
      try (inversion H2; ff; fail); ff
    end;
    repeat match goal with
    | H : build_cvm t1 _ = _ |- _ =>
      eapply sc_immut_better in H
    | H : parallel_vm_thread _ _ _ _ = _ |- _ =>
      eapply parallel_vm_thread_err_axiom in H; ff; 
      check_num_goals_le 1
    end;
    match goal with
    | H : build_cvm t2 ?st' = _,
      H1 : session_config_supports_exec _ _ t2 ?x,
      H2 : session_config_subset ?x _ |- _ =>
      eapply IHt2 with (st := st') in H1; ff;
      try (inversion H2; ff; fail); ff
    end.
Qed.

Definition manifest_support_session_conf (m : Manifest) (sc : Session_Config)
    : Prop :=
  (forall a, In_set a (m.(asps)) -> 
    forall l targ targid ev,
    (exists res, sc.(aspCb) (asp_paramsC a l targ targid) ev = resultC res) \/
    (exists errStr, sc.(aspCb) (asp_paramsC a l targ targid) ev = errC (Runtime errStr))) /\
  (forall a, In_set a (m.(asps)) -> 
    exists loc, map_get a (m.(ASP_Mapping)) = Some loc).

Fixpoint att_sess_supports_term (ats : Attestation_Session) (t : Term) 
    : Prop :=
  match t with
  | asp a =>
      match a with
      | ENC p => 
        exists v, map_get p (ats.(PubKey_Mapping)) = Some v
      | _ => True
      end
  | att p' t' => 
      exists v, map_get p' (ats.(Plc_Mapping)) = Some v /\
      att_sess_supports_term ats t'
  | lseq t1 t2 =>
      att_sess_supports_term ats t1 /\
      att_sess_supports_term ats t2
  | bseq _ t1 t2 =>
      att_sess_supports_term ats t1 /\
      att_sess_supports_term ats t2
  | bpar _ t1 t2 =>
      att_sess_supports_term ats t1 /\
      att_sess_supports_term ats t2
  end.

Definition well_formed_manifest (m : Manifest) : Prop :=
  (forall a, In_set a (m.(asps)) -> 
    (exists v, map_get a (m.(ASP_Mapping)) = Some v)).

Fixpoint manifest_support_appr (m : Manifest) (e : EvidenceT) : Prop :=
  match e with
  | mt_evt => True
  | nonce_evt _ => In_set check_nonce_aspid (m.(asps))
  | asp_evt p' par e' =>
    let '(asp_paramsC aspid l targ targid) := par in
    In_set aspid (m.(asps)) /\
    manifest_support_appr m e'
  | split_evt e1 e2 =>
    manifest_support_appr m e1 /\
    manifest_support_appr m e2
  end.

Fixpoint manifest_support_term (G : GlobalContext) (m : Manifest) (p : Plc)
    (e : EvidenceT) (t : Term) : Prop :=
  match t with
  | asp a =>
      match a with
      | NULL => True
      | CPY => True
      | SIG => 
          In_set sig_aspid (m.(asps))
      | HSH =>
          In_set hsh_aspid (m.(asps))
      | ENC p =>
          In_set enc_aspid (m.(asps))
      | ASPC _ (asp_paramsC aspid _ _ _) =>
          In_set aspid (m.(asps))
      | APPR => manifest_support_appr m e
      end
  | att p' t' => True
    (* exists m', manifest_support_term m' t' *)
  | lseq t1 t2 =>
      exists e',
      manifest_support_term G m p e t1 /\
      eval G p e t1 = resultC e' /\
      manifest_support_term G m p e' t2
  | bseq s t1 t2 =>
      manifest_support_term G m p (splitEv_T_l s e) t1 /\
      manifest_support_term G m p (splitEv_T_r s e) t2
  | bpar s t1 t2 =>
      manifest_support_term G m p (splitEv_T_l s e) t1 /\
      manifest_support_term G m p (splitEv_T_r s e) t2
  end.

Theorem manifest_support_am_config_impl_am_config: forall t absMan ats G p e,
  well_formed_manifest absMan ->
  manifest_support_term G absMan p e t ->
  ats_context ats = G ->
  att_sess_supports_term ats t ->
  forall aspBin uuid,
  session_config_supports_exec p e
    t 
    (session_config_compiler (mkAM_Man_Conf absMan aspBin uuid) ats).
Proof.
  (* unfold manifest_support_term, well_formed_manifest in *; *)
  induction t; simpl in *; intuition; eauto;
  repeat match goal with
  | H : forall _ _, ?p _ _ -> _,
    H' : ?p _ _ |- _ =>
      eapply H in H'; intuition; eauto
  end; try (repeat eexists; eauto; fail); ff.
  - admit. 
  - split; ff. 
  - unfold manifest_support_term, well_formed_manifest in *; ffa. 
  - repeat eexists; ff.
Admitted.

Lemma places_decomp: forall t1 t2 p tp,
In p (places' t2 (places' t1 [])) -> 
(In p (places tp t1) \/ 
      In p (places tp t2)).
Proof.
intros.

assert (In p (places' t2 []) \/ In p (places' t1 [])).
{
  assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
  { 

    apply In_dec_tplc.
  }
  door.
  +
    eauto.
  +             
    assert (In p (places' t2 [])).
    {
      eapply places_app_cumul.
      apply H.
      eassumption.
    }
    eauto.
}
door.
right.
unfold places.
right.
eauto.

left.
right.
eauto.
Qed.

Fixpoint plc_ev_term_subterms (G : GlobalContext) (p : Plc) (e : EvidenceT) (t : Term) : list (Plc * EvidenceT * Term) :=
  [(
    p, e, t
  )] ++
  match t with
  | asp a => (* nothing is sub ASPs *)
    nil
  | att p' t' => [(p', e, t')]
  | lseq t1 t2 =>
    plc_ev_term_subterms G p e t1 ++ 
    match (eval G p e t1) with
    | resultC e' => plc_ev_term_subterms G p e' t2
    | errC _ => []
    end
  | bseq s t1 t2 =>
    plc_ev_term_subterms G p (splitEv_T_l s e) t1 ++
    plc_ev_term_subterms G p (splitEv_T_r s e) t2
  | bpar s t1 t2 =>
    plc_ev_term_subterms G p (splitEv_T_l s e) t1 ++
    plc_ev_term_subterms G p (splitEv_T_r s e) t2
  end.

Lemma plc_ev_term_subterms_refl : forall G p e t,
  In (p, e, t) (plc_ev_term_subterms G p e t).
Proof.
  induction t; ff.
Qed.

Lemma has_manifest_env_places_env_has_manifest' : forall G t p e env env',
  manifest_generator' G p e t env = resultC env' ->
  forall p' m,
    map_get p' env = Some m ->
    exists m', map_get p' env' = Some m'.
Proof.
  induction t; ff.
  - unfold manifest_update_env_res, asp_manifest_update, 
      aspid_manifest_update in *; ff;
    destEq p p';
    try rewrite mapC_get_works; ff;
    try rewrite map_distinct_key_rw; ff.
  - destEq p' p0; ff;
    eapply IHt with (p' := p') in H; ff.
    rewrite String.eqb_neq in *.


Lemma has_manifest_env_places_env_has_manifest' : forall G t p e env env',
  manifest_generator' G p e t env = resultC env' ->
  (forall p' e' t',
    In (p', e', t') (plc_ev_term_subterms G p e t) ->
    exists m', map_get p' env' = Some m'
  ).
Proof.
  induction t; ff.
  - unfold manifest_update_env_res, asp_manifest_update, 
      aspid_manifest_update in *; ff;
    try rewrite mapC_get_works; ff.
  - break_or_hyp; ff.
    * admit. 
    * eapply IHt; ff; eapply plc_ev_term_subterms_refl.
    find_eapply_lem_hyp IHt; ff.
    unfold asp


  map_get p env' = Some m ->
  (exists m', map_get p env = Some m') \/ 
  In p (places tp t).
Proof.
  induction t; intros.
  - destruct a; ff;
    unfold asp_manifest_update, manifest_update_env_res in *;
    simpl in *; ffa using result_monad_unfold;
    destEq tp p; eauto;
    try rewrite map_distinct_key_rw in *; eauto.
  - simpl in *; intuition; eauto; ff; eauto.
    * eapply IHt in H; ff; ff.
    * eapply IHt in H; ff; ff;
      rewrite String.eqb_eq in *; eauto.
    (* find_apply_hyp_hyp; intuition. *)
  - (* lseq case *)
    ff; result_monad_unfold; ff.
    destruct (map_get p) e0 eqn:E.
    * eapply IHt1 in Heqr; ff; 
      pose proof places'_cumul; ff.
    * eapply IHt2 in H; ff;
      pose proof places_app_cumul; ff.
  - ff; result_monad_unfold; ff.
    destruct (map_get p) e0 eqn:E.
    * eapply IHt1 in Heqr; ff; 
      pose proof places'_cumul; ff.
    * eapply IHt2 in H; ff;
      pose proof places_app_cumul; ff.
  - ff; result_monad_unfold; ff.
    destruct (map_get p) e0 eqn:E.
    * eapply IHt1 in Heqr; ff; 
      pose proof places'_cumul; ff.
    * eapply IHt2 in H; ff;
      pose proof places_app_cumul; ff.
Qed.

Lemma has_manifest_env_places_env_has_manifest : forall G t p tp m env',
  manifest_generator G tp t = resultC env' ->
  map_get p env' = Some m ->
  In p (places tp t).
Proof.
  intros.
  unfold manifest_generator in *.
  result_monad_unfold; ff.
  eapply has_manifest_env_places_env_has_manifest' in H; ff.
Qed.

Lemma places_env_has_manifest : forall t p tp e,
  In p (places tp t) -> 
  forall G env env',
  manifest_generator' G tp e t env = resultC env' ->
  exists m, 
    map_get p env' = Some m.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - simpl in *; intuition; subst.
    unfold manifest_update_env_res, asp_manifest_update,
      aspid_manifest_update in *; ff;
    try (rewrite mapC_get_works; ff; fail).
  - (* at case *)
    ff; eapply map_get_mangen; ff; ff;
    try rewrite String.eqb_refl in *; ff.
  - ff; result_monad_unfold; ff;
    find_eapply_lem_hyp places_decomp; ffa;
    eapply IHt1 in Heqr; ff;
    eapply map_get_mangen; ff.
  - ff; result_monad_unfold; ff;
    find_eapply_lem_hyp places_decomp; ffa;
    eapply IHt1 in Heqr; ff;
    eapply map_get_mangen; ff.
  - ff; result_monad_unfold; ff;
    find_eapply_lem_hyp places_decomp; ffa;
    eapply IHt1 in Heqr; ff;
    eapply map_get_mangen; ff.
Qed.

(* 
(* TODO:  this is likely not provable forall p ... 
   TODO:  perhaps generalize to something like:  
            forall p, In p ((places t1 tp) ++ places e) ?? *)
Lemma asdf : forall t1 t2 tp p' absMan e,
map_get (manifest_generator' tp t2 
            (manifest_generator' tp t1 e)) p' = Some absMan -> 
In p' (places tp t1) ->
exists m', 
map_get (manifest_generator' tp t1 e) p' = Some m' /\ 
manifest_subset m' absMan.
Proof.
  intros.

  assert (Environment_subset 
          (manifest_generator' tp t1 e)
          (manifest_generator' tp t2
            (manifest_generator' tp t1 e))
          
  ).
  {
    eapply manifest_generator_cumul'.
  }

  eapply places_env_has_manifest in H0.
  destruct_conjs.

  unfold Environment_subset in *.

  specialize H1 with (m1 := H0) (p:=p').

  assert (
    exists m2 : Manifest,
       map_get
         (manifest_generator' tp t2
            (manifest_generator' tp t1 e)) p' =
       Some m2 /\ manifest_subset H0 m2
  ).
  {
    eapply H1.
    eassumption.
  }

  destruct_conjs.
  exists H0.
  split; eauto.
  find_rewrite.
  ff.
Qed.

Lemma asdf_easy : forall t1 t2 tp absMan e,
  map_get (manifest_generator' tp t2 
              (manifest_generator' tp t1 e)) tp = Some absMan -> 
              
  exists m', (* p', 
  In p' (places tp t1) /\
  *)
  map_get (manifest_generator' tp t1 e) tp = Some m' /\ 
  manifest_subset m' absMan.
Proof.
  intros; eapply asdf; ff.
Qed.
*)

Lemma manifest_supports_appr_sub : forall m1 m2 e,
  manifest_subset m1 m2 ->
  manifest_support_appr m1 e -> 
  manifest_support_appr m2 e.
Proof.
  induction e; ff.
Qed.

Lemma manifest_supports_term_sub : forall m1 m2 t p e G,
  manifest_subset m1 m2 ->
  manifest_support_term G m1 p e t -> 
  manifest_support_term G m2 p e t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; ff; try eapply manifest_supports_appr_sub; ff.
  find_eapply_lem_hyp IHt1; ff.
Qed.

Lemma env_subset_man_subset : forall e1 e2 p m m',
  Environment_subset e1 e2 -> 
  map_get p e1 = Some m -> 
  map_get p e2 = Some m' -> 
  manifest_subset m m'.
Proof.
  unfold Environment_subset in *; ff;
  specialize H with (m1:= m) (p:=p);
  intuition; ff.
Qed.

Theorem man_gen_old_always_supports : forall G t t' tp p e env env' absMan,
  well_formed_context G ->
  manifest_generator' G tp e t env = resultC env' ->
  (forall p' e' t',
    In (p', e', t') (plc_ev_term_subterms G p e t) ->

  )
  map_get p env' = Some absMan ->
  (* NOTE: Big issue here, it only holds for the EVIDENCE that it 
  should be receiving! *)
  In p (places tp t) ->
  In t' (place_terms t tp p) ->
  manifest_support_term G absMan p e t'.
Proof.
  induction t; ff;
  try rewrite String.eqb_eq in *;
  try rewrite String.eqb_refl in *;
  ff.
  - repeat break_or_hyp; ff;
    unfold well_formed_context in *;
    ff.
  - result_monad_unfold; ff.

  induction t; intuition.
  - simpl in *.
    repeat (try break_match; 
      unfold asp_manifest_update, manifest_update_env, 
        aspid_manifest_update in *;
      subst; simpl in *; intuition; eauto; try congruence;
      repeat find_rewrite;
      repeat find_injection;
      simpl in * );
    try (rewrite mapC_get_works in *; simpl in *; repeat find_injection; simpl in *; intuition; eauto);
    try (eapply manadd_In_add).

  - simpl in *; intuition; subst; eauto. 
    * rewrite String.eqb_refl in *; simpl in *; intuition; subst; eauto;
      simpl in *; eauto.
    * ff; intuition; subst; eauto; simpl in *; eauto. 
    * ff; intuition; subst; simpl in *; eauto.

  - (* lseq case *)

  ff.
  ff.
  +
  door; try solve_by_inversion.
  subst.
  ff.
  assert (tp = p).
  {
    rewrite String.eqb_eq in *; ff.
  }
  subst.



  split.
    ++

    find_apply_lem_hyp asdf_easy.
    destruct_conjs.

    eapply manifest_supports_term_sub.
    eassumption.


    eapply IHt1.
    eassumption.
    eauto.
    apply top_plc_refl.

  ++
  eapply IHt2.
  eassumption.
  eauto.
  apply top_plc_refl.


  + (* tp <> p *)
    destruct H0.
    ++
      subst.
      rewrite String.eqb_refl in *; ff.
    ++
      assert ((In t' (place_terms t1 tp p)) \/ (In t' (place_terms t2 tp p))).
      {
        eapply in_app_or; eauto.
      }
      clear H1.

      destruct H2.
      +++ (* In t' (place_terms t1 tp p) *)
        assert (In p (places tp t1)).
        {
          apply in_plc_term.
          eapply in_not_nil.
          eassumption.
        }
          find_apply_lem_hyp asdf.
          ++++
            destruct_conjs.
            eapply manifest_supports_term_sub.
            eassumption.
            eapply IHt1.
            eassumption.
            eauto.
            eassumption.

          ++++
            right.
            unfold places in *.
            invc H2.
            +++++
              rewrite String.eqb_refl in Heqb.
              solve_by_inversion.
            +++++
              eauto.
      +++ (* In t' (place_terms t2 tp p) *)
        simpl.

        assert (In p (places tp t2)).
      {
        apply in_plc_term.
        eapply in_not_nil; eauto.
      }

        eapply IHt2.
        ++++
          eassumption.
        ++++
          right.
          unfold places in H2.
          eauto.
          invc H2.
            +++++
              rewrite String.eqb_refl in *.
              solve_by_inversion.
            +++++
              eassumption.
          ++++
            eassumption.

  - (* bseq case*) 

  ff.
  ff.
  +
  door; try solve_by_inversion.
  subst.
  ff.
  assert (tp = p).
  {
    eapply String.eqb_eq; eauto.
  }
  subst.

  split.
    ++
      find_apply_lem_hyp asdf_easy.
      destruct_conjs.
  
      eapply manifest_supports_term_sub.
      eassumption.
  
  
      eapply IHt1.
      eassumption.
      eauto.
      apply top_plc_refl.

    ++
      eapply IHt2.
      eassumption.
      eauto.
      apply top_plc_refl.

  + (* tp <> p *)
    destruct H0.
    ++
      subst.
      rewrite String.eqb_refl in *.
      solve_by_inversion.
    ++
      assert ((In t' (place_terms t1 tp p)) \/ (In t' (place_terms t2 tp p))).
      {
        eapply in_app_or; eauto.
      }
      clear H1.
    
      destruct H2.
      +++ (* In t' (place_terms t1 tp p) *)
        assert (In p (places tp t1)).
        {
          apply in_plc_term.
          eapply in_not_nil.
          eassumption.
        }
          find_apply_lem_hyp asdf.
          ++++
            destruct_conjs.
        
            eapply manifest_supports_term_sub.
            eassumption.
            eapply IHt1.
            eassumption.
            eauto.
            eassumption.
      
          ++++
            right.
            unfold places in *.
            invc H2.
            +++++
              rewrite String.eqb_refl in Heqb.
              solve_by_inversion.
            +++++
              eauto.
      +++ (* In t' (place_terms t2 tp p) *)
        simpl.
    
        assert (In p (places tp t2)).
      {
        apply in_plc_term.
        eapply in_not_nil; eauto.
      }
    
        eapply IHt2.
        ++++
          eassumption.
        ++++
          right.
          unfold places in H2.
          eauto.
          invc H2.
          +++++
            rewrite String.eqb_refl in *.
            solve_by_inversion.
          +++++
            eassumption.
        ++++
          eassumption.


  - (* bpar case*) 

  ff.
  ff.
  +
  door; try solve_by_inversion.
  subst.
  ff.
  assert (tp = p).
  {
    eapply String.eqb_eq; eauto.
  }
  subst.

  split.
    ++
      find_apply_lem_hyp asdf_easy.
      destruct_conjs.
  
      eapply manifest_supports_term_sub.
      eassumption.
  
  
      eapply IHt1.
      eassumption.
      eauto.
      apply top_plc_refl.

    ++
      eapply IHt2.
      eassumption.
      eauto.
      apply top_plc_refl.

  + (* tp <> p *)
    destruct H0.
    ++
      subst.
      rewrite String.eqb_refl in *.
      solve_by_inversion.
    ++
      assert ((In t' (place_terms t1 tp p)) \/ (In t' (place_terms t2 tp p))).
      {
        eapply in_app_or; eauto.
      }
      clear H1.
    
      destruct H2.
      +++ (* In t' (place_terms t1 tp p) *)
        assert (In p (places tp t1)).
        {
          apply in_plc_term.
          eapply in_not_nil.
          eassumption.
        }
          find_apply_lem_hyp asdf.
          ++++
            destruct_conjs.
        
            eapply manifest_supports_term_sub.
            eassumption.
            eapply IHt1.
            eassumption.
            eauto.
            eassumption.
      
          ++++
            right.
            unfold places in *.
            invc H2.
            +++++
              rewrite String.eqb_refl in Heqb.
              solve_by_inversion.
            +++++
              eauto.
      +++ (* In t' (place_terms t2 tp p) *)
        simpl.
    
        assert (In p (places tp t2)).
      {
        apply in_plc_term.
        eapply in_not_nil; eauto.
      }
    
        eapply IHt2.
        ++++
          eassumption.
        ++++
          right.
          unfold places in H2.
          eauto.
          invc H2.
          +++++
            rewrite String.eqb_refl in *.
            solve_by_inversion.
          +++++
            eassumption.
        ++++
          eassumption.
Qed.

Lemma att_sess_supports_place_terms : forall ats t tp p t',
  att_sess_supports_term ats t ->
  In t' (place_terms t tp p) ->
  att_sess_supports_term ats t'.
Proof.
  induction t; simpl in *; intuition; eauto;
  repeat (ff; subst; simpl in *; repeat find_rewrite;
    repeat find_injection; intuition; eauto).
  - break_exists; intuition.
    eapply IHt in H2; eauto.
  - find_eapply_lem_hyp in_app_iff; intuition; eauto.
  - find_eapply_lem_hyp in_app_iff; intuition; eauto.
  - find_eapply_lem_hyp in_app_iff; intuition; eauto.
Qed.

(* Lemma man_gen_yields_wf_manifests : forall t tp p absMan,
  (* well_formed_manifest backMan -> *)
  map_get (manifest_generator tp t) p = Some absMan ->
  well_formed_manifest absMan.
Proof.
  induction t; simpl in *; intuition; eauto;
  repeat ff; intuition; simpl in *.
  - unfold well_formed_manifest; intuition. 
    unfold asp_manifest_update; simpl in *; ff; intuition;
    subst; eauto. *)

Theorem manifest_generator_compiler_soundness_distributed : forall t tp p absMan uuid aspBin sc att_sess,
  map_get (manifest_generator t tp) p = Some absMan ->
  well_formed_manifest absMan ->
  manifest_support_session_conf absMan sc ->
  att_sess_supports_term att_sesplit_evt t ->
  session_config_compiler (mkAM_Man_Conf absMan aspBin uuid) att_sesplit_evt = sc ->
  forall st,
    session_config_subset sc (st.(st_config)) ->  
    (  forall t', 
         In t' (place_terms t tp p) -> 
        (exists st', 
        
        build_cvm (copland_compile t') st = (resultC tt, st')) \/
        
        (exists st' errStr,
        build_cvm (copland_compile t') st = (errC (dispatch_error (Runtime errStr)), st'))
    ).
Proof.
  intros.
  assert (In p (places tp t)) by 
            (eapply has_manifest_env_places_env_has_manifest; eauto);
  subst.
  eapply well_formed_am_config_impl_executable; eauto.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config; eauto.
    * eapply man_gen_old_always_supports; eauto.
    * eapply att_sess_supports_place_terms; eauto.
  Unshelve. eapply default_uuid.
Qed.

Close Scope cop_ent_scope.

Lemma map_get_some_impl_in : forall (A B : Type) `{EqClass A} (m : Maps.Map A B) p v,
  map_get p m = Some v -> 
  In p (map fst m).
Proof.
  induction m; simpl in *; intuition; try congruence;
  repeat break_match; repeat find_injection; eauto;
  rewrite eqb_eq in *; eauto.
Qed.

Lemma map_get_env_union_key : forall env env' p m,
  map_get (Manifest_Union.environment_union env env') p = Some m ->
  In p (map fst env) \/ In p (map fst env').
Proof.
  induction env; simpl in *; intuition; eauto.
  - right; eapply map_get_some_impl_in; eauto. 
  - unfold Manifest_Union.env_union_helper,
      Manifest_Union.environment_union'' in *;
    ff; simpl in *; repeat find_rewrite;
    repeat find_injection; simpl in *;
    subst.
    * destEq a0 p; eauto;
      erewrite map_distinct_key_rw in *;
      eauto; find_apply_hyp_hyp;
      eauto; intuition.
    * destEq a0 p; eauto;
      erewrite map_distinct_key_rw in *;
      eauto; find_apply_hyp_hyp;
      eauto; intuition.
Qed.

(* Global Hint Resolve manifest_subset_union_l : core. *)
Lemma manifest_env_union_all_cases : forall env env' p m,
  NoDup (map fst env) ->
  NoDup (map fst env') ->
  map_get (Manifest_Union.environment_union env env') p = Some m ->
  ((map_get p env = Some m) \/ (map_get p env' = Some m) \/
  (exists m1 m2, map_get p env = Some m1 /\ 
    map_get p env' = Some m2 /\ Manifest_Union.manifest_union_asps m2 m1 = m)).
Proof.
  induction env; simpl in *; intuition; eauto;
  try congruence.
  - simpl in *; invc H; 
    unfold Manifest_Union.env_union_helper,
      Manifest_Union.environment_union'' in *;
    repeat break_match; simpl in *; intuition; eauto; try congruence;
    try (try rewrite String.eqb_eq in *; subst;
    try rewrite String.eqb_neq in *; subst;
    try rewrite mapC_get_works in *; repeat find_injection;
    try rewrite map_distinct_key_rw in *; repeat find_injection;
    eauto; fail); eauto.
    assert (In a0 (map fst env) \/ In a0 (map fst env')). {
      eapply map_get_env_union_key; eauto.
    }
    intuition.
    rewrite String.eqb_eq in *; subst.
    rewrite mapC_get_works in *; repeat find_injection;
    eapply IHenv in Heqo; intuition; eauto;
    clear IHenv.
    * eapply map_get_some_impl_in in H; congruence.
    * right. right.
      repeat eexists; eauto.
    * break_exists; intuition. 
      eapply map_get_some_impl_in in H1; congruence.
Qed.

Lemma manifest_env_union_works : forall env env' p m,
  map_get (Manifest_Union.environment_union env env') p = Some m ->
  (exists m', map_get p env = Some m' /\ manifest_subset m' m) \/
  (exists m', map_get p env' = Some m' /\ manifest_subset m' m).
Proof.
  induction env; simpl in *; intuition; eauto;
  try congruence.
  - right; eauto; eexists; intuition; eauto;
    eapply manifest_subset_refl.
  - destruct (String.eqb a0 p) eqn:E; simpl in *;
    unfold Manifest_Union.env_union_helper,
      Manifest_Union.environment_union'' in *;
    repeat break_match; simpl in *; intuition; eauto; try congruence;
    try rewrite String.eqb_eq in *; subst.
    * erewrite mapC_get_works in H; find_injection; eauto.
    * erewrite mapC_get_works in H; find_injection; 
      left; eexists; intuition; eapply manifest_subset_refl.
    * eapply IHenv; eapply mapC_get_distinct_keys_from_set in H; 
      eauto; intuition; subst; rewrite String.eqb_refl in E; congruence.
    * eapply IHenv; eapply mapC_get_distinct_keys_from_set in H; 
      eauto; intuition; subst; rewrite String.eqb_refl in E; congruence.
Qed.

Lemma man_env_union_not_none_fwd : forall env env' p,
  (map_get p env <> None \/ map_get p env' <> None) ->
  map_get (Manifest_Union.environment_union env env') p <> None.
Proof.
  induction env; destruct env'; simpl in *; intuition; eauto.
  - destruct (String.eqb a0 p) eqn:E; simpl in *; intuition; eauto;
    try rewrite String.eqb_eq in *; subst; eauto;
    unfold Manifest_Union.env_union_helper,
      Manifest_Union.environment_union'' in *; simpl in *;
    repeat break_match; simpl in *; intuition; eauto;
    try (rewrite mapC_get_works in H0; congruence);
    rewrite map_distinct_key_rw in H0; intuition; eauto;
    subst; rewrite String.eqb_refl in E; congruence.
  - destruct (String.eqb a0 p) eqn:E; simpl in *; intuition; eauto;
    try rewrite String.eqb_eq in *; subst; eauto;
    unfold Manifest_Union.env_union_helper,
      Manifest_Union.environment_union'' in *; simpl in *;
    repeat break_match; simpl in *; intuition; eauto;
    try (rewrite mapC_get_works in H0; congruence);
    rewrite map_distinct_key_rw in H0; intuition; eauto;
    subst; rewrite String.eqb_refl in E; congruence.
  - destruct (String.eqb a0 p) eqn:E, (String.eqb a p) eqn:E2;
    simpl in *; intuition; eauto;
    try rewrite String.eqb_eq in *; subst; eauto;
    unfold Manifest_Union.env_union_helper,
      Manifest_Union.environment_union'' in *; simpl in *;
    repeat break_match; simpl in *; intuition; eauto;
    try (rewrite mapC_get_works in H0; congruence);
    rewrite map_distinct_key_rw in H0; intuition; eauto;
    try (subst; rewrite String.eqb_refl in E; congruence).
    * pose proof (IHenv ((p, b0) :: env') p);
      simpl in *; rewrite String.eqb_refl in *; intuition. 
    * pose proof (IHenv ((p, b0) :: env') p);
      simpl in *; rewrite String.eqb_refl in *; intuition. 
    * pose proof (IHenv ((a, b0) :: env') p);
      simpl in *; find_rewrite; intuition. 
    * pose proof (IHenv ((a, b0) :: env') p);
      simpl in *; find_rewrite; intuition. 
Qed.
Global Hint Resolve man_env_union_not_none_fwd : core.

Lemma man_env_union_not_none_rev : forall env env' p,
  map_get (Manifest_Union.environment_union env env') p <> None ->
  (map_get p env <> None \/ map_get p env' <> None).
Proof.
  induction env; destruct env'; simpl in *; intuition; eauto.
  - destruct (String.eqb a0 p) eqn:E; simpl in *; intuition; eauto;
    try rewrite String.eqb_eq in *; subst; eauto;
    unfold Manifest_Union.env_union_helper,
      Manifest_Union.environment_union'' in *; simpl in *;
    repeat break_match; simpl in *; intuition; eauto;
    try (left; intuition; congruence).
    * rewrite map_distinct_key_rw in H; intuition; eauto;
      try eapply IHenv in H; intuition; eauto;
      subst; rewrite String.eqb_refl in E; congruence.
    * rewrite map_distinct_key_rw in H; intuition; eauto;
      try eapply IHenv in H; intuition; eauto;
      subst; rewrite String.eqb_refl in E; congruence.
  - destruct (String.eqb a0 p) eqn:E; simpl in *; intuition; eauto;
    try rewrite String.eqb_eq in *; subst; eauto;
    unfold Manifest_Union.env_union_helper,
      Manifest_Union.environment_union'' in *; simpl in *;
    repeat break_match; simpl in *; intuition; eauto;
    try (left; intuition; congruence);
    try (right; intuition; congruence);
    try rewrite String.eqb_eq in *; subst; eauto;
    intuition; eauto.
    * rewrite map_distinct_key_rw in H; intuition; eauto;
      try eapply IHenv in H; intuition; eauto;
      simpl in *; find_rewrite; intuition;
      subst; rewrite String.eqb_refl in E; congruence.
    * rewrite map_distinct_key_rw in H; intuition; eauto;
      try eapply IHenv in H; intuition; eauto;
      simpl in *; find_rewrite; intuition;
      subst; rewrite String.eqb_refl in E; congruence.
Qed.
Global Hint Resolve man_env_union_not_none_rev : core.

Lemma man_env_union_not_none : forall env env' p,
  map_get (Manifest_Union.environment_union env env') p <> None <->
  (map_get p env <> None \/ map_get p env' <> None).
Proof.
  split; eauto.
Qed.
Global Hint Resolve man_env_union_not_none : core.

Lemma manifest_env_union_always_subset : forall env env' p m,
  map_get (Manifest_Union.environment_union env env') p = Some m ->
  (forall m', map_get p env = Some m' -> manifest_subset m' m) /\
  (forall m', map_get p env' = Some m' -> manifest_subset m' m).
Proof.
  induction env; simpl in *; intuition; eauto; try congruence.
  (* - find_rewrite; find_injection; eapply manifest_subset_refl. *)
  - destruct (String.eqb a0 p) eqn:E; simpl in *;
    unfold Manifest_Union.env_union_helper, 
      Manifest_Union.environment_union'' in *;
    simpl in *; eauto; try rewrite String.eqb_eq in E; subst.
    * repeat break_match; simpl in *; find_injection; 
      rewrite mapC_get_works in H; find_injection; eauto;
      eapply manifest_subset_refl.
    * repeat break_match; simpl in *.
      + eapply mapC_get_distinct_keys_from_set in H; 
        eauto; intuition; subst; eauto.
        eapply IHenv in H; intuition.
        rewrite String.eqb_refl in E; congruence.
      + eapply mapC_get_distinct_keys_from_set in H; 
        eauto; intuition; subst; eauto.
        eapply IHenv in H; intuition.
        rewrite String.eqb_refl in E; congruence.
  - destruct (String.eqb a0 p) eqn:E; simpl in *;
    unfold Manifest_Union.env_union_helper, 
      Manifest_Union.environment_union'' in *;
    simpl in *; eauto; try rewrite String.eqb_eq in E; subst.
    * repeat break_match; simpl in *.
      ** rewrite mapC_get_works in H; find_injection. 
        eapply IHenv in Heqo; intuition.
        eapply H1 in H0.
        eapply manifest_subset_trans; eauto.
      ** rewrite mapC_get_works in H; find_injection. 
        edestruct (man_env_union_not_none_fwd); intuition; eauto.
        right; intuition; congruence.
    * repeat break_match; simpl in *.
      ** eapply mapC_get_distinct_keys_from_set in H; 
        intuition; eauto.
        eapply IHenv in H; intuition.
        subst; rewrite String.eqb_refl in *; congruence.
      ** eapply mapC_get_distinct_keys_from_set in H; 
        intuition; eauto. 
        eapply IHenv in H; intuition.
        subst; rewrite String.eqb_refl in *; congruence.
Qed. 
Global Hint Resolve manifest_env_union_always_subset : core.

Lemma manifest_env_union_map_one_fwd : forall env env' p m,
  map_get (Manifest_Union.environment_union env env') p = Some m ->
  (exists m', (map_get p env = Some m' \/
  map_get p env' = Some m')).
Proof.
  induction env; simpl in *; intuition; eauto;
  destruct (String.eqb a0 p) eqn:E; simpl in *; intuition; eauto.
  unfold Manifest_Union.env_union_helper, Manifest_Union.environment_union'' in H;
  simpl in *; repeat break_match; simpl in *; intuition; eauto;
  break_exists.
  - eapply mapC_get_distinct_keys_from_set in H; intuition; eauto;
    subst; rewrite String.eqb_refl in *; congruence. 
  - eapply mapC_get_distinct_keys_from_set in H; intuition; eauto;
    subst; rewrite String.eqb_refl in *; congruence.
Qed.
Global Hint Resolve manifest_env_union_map_one_fwd : core.

Lemma manifest_env_union_map_one : forall env env' p,
  (exists m, map_get (Manifest_Union.environment_union env env') p = Some m) <->
  (exists m', (map_get p env = Some m' \/
  map_get p env' = Some m')).
Proof.
  intuition;
  pose proof (man_env_union_not_none env env' p);
  break_exists; repeat find_rewrite.
  - destruct (map_get env p); eauto;
    destruct (map_get env' p); eauto.
    assert (Some x <> None) by congruence.
    rewrite H0 in H1; intuition.
  - destruct H; repeat find_rewrite;
    destruct (map_get (Manifest_Union.environment_union env env') p);
    eauto; assert (Some x <> None) by congruence;
    assert (@None Manifest <> None) by (erewrite H0; eauto);
    congruence.
Qed.
(* 
  split.
  * induction env; simpl in *; intuition; eauto;
    break_let; simpl in *; destruct a;
    find_injection;
    destruct (eqb p0 p) eqn:E; simpl in *; intuition; eauto.
    unfold Manifest_Union.env_union_helper, Manifest_Union.environment_union'' in H;
    simpl in *; repeat break_match; simpl in *; intuition; eauto;
    break_exists.
    - eapply mapC_get_distinct_keys_from_set in H; intuition; eauto;
      subst; rewrite eqb_refl in *; congruence. 
    - eapply mapC_get_distinct_keys_from_set in H; intuition; eauto;
      subst; rewrite eqb_refl in *; congruence.
  * intuition; break_exists; eauto;
    pose proof (man_env_union_not_none env env' p);
    destruct (map_get (Manifest_Union.environment_union env env') p);
    intuition; find_rewrite; eauto; exfalso;
    try (eapply H1; intuition; congruence).
    - eapply H1; intuition; congruence. 
    - eapply H2; intuition; congruence. 
Qed. *)
Global Hint Resolve manifest_env_union_map_one : core.

Lemma manifest_part_of_fold_impl_fold : forall env_start p m',
  map_get p env_start = Some m' ->
  (forall envs, 
    exists m,
    map_get (fold_right Manifest_Union.environment_union env_start envs) p = Some m /\
    manifest_subset m' m
  ).
Proof.
  intuition.
  induction envs; simpl in *; intuition; eauto.
  - exists m'; intuition; eapply manifest_subset_refl. 
  - break_exists; intuition; simpl in *.
    pose proof (manifest_env_union_map_one a (fold_right Manifest_Union.environment_union env_start envs) p).
    assert ((exists m : Manifest, map_get (Manifest_Union.environment_union a (fold_right Manifest_Union.environment_union env_start envs)) p = Some m)) by (rewrite H0; eauto).
    clear H0.
    break_exists.
    eapply manifest_env_union_always_subset in H0 as H'; intuition.
    exists x0; intuition; eauto.
Qed.
Global Hint Resolve manifest_part_of_fold_impl_fold : core.

Lemma manifest_part_of_fold_ind_impl_fold : forall envs env p m',
  In env envs ->
  map_get p env = Some m' ->
  (forall env_start, 
    exists m,
    map_get (fold_right Manifest_Union.environment_union env_start envs) p = Some m /\
    manifest_subset m' m
  ).
Proof.
  induction envs; intros; eauto with *; simpl in *; eauto; intuition;
  subst; eauto.
  - pose proof (manifest_env_union_map_one env (fold_right Manifest_Union.environment_union env_start envs) p). 
    assert ((exists m' : Manifest, map_get p env = Some m' \/ map_get (fold_right Manifest_Union.environment_union env_start envs) p = Some m')) by (rewrite H0; eauto).
    rewrite <- H in H1.
    break_exists.
    eapply manifest_env_union_always_subset in H1 as H'';
    destruct H''.
    eapply H2 in H0 as H'.
    exists x; intuition; eauto.
  - pose proof (IHenvs _ _ _ H1 H0 env_start).
    break_exists; intuition; eauto.
    pose proof (manifest_env_union_map_one a (fold_right Manifest_Union.environment_union env_start envs) p).
    assert ((exists m' : Manifest, map_get p a = Some m' \/ map_get (fold_right Manifest_Union.environment_union env_start envs) p = Some m')) by (rewrite H2; eauto).
    rewrite <- H in H4.
    break_exists.
    eapply manifest_env_union_always_subset in H4 as H'.
    destruct H'.
    eapply H6 in H2 as H''.
    exists x0; intuition; eauto.
Qed.
Global Hint Resolve manifest_part_of_fold_ind_impl_fold : core.
(* 
Lemma manifest_part_of_fold_ind_impl_fold : forall env_start envs p m,
  map_get (fold_right Manifest_Union.environment_union env_start envs) p = Some m ->
  (forall env,
      In env envs ->
      exists m', map_get env p = Some m'
  ). *)

Lemma manifest_fold_env_union_subsumes : forall envs env_start p m,
  map_get (fold_right Manifest_Union.environment_union env_start envs) p = Some m ->
  ((forall m',
    map_get p env_start = Some m' ->
    manifest_subset m' m) /\
  (forall env m', 
    In env envs ->
    map_get p env = Some m' ->
    manifest_subset m' m)).
Proof.
  intuition.
  - pose proof (manifest_part_of_fold_impl_fold env_start p m' H0 envs).
    setoid_rewrite H in H1.
    break_exists; intuition; find_injection; eauto.
  - pose proof (manifest_part_of_fold_ind_impl_fold envs env p m' H0 H1 env_start). 
    setoid_rewrite H in H2;
    break_exists; intuition; find_injection; eauto.
Qed.
Global Hint Resolve manifest_fold_env_union_subsumes : core.

Lemma exists_weaken : forall {T : Type} (P Q : T -> Prop),
  (exists x, P x \/ Q x) ->
  (exists x, P x) \/ (exists x, Q x).
Proof.
  intuition.
  break_exists; intuition; eauto.
Qed.

Lemma manifest_env_list_union_subsumes : forall envs p m,
  map_get (env_list_union envs) p = Some m ->
  (forall env m', 
    In env envs ->
    map_get p env = Some m' ->
    manifest_subset m' m).
Proof.
  intros envs p m HM;
  eapply manifest_fold_env_union_subsumes in HM; 
  intuition.
Qed.
Global Hint Resolve manifest_env_list_union_subsumes : core.

(* Lemma manifest_env_list_union_exists : forall envs p m,
  map_get (env_list_union envs) p = Some m ->
  (forall env, 
    In env envs ->
    exists m', map_get env p = Some m').
Proof.
  intros.
  unfold env_list_union in *.

  induction envs; eauto with *; simpl in *; intuition; subst; eauto.
  - pose proof (manifest_env_union_map_one env (env_list_union envs) p).
    assert ((exists m : Manifest, map_get (Manifest_Union.environment_union env (env_list_union envs)) p = Some m)). 
    rewrite H.
    rewrite H0 in H1.
    break_exists; intuition; eauto.
    clear H2 H3.
    eapply IHenvs in H0; eauto. *)

Lemma mangen_plcTerm_list_spec : forall ts t tp,
  In (t, tp) ts ->
  In (manifest_generator t tp) (manifest_generator_plcTerm_list ts).
Proof.
  induction ts; simpl in *; intuition; subst; eauto;
  find_injection; eauto.
Qed.
Global Hint Resolve mangen_plcTerm_list_spec : core.

Lemma mangen_plcTerm_list_exists : forall ts t tp p m,
  In (t, tp) ts ->
  map_get (manifest_generator t tp) p = Some m ->
  exists m', map_get (mangen_plcTerm_list_union ts) p = Some m'.
Proof.
  intuition.
  unfold mangen_plcTerm_list_union.
  induction ts; simpl in *; intuition; subst; eauto.
  - erewrite manifest_env_union_map_one; eauto. 
  - erewrite manifest_env_union_map_one; 
    break_exists; eauto. 
Qed.
Global Hint Resolve mangen_plcTerm_list_exists : core.

Lemma mangen_plcTerm_list_subsumes : forall ts p m,
  map_get (mangen_plcTerm_list_union ts) p = Some m ->
  (forall t tp,
    In (t,tp) ts ->
    (forall m', 
      map_get (manifest_generator t tp) p = Some m' ->
      manifest_subset m' m
    )
  ).
Proof.
  intuition; unfold mangen_plcTerm_list_union in *.
  eapply (manifest_env_list_union_subsumes _ _ _ H
    (manifest_generator t tp) m'); eauto.
Qed.
Global Hint Resolve mangen_plcTerm_list_subsumes : core.

Lemma mangen_plcTerm_subset_end_to_end_mangen : forall ts t tp,
  In (t, tp) ts ->
  (forall m m' p,
    map_get (mangen_plcTerm_list_union ts) p = Some m' ->
    forall ls cm env, 
      end_to_end_mangen cm ls ts = resultC env ->
      map_get p env = Some m ->
      manifest_subset m' m
  ).
Proof.
  intuition; unfold end_to_end_mangen in *; ff;
  find_eapply_lem_hyp manifest_env_union_always_subset; intuition.
  eapply map_map_get_works in H0; eapply H3 in H0;
  unfold manifest_subset, add_compat_map_manifest in *;
  intuition; simpl in *; destruct m, m'; eauto.
Qed.
Global Hint Resolve mangen_plcTerm_subset_end_to_end_mangen : core.

Lemma mangen_subset_end_to_end_mangen : forall ts t tp,
  In (t, tp) ts ->
  (forall m m' p,
    map_get (manifest_generator t tp) p = Some m' ->
    forall ls cm env, 
      end_to_end_mangen cm ls ts = resultC env ->
      map_get p env = Some m ->
      manifest_subset m' m
  ).
Proof.
  intuition.
  assert (exists m'', map_get (mangen_plcTerm_list_union ts) p = Some m''). eapply mangen_plcTerm_list_exists; eauto.
  break_exists.
  pose proof (mangen_plcTerm_list_subsumes ts p x H3 t tp H _ H0);
  eauto.
Qed.
Global Hint Resolve mangen_subset_end_to_end_mangen : core.

Lemma always_a_man_gen_exists : forall t p tp,
  In p (places tp t) ->
  exists m', map_get (manifest_generator t tp) p = Some m'.
Proof.
  intuition.
  pose proof (places_env_has_manifest t p tp e_empty);
  intuition.
Qed.
Global Hint Resolve always_a_man_gen_exists : core.

Lemma mangen_exists_end_to_end_mangen : forall ts ls p m,
  forall cm env,
    end_to_end_mangen cm ls ts = resultC env ->
    map_get p env = Some m ->
  (forall t tp,
    In (t, tp) ts ->
    In p (places tp t) ->
    (forall t',
      In t' (place_terms t tp p) ->
      exists m', map_get (manifest_generator t tp) p = Some m'
    )
  ).
Proof.
  intuition.
Qed.
Global Hint Resolve mangen_exists_end_to_end_mangen : core.

(* Lemma lib_supports_manifest_subset : forall al m m',
  lib_supports_manifest al m -> 
  manifest_subset m' m -> 
  lib_supports_manifest al m'.
Proof.
  unfold lib_supports_manifest, manifest_subset; intuition.
Qed.
Global Hint Resolve lib_supports_manifest_subset : core.

Lemma man_supports_am_man_subset: forall m m' ac,
  manifest_support_am_config m ac -> 
  manifest_subset m' m ->
  manifest_support_am_config m' ac.
Proof.
  unfold manifest_support_am_config, manifest_subset;
  intuition.
Qed.
Global Hint Resolve man_supports_am_man_subset : core.

Lemma mapC_get_filtered_impossible : forall T `{EqClass T} B (a : B) (aid : T) al f,
  map_get (minify_mapC al f) aid = Some a ->
  f aid = false ->
  False.
Proof.
  induction al; intuition; simpl in *; try congruence.
  break_if; simpl in *; intuition; ff; eauto.
  rewrite eqb_eq in Heqb1; subst; congruence.
Qed.
Global Hint Resolve mapC_get_filtered_impossible : core.

Lemma mapD_get_filtered_impossible : forall T B `{EqClass T, EqClass B} (a : B) (aid : T) al f,
  map_get (minify_mapD al f) aid = Some a ->
  f aid = false ->
  False.
Proof.
  induction al; intuition; simpl in *; try congruence.
  break_if; simpl in *; intuition; ff; eauto.
  rewrite eqb_eq in Heqb1; subst; congruence.
Qed.
Global Hint Resolve mapD_get_filtered_impossible : core.

Lemma mapC_get_subset : forall T `{EqClass T} B (a : B) (aid : T) al s1 s2,
  (forall i : T, In i s1 -> In i s2) ->
  map_get (minify_mapC al (fun x : T => if in_dec_set x s1 then true else false)) aid = Some a ->
  map_get (minify_mapC al (fun x : T => if in_dec_set x s2 then true else false)) aid = Some a.
Proof.
  intuition.
  induction al; repeat ff.
  - (* Provable because aid \not\in s1 but map get got some*)
    intuition.
    destruct H;
    rewrite eqb_eq in Heqb2; subst.
    eapply mapC_get_filtered_impossible in H1; intuition.
    break_if; intuition.
  - pose proof (H0 t i); intuition.
Qed.
Global Hint Resolve mapC_get_subset : core.

Lemma mapD_get_subset : forall T B `{EqClass T, EqClass B} (a : B) (aid : T) al s1 s2,
  (forall i : T, In i s1 -> In i s2) ->
  map_get (minify_mapD al (fun x : T => if in_dec_set x s1 then true else false)) aid = Some a ->
  map_get (minify_mapD al (fun x : T => if in_dec_set x s2 then true else false)) aid = Some a.
Proof.
  intuition.
  induction al; repeat ff.
  - (* Provable because aid \not\in s1 but map get got some*)
    intuition.
    destruct H;
    rewrite eqb_eq in Heqb2; subst.
    eapply mapD_get_filtered_impossible in H2; intuition.
    break_if; intuition.
  - pose proof (H1 t i); intuition.
Qed.
Global Hint Resolve mapD_get_subset : core.
*)
(* 
Lemma supports_am_mancomp_subset: forall m m' att_sesplit_evt aspBin uuid sc,
  session_config_subset 
    (session_config_compiler (mkAM_Man_Conf m aspBin uuid) att_sess) sc -> 
  manifest_subset m' m ->
  session_config_subset 
    (session_config_compiler (mkAM_Man_Conf m' aspBin uuid) att_sess) sc.
Proof.
  intuition.
  unfold session_config_subset, manifest_subset in *;
  intuition; simpl in *; eauto;
  repeat break_match; simpl in *; repeat ff; intuition; subst; eauto;
  unfold res_bind in *;
  try congruence; eauto; try find_injection;
  repeat break_match; simpl in *; intuition; subst; eauto;
  try congruence.
  - find_apply_hyp_hyp; intuition. 
    eapply H1; ff; eauto; try congruence;
    repeat find_rewrite; try congruence.
  find_apply_hyp_hyp.
  try match goal with
  | [ H : forall x : ?t, In_set _ _ -> _ , H1 : map_get (minify_mapC _ (fun x : ?t => _)) _ = Some _ , H2 : forall (x : ?t), _ |- _ ]
      =>
        pose proof (mapC_get_subset _ _ _ _ _ _ _ H H1);
        eapply H2

  | [ H : forall x : ?t, In_set _ _ -> _ , H1 : map_get (minify_mapD _ (fun x : ?t => _)) _ = Some _, H2 : forall (x : ?t), _ |- _ ]
      =>
        pose proof (mapD_get_subset _ _ _ _ _ _ _ H H1);
        eapply H2
  end; repeat break_match; simpl in *; intuition; subst; eauto; 
  try congruence;
  try match goal with
  | H : context[ _ -> aspCb _ _ _ = errC _ ] |- aspCb _ _ _ = errC _ =>
    eapply H; repeat ff; try congruence;
    exfalso; eauto
  | H : context[ _ -> aspCb _ _ _ = resultC _ ] |- aspCb _ _ _ = resultC _ =>
    eapply H; repeat ff; try congruence;
    exfalso; eauto
  end.
Qed.
Global Hint Resolve supports_am_mancomp_subset : core. *)

Lemma end_to_end_mangen_supports_all : forall ts ls p m,
  forall cm env,
    end_to_end_mangen cm ls ts = resultC env ->
    map_get p env = Some m ->
  (forall t tp, 
    In (t, tp) ts ->
    In p (places tp t) ->
    (forall t',
      In t' (place_terms t tp p) ->
      manifest_support_term m t'
    )
  ).
Proof.
  intuition.
  pose proof (mangen_exists_end_to_end_mangen _ _ _ _ _ _ H H0 _ _ H1 H2 _ H3).
  break_exists.
  pose proof (mangen_subset_end_to_end_mangen _ _ _ H1 _ _ _ H4 _ _ _ H H0).
  pose proof manifest_supports_term_sub.
  pose proof (man_gen_old_always_supports _ _ _ _ _ _ H4 H2 H3).
  eauto.
Qed.
Global Hint Resolve end_to_end_mangen_supports_all : core.

Theorem manifest_generator_compiler_soundness_distributed_multiterm' : forall t ts ls tp p absMan aspBin cm sc att_sesplit_evt uuid,
forall env,
  end_to_end_mangen cm ls ts = resultC env ->
  map_get p env = Some absMan ->
  In (t,tp) ts ->
  (* In p (places tp t) -> *)
  well_formed_manifest absMan ->
  manifest_support_session_conf absMan sc ->
  att_sess_supports_term att_sesplit_evt t ->
  session_config_compiler (mkAM_Man_Conf absMan aspBin uuid) att_sesplit_evt = sc ->
  forall st,

    session_config_subset sc (st.(st_config)) ->  

    (  forall t', 
         In t' (place_terms t tp p) -> 
        (exists st', 
        
        build_cvm (copland_compile t') st = (resultC tt, st')) \/
        
        (exists st' errStr,
        build_cvm (copland_compile t') st = (errC (dispatch_error (Runtime errStr)), st'))
    ).
Proof.
  (* Search place_terms. *)
  intros.
  (* assert (In p (places tp t)) by 
            (eapply has_manifest_env_places_env_has_manifest; eauto). *)
  eapply well_formed_am_config_impl_executable.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config.
    * eauto.
    * (* NOTE: This is the important one, substitute proof of any manifest here *)
      assert (In p (places tp t)). {
        eapply in_plc_term; intuition; subst.
        find_rewrite; eauto.
      }
      eapply end_to_end_mangen_supports_all; eauto.
    * eapply att_sess_supports_place_terms; eauto.
  - subst; eauto.
Qed.

(* 
Lemma manifest_subset_knowsof_myPlc_update_self : forall b,
manifest_subset b (knowsof_myPlc_manifest_update b).
Proof.
  intros.
  induction b; ff.
  simpl.
  unfold manifest_subset.
  intuition.
  ff.
  eapply in_set_add.
  eassumption.
Qed.

Definition fun_cumul{A : Type} `{HA : EqClass A} (f: A -> manifest_set A -> manifest_set A) :=
  forall a x xs, 
    In x xs -> 
    In x (f a xs).

Lemma asdff{A : Type} `{HA : EqClass A} : forall (x:A) xs (ys:manifest_set A) f, 
  fun_cumul f ->
  In x xs -> 
  In x (fold_right f xs ys).
Proof.
intros.
generalizeEverythingElse ys.
induction ys.
  - intuition.
  - intuition.
    ff.
    eapply H.
    eauto.
Qed.



Lemma manifest_subset_pubkeys_update_self : forall b pubs,
manifest_subset b (pubkeys_manifest_update pubs b).
Proof.
  intros.
  induction b; ff.
  simpl.
  unfold manifest_subset.
  intuition.
  ff.

  eapply asdff; eauto.

  unfold fun_cumul.
  intros.
  eapply in_set_add.
  eassumption.
Qed.


(*
Definition end_to_end_mangen (ls:list (EvidenceT*Plc)) (ts: list (Term*Plc)) : EnvironmentM := 
  let ps := get_all_unique_places ts ls in 
    update_pubkeys_env ps (update_knowsOf_myPlc_env (end_to_end_mangen' ls ts)).
*)

Lemma exists_manifest_subset_update_pubkeys_env : forall e p pubs absMan, 
map_get (update_pubkeys_env pubs e) p = Some absMan -> 
(exists absMan', map_get e p = Some absMan' 
  /\ manifest_subset absMan' absMan).
Proof.
  induction e.
  -
  intuition.
  ff.
  -
  intuition.
  repeat ff.
  rewrite String.eqb_eq in *.
  subst.
  intuition.
  eexists.
  split; eauto.
  eapply manifest_subset_pubkeys_update_self.
  eauto.
Qed.

Lemma exists_manifest_subset_update_knowsOf_myPlc_env : forall e p absMan, 
map_get (update_knowsOf_myPlc_env e) p = Some absMan -> 
(exists absMan', map_get e p = Some absMan' 
  /\ manifest_subset absMan' absMan).
Proof.
  induction e.
  -
  intuition.
  ff.
  -
  intuition.
  repeat ff.
  rewrite String.eqb_eq in *.
  subst.
  intuition.
  eexists.
  split; eauto.
  eapply manifest_subset_knowsof_myPlc_update_self.
Qed.

Theorem manifest_generator_compiler_soundness_distributed_multiterm : forall t ts ls tp p absMan amLib amConf aspBin env,
  end_to_end_mangen ls ts amLib = resultC env ->
  map_get env p = Some absMan -> 
  In (t,tp) ts ->
  (* In p (places tp t) -> *)
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib aspBin = amConf ->
  forall st,

  (* st.(st_config) = amConf -> *)
  supports_am amConf (st.(st_config)) ->

  (*
    (* Note, this should be trivial typically as amConf = st.(st_config) and refl works *)
    supports_am amConf (st.(st_config)) ->  
    *)

    (  forall t', 
         In t' (place_terms t tp p) -> 
        (exists st', 
        
        build_cvm (copland_compile t') st = (resultC tt, st')) \/
        
        (exists st' errStr,
        build_cvm (copland_compile t') st = (errC (dispatch_error (Runtime errStr)), st'))
    ).
Proof.
  intros.
  unfold end_to_end_mangen in H; ff; simpl in *.
  pose proof (exists_manifest_subset_update_pubkeys_env _ _ _ _ H0).
  destruct_conjs.
  find_eapply_lem_hyp exists_manifest_subset_update_knowsOf_myPlc_env.
  destruct_conjs.
  eapply manifest_generator_compiler_soundness_distributed_multiterm'.
  eassumption.
  eassumption.
  eassumption.
  eapply lib_supports_manifest_subset.
  eassumption.
  eapply manifest_subset_trans.
  eassumption.
  eassumption.
  reflexivity.
  eapply supports_am_mancomp_subset.
  eassumption.
  eapply manifest_subset_trans.
  eassumption.
  eassumption.
  eassumption.
Qed.

Theorem manifest_generator_compiler_soundness_distributed_multiterm 
    : forall t ts ls tp p comp_map absMan env,
  end_to_end_mangen comp_map ls ts = resultC env ->
  map_get env p = Some absMan -> 
  In (t,tp) ts ->
  (* lib_supports_manifest amLib absMan -> *)
  (*
    (* Note, this should be trivial typically as amConf = st.(st_config) and refl works *)
    supports_am amConf (st.(st_config)) ->  
    *)
  (forall t' att_sesplit_evt aspBin uuid conf ev,
    In t' (place_terms t tp p) -> 
    conf = (mkAM_Man_Conf absMan aspBin uuid) ->
    (exists st',
      (run_cvm_w_config t' ev (session_config_compiler conf att_sess)) = 
      (resultC st')) 
    \/
    (exists errStr,
      (run_cvm_w_config t' ev (session_config_compiler conf att_sess)) = 
      (errC (dispatch_error (Runtime errStr)))
    )
  ).
Proof.
  induction t; subst; simpl in *; intuition; subst; eauto;
  simpl in *; intuition; eauto.
  - destruct (tp =? p); simpl in *; intuition; subst;
    simpl in *;
    unfold run_cvm_w_config, run_cvm, run_core_cvm;
    destruct a; simpl in *; eauto;
    repeat (break_match; subst; repeat find_rewrite; repeat find_injection;
      simpl in *; intuition; eauto; try cvm_monad_unfold; try congruence).
    unfold generate_ASP_dispatcher, generate_ASP_dispatcher' in *; simpl in *; intuition.
    * unfold generate_ASP_dispatcher, generate_ASP_dispatcher' in *; simpl in *; intuition.  
      ff; simpl in *.
      build_cvm; simpl in *.

  subst.
*)
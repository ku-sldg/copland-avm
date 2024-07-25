(*  Primary results of Manifest Compiler Soundness (for Attestation).
      Namely, that the compiler outputs a collection of manifests that support 
      execution of the input protocols.  *)

Require Import Manifest Manifest_Generator ID_Type
  Maps Term_Defs List Cvm_St Cvm_Impl ErrorStMonad_Coq StructTactics 
  Cvm_Monad EqClass Manifest_Admits Auto.
Require Import Manifest_Generator_Facts Eqb_Evidence Attestation_Session.

Require Import Manifest_Generator_Helpers Session_Config_Compiler.
Require Import Helpers_CvmSemantics.

Require Import Coq.Program.Tactics.

Import ListNotations.

Definition session_config_subset (sc1 sc2 : Session_Config) : Prop :=
  (forall aid l targ targid ev, 
      (forall res, 
      sc1.(aspCb) (asp_paramsC aid l targ targid) ev = resultC res ->
      sc2.(aspCb) (asp_paramsC aid l targ targid) ev = resultC res)) /\
  (forall p, (forall res, 
      map_get (sc1.(plc_map)) p = Some res ->
      map_get (sc2.(plc_map)) p = Some res)) /\
  (forall p, (forall res, 
      map_get (sc1.(pubkey_map)) p = Some res ->
      map_get (sc2.(pubkey_map)) p = Some res)) /\
  (forall aid l targ targid ev errStr,
      sc1.(aspCb) (asp_paramsC aid l targ targid) ev = errC (Runtime errStr) ->
      sc2.(aspCb) (asp_paramsC aid l targ targid) ev = errC (Runtime errStr)) 
  /\
  (forall p,
      map_get (sc1.(plc_map)) p = None ->
      map_get (sc2.(plc_map)) p = None) /\
  (forall p, 
      map_get (sc1.(pubkey_map)) p = None ->
      map_get (sc2.(pubkey_map)) p = None).

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
  unfold session_config_subset; intuition.
Qed.

Fixpoint session_config_supports_exec (t : Term) (sc : Session_Config) : Prop :=
  match t with
  | asp a =>
      match a with
      | NULL => True
      | CPY => True
      | SIG => 
          forall l targ targid ev,
          ((exists res, 
          sc.(aspCb) (asp_paramsC sig_aspid l targ targid) ev = resultC res) \/ 
          (exists errStr, sc.(aspCb) (asp_paramsC sig_aspid l targ targid) ev = errC (Runtime errStr)))
      | HSH =>
          forall l targ targid ev,
          ((exists res, 
          sc.(aspCb) (asp_paramsC hsh_aspid l targ targid) ev = resultC res) \/ 
          (exists errStr, sc.(aspCb) (asp_paramsC hsh_aspid l targ targid) ev = errC (Runtime errStr)))
      | ENC p =>
          (forall l targ targid ev,
          ((exists res, 
          sc.(aspCb) (asp_paramsC enc_aspid l targ targid) ev = resultC res) \/ 
          (exists errStr, sc.(aspCb) (asp_paramsC enc_aspid l targ targid) ev = errC (Runtime errStr)))) /\
          ((exists res, 
            map_get (sc.(pubkey_map)) p = Some res))
      | ASPC _ _ (asp_paramsC aspid _ _ _) =>
          (forall l targ targid ev,
          ((exists res, 
          sc.(aspCb) (asp_paramsC aspid l targ targid) ev = resultC res) \/ 
          (exists errStr, sc.(aspCb) (asp_paramsC aspid l targ targid) ev = errC (Runtime errStr))))
      end
  | att p' t' => 
      (* We only care that we can dispatch it *)
      ((exists res, map_get (sc.(plc_map)) p' = Some res))
  | lseq t1 t2 =>
      exists sc1 sc2,
      (session_config_supports_exec t1 sc1) /\
      (session_config_supports_exec t2 sc2) /\
      session_config_subset sc1 sc /\
      session_config_subset sc2 sc
  | bseq _ t1 t2 =>
      exists sc1 sc2,
      (session_config_supports_exec t1 sc1) /\
      (session_config_supports_exec t2 sc2) /\
      session_config_subset sc1 sc /\
      session_config_subset sc2 sc
  | bpar _ t1 t2 =>
      exists sc1 sc2,
      (session_config_supports_exec t1 sc1) /\
      (session_config_supports_exec t2 sc2) /\
      session_config_subset sc1 sc /\
      session_config_subset sc2 sc
  end.

Ltac unfolds :=
  (* repeat monad_unfold; *)
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
Require Import Manifest_Generator_Union Cvm_Run AM_Manager.


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

(* Theorem filter_resolver : forall {A B} `{EqClass A} (m : MapC A B) a (filt : A -> bool),
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

Theorem filter_resolver_mapd : forall {A B} `{EqClass A, EqClass B} (m : MapC A B) a (filt : A -> bool),
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
    H3 : map_get ?l' ?x = None,
    H4 : forall _ : _, In_set _ ?l -> _
      |- _ => 
    let H' := fresh "H'" in
    let H'' := fresh "H'" in
    let H''' := fresh "H'" in
    eapply H4 in H1 as H';
    destruct H'; find_rewrite; congruence
  (* | H1 : In_set ?x ?l,
    H3 : map_get (_ ?l' ?fn) ?x = None,
    H4 : forall _ : _, In_set _ ?l -> _
      |- _ => 
    let H' := fresh "H'" in
    let H'' := fresh "H'" in
    let H''' := fresh "H'" in
    eapply H4 in H1 as H';
    assert (H'' : fn x = true) by ff;
    pose proof (filter_resolver _ _ _ H' H'') as H''';
    destruct H'''; find_rewrite; congruence *)
  end.

Lemma never_change_sess_conf : forall t st res st',
  build_cvm (copland_compile t) st = (res, st') ->
  st_config st = st_config st'.
Proof.
  intros;
  destruct st.
  simpl; eauto. 
  edestruct sc_immut; eauto.
  unfold execErr.
  rewrite H.
  simpl; eauto.
Qed.

Local Hint Resolve never_change_sess_conf : core.
Local Hint Resolve session_config_subset_refl : core.
Local Hint Resolve session_config_subset_trans : core.

Theorem well_formed_am_config_impl_executable : forall t sc,
  session_config_supports_exec t sc ->
  forall st,
  session_config_subset sc (st.(st_config)) ->
  (exists st', 
    build_cvm (copland_compile t) st = (resultC tt, st')) \/
  (exists st' errStr, 
    build_cvm (copland_compile t) st = (errC (dispatch_error (Runtime errStr)), st')).
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a;
    try (simpl in *; monad_unfold; eauto; fail); (* NULL, CPY *)
    subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    unfold session_config_subset, sig_params, enc_params, hsh_params in *; intuition;


    match goal with
    | H1 : forall _, _,
      H2 : aspCb _ (asp_paramsC ?a ?l ?targ ?tid) ?ev = _,
      H3 : context[ aspCb _ _ _ = errC (Runtime _) -> _],
      H4 : context[ aspCb _ _ _ = resultC _ -> _]
      |- _ =>
        let H := fresh "H" in
        let H' := fresh "Hx" in
        let H'' := fresh "Hx" in
        let res := fresh "res" in
        destruct (H1 l targ tid ev) as [H | H]
        ; 
        [
          (* result side *)
          destruct H as [res H''];
          pose proof (H4 a l targ tid ev) as H';
          erewrite H' in *; eauto; congruence
          |
          (* err side *)
          destruct H as [errStr H''];
          pose proof (H3 a l targ tid ev errStr) as H';
          intuition; find_rewrite; find_injection; eauto
        ]
    end.

  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      unfold remote_session, doRemote, doRemote_session', do_remote, check_cvm_policy in *;
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    unfold session_config_subset in *; intuition.
    + break_exists;  
      repeat find_apply_hyp_hyp; repeat find_rewrite; congruence.
  - break_exists; intuition.
    eapply IHt1 in H1; intuition; eauto;
    monad_unfold; break_exists; find_rewrite; eauto.
    find_eapply_lem_hyp sc_immut_better; find_rewrite.
    eapply IHt2 in H; intuition; eauto; break_exists;
    repeat find_rewrite; eauto.
  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
      match goal with
      | H1 : exists _ _ : Session_Config, _
        |- _ =>
          let ac1 := fresh "ac" in
          let ac2 := fresh "ac" in
          let AS1 := fresh "AS" in
          let AS2 := fresh "AS" in
          let S1 := fresh "S" in
          let S2 := fresh "S" in
          destruct H1 as [ac1 [ac2 [AS1 [AS2 [S1 S2]]]]]
          ;
          match goal with
          | H2 : build_cvm (copland_compile t1) ?st = _
            |- _ =>
              let A := fresh "A" in
              assert (A : session_config_subset ac1 (st_config st)); [
                simpl in *; eauto
                |
                destruct (IHt1 ac1 AS1 st A); 
                intuition; repeat find_rewrite; 
                try break_exists;
                repeat find_injection;
                try congruence; eauto
              ];
            eapply sc_immut_better in H2; simpl in *; 
            repeat find_rewrite; subst; eauto
          end
          ;
          match goal with
          | H3 : build_cvm (copland_compile t2) ?st = _
            |- _ =>
              let A := fresh "A" in
              assert (A : session_config_subset ac2 (st_config st)); [ 
                repeat find_eapply_lem_hyp never_change_am_conf;
                repeat find_rewrite;
                simpl in *; eauto
                |
                destruct (IHt2 ac2 AS2 st A);
                intuition; repeat find_rewrite;
                repeat find_injection;
                try congruence; eauto
              ];
            eapply sc_immut_better in H3; simpl in *; 
            repeat find_rewrite; subst; eauto
          end
      end.
  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
      match goal with
      | H1 : exists _ _ : Session_Config, _
        |- _ =>
          let ac1 := fresh "ac" in
          let ac2 := fresh "ac" in
          let AS1 := fresh "AS" in
          let AS2 := fresh "AS" in
          let S1 := fresh "S" in
          let S2 := fresh "S" in
          destruct H1 as [ac1 [ac2 [AS1 [AS2 [S1 S2]]]]]
          ;
          match goal with
          | H2 : build_cvm (copland_compile t1) ?st = _
            |- _ =>
              let A := fresh "A" in
              assert (A : session_config_subset ac1 (st_config st)); [
                simpl in *; eauto
                |
                destruct (IHt1 ac1 AS1 st A); 
                intuition; repeat find_rewrite; 
                try break_exists;
                repeat find_injection;
                try congruence; eauto
              ];
            eapply sc_immut_better in H2; simpl in *; 
            repeat find_rewrite; subst; eauto
          end
          ;
          match goal with
          | H3 : build_cvm (copland_compile t2) ?st = _
            |- _ =>
              let A := fresh "A" in
              assert (A : session_config_subset ac2 (st_config st)); [ 
                repeat find_eapply_lem_hyp never_change_am_conf;
                repeat find_rewrite;
                simpl in *; eauto
                |
                destruct (IHt2 ac2 AS2 st A);
                intuition; repeat find_rewrite;
                repeat find_injection;
                try congruence; eauto
              ];
            eapply sc_immut_better in H3; simpl in *; 
            repeat find_rewrite; subst; eauto
          end
      end.
Qed.

Definition manifest_support_session_conf (m : Manifest) (sc : Session_Config)
    : Prop :=
  (forall a, In_set a (m.(asps)) -> 
    forall l targ targid ev,
    (exists res, sc.(aspCb) (asp_paramsC a l targ targid) ev = resultC res) \/
    (exists errStr, sc.(aspCb) (asp_paramsC a l targ targid) ev = errC (Runtime errStr))) /\
  (forall a, In_set a (m.(asps)) -> 
    exists loc, map_get (m.(ASP_Mapping)) a = Some loc).
(* 
Definition att_sess_support_session_conf (ats : Attestation_Session) (sc : Session_Config)
    : Prop :=
  (forall p, 
    exists res, map_get (att_sess.(plc_map)) p = Some res) /\
  (forall p, 
    exists res, map_get (sc.(pubkey_map)) p = Some res). *)

(* 
Theorem manifest_support_session_conf_compiler 
    : forall absMan aspBin myUUID att_sess,
  manifest_support_session_conf 
    absMan 
    (session_config_compiler (mkAM_Man_Conf absMan aspBin myUUID) att_sess).
Proof.
  unfold manifest_support_session_conf; intuition.
  unfold manifest_support_session_conf, session_config_compiler in *;
  intuition; simpl in *; ff; intuition; eauto.
  ff.
  ff.
  simpl in *; ff; intuition.
  simpl in *; repeat ff; intuition;
  repeat break_match; simpl in *; eauto with *; intuition; eauto.
  try kill_map_none;
  match goal with
  | H:  context[ map_get (minify_mapC ?l ?filt) ?a],
    H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
    assert (CO : exists x, map_get (minify_mapC l filt) a = Some x)
    ;
      [
      eapply filter_resolver; eauto;
      repeat break_match; intuition; try congruence
      | 
      rewrite H in CO; destruct CO; congruence
    ]
  | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
    H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
    assert (CO : exists x, map_get (minify_mapD l filt) a = Some x)
    ;
      [
      eapply filter_resolver_mapd; eauto;
      repeat break_match; intuition; try congruence
      | 
      rewrite H in CO; destruct CO; congruence
    ]
  end.
Qed. *)

Fixpoint att_sess_supports_term (ats : Attestation_Session) (t : Term) 
    : Prop :=
  match t with
  | asp a =>
      match a with
      | ENC p => 
        exists v, map_get (ats.(PubKey_Mapping)) p = Some v
      | _ => True
      end
  | att p' t' => 
      exists v, map_get (ats.(Plc_Mapping)) p' = Some v /\
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
    (exists v, map_get (m.(ASP_Mapping)) a = Some v)).

Fixpoint manifest_support_term (m : Manifest) (t : Term) : Prop :=
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
      | ASPC _ _ (asp_paramsC aspid _ _ _) =>
          In_set aspid (m.(asps))
      end
  | att p' t' => True
    (* exists m', manifest_support_term m' t' *)
  | lseq t1 t2 =>
      manifest_support_term m t1 /\
      manifest_support_term m t2
  | bseq _ t1 t2 =>
      manifest_support_term m t1 /\
      manifest_support_term m t2
  | bpar _ t1 t2 =>
      manifest_support_term m t1 /\
      manifest_support_term m t2
  end.

Theorem manifest_support_am_config_impl_am_config: forall t absMan ats,
  well_formed_manifest absMan ->
  manifest_support_term absMan t ->
  att_sess_supports_term ats t ->
  forall aspBin uuid,
  session_config_supports_exec 
    t 
    (session_config_compiler (mkAM_Man_Conf absMan aspBin uuid) ats).
Proof.
  unfold manifest_support_term, well_formed_manifest in *;
  induction t; simpl in *; intuition; eauto;
  repeat match goal with
  | H : forall _ _, ?p _ _ -> _,
    H' : ?p _ _ |- _ =>
      eapply H in H'; intuition; eauto
  end; try (repeat eexists; eauto; fail).
  - repeat (break_match; repeat find_rewrite; repeat find_injection;
      simpl in *; intuition; eauto; break_exists; try congruence);
    find_apply_hyp_hyp; break_exists; congruence.
  - break_exists; intuition; eauto.
Qed.
Require Import ManCompSoundness_Helpers.

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

Lemma has_manifest_env_places_env_has_manifest' : forall t p tp m e,
  map_get (manifest_generator' tp t e) p = Some m ->
  (exists m', map_get e p = Some m') \/ 
  In p (places tp t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - destruct a; ff;
    unfold asp_manifest_update, manifest_update_env in *;
    simpl in *;
    destEq tp p; eauto;
    try rewrite map_distinct_key_rw in *; eauto.
  - simpl in *; intuition; eauto.
    find_apply_hyp_hyp; intuition.
  - (* lseq case *)
    ff; find_apply_hyp_hyp; intuition;
    break_exists; eauto;
    try find_apply_hyp_hyp; intuition;
    pose proof places'_cumul;
    pose proof places_app_cumul;
    eauto.
  - ff; find_apply_hyp_hyp; intuition;
    break_exists; eauto;
    try find_apply_hyp_hyp; intuition;
    pose proof places'_cumul;
    pose proof places_app_cumul;
    eauto.
  - ff; find_apply_hyp_hyp; intuition;
    break_exists; eauto;
    try find_apply_hyp_hyp; intuition;
    pose proof places'_cumul;
    pose proof places_app_cumul;
    eauto.
Qed.

Lemma has_manifest_env_places_env_has_manifest : forall t p tp m,
  map_get (manifest_generator t tp) p = Some m ->
  In p (places tp t).
Proof.
  intros.
  unfold manifest_generator in *.
  apply has_manifest_env_places_env_has_manifest' in H.
  destruct_conjs.
  door; ff. 
Qed.


Lemma places_env_has_manifest : forall t p tp,
  In p (places tp t) -> 
  exists m, 
    map_get (manifest_generator t tp) p = Some m.
Proof.
  intros.
  unfold manifest_generator.
  generalizeEverythingElse t.
  induction t; intros.
  -
    ff.
    door; try solve_by_inversion.
    subst.
    destruct a;
    unfold asp_manifest_update;
    unfold manifest_update_env;
    ff; rewrite String.eqb_refl in *; try congruence;
    eauto.

  - (* at case *)
    simpl in *; intuition; subst; eauto.
    intuition; subst; eauto.
    eapply IHt.
    eapply IHt; eauto.
    simpl in *; intuition; subst; eauto.
    eauto.

    ff.
    door; ff.
    subst.
    ff.
    unfold manifest_update_env.
    ff.
    +
      subst.

      assert (Environment_subset 
      (map_set e p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            uuidPlcs := manset_add p uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |})

          (manifest_generator' p t
       (map_set e p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            uuidPlcs := manset_add p uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |}))
      
      ).
      {
        eapply manifest_generator_cumul'.
      }
      unfold Environment_subset in *.


      assert (
        map_get
      (map_set e p0
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           uuidPlcs := manset_add p uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) p0 = Some {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := manset_add p uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |}
      ).
      {
        eapply mapC_get_works.

      }

      specialize H with (m1 := {|
        my_abstract_plc := my_abstract_plc;
        asps := asps;
        uuidPlcs := @manset_add _ Eq_Class_ID_Type p uuidPlcs;
        pubKeyPlcs := pubKeyPlcs;
        targetPlcs := targetPlcs;
        policy := policy
      |}) (p := p0).
      find_apply_hyp_hyp.
      destruct_conjs.

      exists H0.
      eauto.


      +

      subst; simpl in *.

      assert (Environment_subset 
      (map_set e my_abstract_plc
          {|
            my_abstract_plc := my_abstract_plc;
            asps := manifest_set_empty;
            uuidPlcs := [p];
            pubKeyPlcs := manifest_set_empty;
            targetPlcs := manifest_set_empty;
            policy := empty_PolicyT;
          |})

          (manifest_generator' p t
      (map_set e my_abstract_plc
          {|
            my_abstract_plc := my_abstract_plc;
            asps := manifest_set_empty;
            uuidPlcs := [p];
            pubKeyPlcs := manifest_set_empty;
            targetPlcs := manifest_set_empty;
            policy := empty_PolicyT;
          |}))
      
      ).
      {
        eapply manifest_generator_cumul'.
      }
      unfold Environment_subset in *.

      assert (
        map_get
      (map_set e my_abstract_plc
         {|
           my_abstract_plc := my_abstract_plc;
           asps := manifest_set_empty;
           uuidPlcs := [p];
           pubKeyPlcs := manifest_set_empty;
           targetPlcs := manifest_set_empty;
           policy := empty_PolicyT;
         |}) my_abstract_plc = Some {|
           my_abstract_plc := my_abstract_plc;
           asps := manifest_set_empty;
           uuidPlcs := [p];
           pubKeyPlcs := manifest_set_empty;
           targetPlcs := manifest_set_empty;
           policy := empty_PolicyT;
       |}
      ).
      {
        eapply mapC_get_works.
      }

      pose proof (H _ _ H0).

      find_apply_hyp_hyp.
      destruct_conjs.
      eexists.
      erewrite H2.

      simpl in *; intuition.

    - (* lseq case *)
      ff.
      door; ff.




      assert (In p (places tp t1) \/ 
              In p (places tp t2)).
              {
                eapply places_decomp; eauto.
              }
      door.
      +
        assert (exists mm, 
                map_get (manifest_generator' tp t1 e) p = Some mm).
        {
          eauto.
        }
        destruct_conjs.

        assert (Environment_subset 
        (manifest_generator' tp t1 e)
        (manifest_generator' tp t2
         (manifest_generator' tp t1 e))
        ).
        {
          eapply manifest_generator_cumul'.
        }

        unfold Environment_subset in *.
        specialize H3 with (m1:=H1) (p:=p).
        find_apply_hyp_hyp.
        destruct_conjs.
        eexists.
        eassumption.

      +
      eapply IHt2.
      unfold places in H0.
      invc H0.
      eauto.
      eauto.


      - (* lseq case *)
      ff.
      door; ff.




      assert (In p (places tp t1) \/ 
              In p (places tp t2)).
              {
                eapply places_decomp; eauto.
              }
      door.
      +
        assert (exists mm, 
                map_get (manifest_generator' tp t1 e) p = Some mm).
        {
          eauto.
        }
        destruct_conjs.

        assert (Environment_subset 
        (manifest_generator' tp t1 e)
        (manifest_generator' tp t2
         (manifest_generator' tp t1 e))
        ).
        {
          eapply manifest_generator_cumul'.
        }

        unfold Environment_subset in *.
        specialize H3 with (m1:=H1) (p:=p).
        find_apply_hyp_hyp.
        destruct_conjs.
        eexists.
        eassumption.

      +
      eapply IHt2.
      unfold places in H0.
      invc H0.
      eauto.
      eauto.



      - (* lseq case *)
      ff.
      door; ff.




      assert (In p (places tp t1) \/ 
              In p (places tp t2)).
              {
                eapply places_decomp; eauto.
              }
      door.
      +
        assert (exists mm, 
                map_get (manifest_generator' tp t1 e) p = Some mm).
        {
          eauto.
        }
        destruct_conjs.

        assert (Environment_subset 
        (manifest_generator' tp t1 e)
        (manifest_generator' tp t2
         (manifest_generator' tp t1 e))
        ).
        {
          eapply manifest_generator_cumul'.
        }

        unfold Environment_subset in *.
        specialize H3 with (m1:=H1) (p:=p).
        find_apply_hyp_hyp.
        destruct_conjs.
        eexists.
        eassumption.

      +
      eapply IHt2.
      unfold places in H0.
      invc H0.
      eauto.
      eauto.
Qed.
*)




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
  intros.
  eapply asdf.
  eassumption.
  ff.
  eauto.
Qed.
*)

Lemma manifest_supports_term_sub : forall m1 m2 t,
  manifest_subset m1 m2 ->
  manifest_support_term m1 t -> 
  manifest_support_term m2 t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; simpl in *; intuition; eauto;
  repeat ff. 
Qed.

Lemma env_subset_man_subset : forall e1 e2 p m m',
  Environment_subset e1 e2 -> 
  map_get e1 p = Some m -> 
  map_get e2 p = Some m' -> 
  manifest_subset m m'.
Proof.
  intros.
  unfold Environment_subset in *.
  specialize H with (m1:= m) (p:=p).
  find_apply_hyp_hyp.
  destruct_conjs.
  find_rewrite.
  ff.
Qed.


Theorem man_gen_old_always_supports : forall t t' tp p backMan absMan,
  map_get (manifest_generator' tp t backMan) p = Some absMan ->
  In p (places tp t) ->
  In t' (place_terms t tp p) ->
  manifest_support_term absMan t'.
Proof.
  induction t; intuition.
  - admit. 
  - simpl in *; intuition; subst; eauto. 
    * rewrite String.eqb_refl in *; simpl in *; intuition; subst; eauto;
      simpl in *; eauto.
    * ff; intuition; subst; eauto; simpl in *; eauto. 
    * ff; intuition; subst; simpl in *; eauto.
  - 
 
  ff.
  ff.
  +
  door; try solve_by_inversion.
  subst.
  ff.
  assert (tp = p).
  {
    eapply eqb_eq_plc; eauto.
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
      rewrite eqb_plc_refl in *.
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
              rewrite eqb_plc_refl in Heqb.
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
              rewrite eqb_plc_refl in *.
              solve_by_inversion.
            +++++
              eassumption.
          ++++
            eassumption.
 
  
  simpl in *.
    destruct (map_get (manifest_generator' tp t1 backMan) .
    simpl in *; intuition; subst; eauto; ff;
    try rewrite String.eqb_refl in *; simpl in *; eauto;
    try door; subst; simpl in *; try (exfalso; eauto; congruence).
    destruct (manifest_g)
    simpl in *; intuition; subst; eauto; ff;
    intuition; eauto;
    try rewrite String.eqb_refl in *; try congruence;
    subst; simpl in *; intuition; eauto.
    * eapply IHt in H; eauto.
      ff; intuition; subst; eauto.
      simpl in *; eauto.
    * eapply IHt in H; eauto.
      ff; intuition; subst; eauto.
      simpl in *; eauto. 


  induction t; simpl in *; intuition; subst; eauto;
  try rewrite String.eqb_refl in *;
  simpl in *; intuition; subst; eauto.
  - admit. 
  - simpl; eauto. 
  - eapply IHt; eauto. 
    ff; intuition; subst; eauto.
    simpl in *.
    eexists; eapply IHt.


  induction t; intuition; subst; simpl in *;
  intuition; subst; eauto;
  try match goal with
  | H : context[?p =? ?p] |- _ =>
    rewrite String.eqb_refl in H
  end; simpl in *; intuition; subst; eauto;  
  try unfold manifest_update_env, aspid_manifest_update, 
    asp_manifest_update in *;
  try rewrite mapC_get_works in *; repeat find_injection;
  simpl in *; intuition; eauto; repeat (ff; fail).
  - eapply IHt in H; eauto. 
  repeat (try break_match; 
    try unfold manifest_update_env, aspid_manifest_update in *;
    subst; simpl in *; intuition;
    subst; repeat find_rewrite; repeat find_injection;
    try rewrite mapC_get_works in *;
    eauto using in_set_add, manadd_In_add;
    intuition; eauto; try congruence);
  try eapply manadd_In_add.
    pose proof manadd_In_add; eauto
    eapply manadd_In_add.
    pose proof in_set_add.
    Search manset_add.
  eauto using in_set_add.
  - repeat (try break_match; 
      unfold manifest_update_env, 
        aspid_manifest_update in *;
      subst; simpl in *; intuition; eauto; try congruence;
      repeat find_rewrite;
      repeat find_injection;
      simpl in * );
    try (rewrite mapC_get_works in *; simpl in *; repeat find_injection; simpl in *; intuition; eauto);
    try (eapply manadd_In_add).

  - (* at case *)
    simpl in *; intuition; subst; eauto;
    eapply IHt in H; intuition; subst; eauto.
    * ff; intuition; subst; eauto.
      ** admit.
      **  destEq p0 p0; eauto.
      rewrite eqb_refl in *.
    eapply IHt in H; intuition; subst; eauto;
    break_if; intuition; simpl in *; intuition;
    subst.
    repeat ff; intuition; subst; eauto.
  ff.

  ff.
  +
    door; try solve_by_inversion.
    subst.
    ff.
    unfold at_manifest_generator in *.
    ff.
    unfold manifest_update_env in *.
    ff.
    ++
      unfold knowsof_manifest_update in *.
      ff.
      subst.
      assert (tp = p0).
      {
        eapply eqb_eq_plc; eauto.
      }
      subst.

      pose (manifest_generator_cumul' t p 
              (map_set backMan p0
              {|
                my_abstract_plc := my_abstract_plc;
                asps := asps;
                uuidPlcs := manset_add p uuidPlcs;
                pubKeyPlcs := pubKeyPlcs;
                targetPlcs := targetPlcs;
                policy := policy
              |})).

    eapply fdsa; eauto.
    simpl.
    eapply manadd_In_add.

    ++
    assert (tp = p0).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.


    pose (manifest_generator_cumul' t p 
            ((map_set backMan p0
              {|
                my_abstract_plc := p0;
                asps := manifest_set_empty;
                uuidPlcs := manset_add p manifest_set_empty;
                pubKeyPlcs := manifest_set_empty;
                targetPlcs := manifest_set_empty; (* v; *)
                policy := empty_PolicyT
              |}))).

    eapply fdsa; eauto.
    simpl.
    auto.
  +
    door; eauto.
    subst.
    rewrite eqb_plc_refl in *.
    solve_by_inversion.

  - (* lseq case *)

  ff.
  ff.
  +
  door; try solve_by_inversion.
  subst.
  ff.
  assert (tp = p).
  {
    eapply eqb_eq_plc; eauto.
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
      rewrite eqb_plc_refl in *.
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
              rewrite eqb_plc_refl in Heqb.
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
              rewrite eqb_plc_refl in *.
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
    eapply eqb_eq_plc; eauto.
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
      rewrite eqb_plc_refl in *.
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
              rewrite eqb_plc_refl in Heqb.
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
            rewrite eqb_plc_refl in *.
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
    eapply eqb_eq_plc; eauto.
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
      rewrite eqb_plc_refl in *.
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
              rewrite eqb_plc_refl in Heqb.
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
            rewrite eqb_plc_refl in *.
            solve_by_inversion.
          +++++
            eassumption.
        ++++
          eassumption.
Qed.
*)

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

Lemma man_gen_yields_wf_manifests : forall t tp p absMan,
  (* well_formed_manifest backMan -> *)
  map_get (manifest_generator' tp t []) p = Some absMan ->
  well_formed_manifest absMan.
Proof.
  induction t; simpl in *; intuition; eauto;
  repeat ff; intuition; simpl in *.
  - unfold well_formed_manifest; intuition. 
    unfold asp_manifest_update; simpl in *; ff; intuition;
    subst; eauto.

Theorem manifest_generator_compiler_soundness_distributed : forall t tp p absMan uuid aspBin sc att_sess,
  map_get (manifest_generator t tp) p = Some absMan ->
  well_formed_manifest absMan ->
  manifest_support_session_conf absMan sc ->
  att_sess_supports_term att_sess t ->
  session_config_compiler (mkAM_Man_Conf absMan aspBin uuid) att_sess = sc ->
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
    * 
    * eapply att_sess_supports_place_terms; eauto.
      Search (manifest_support_term _ _).
      eapply manifest_support_am_config_compiler; eauto.
    * (* NOTE: This is the important one, substitute proof of any manifest here *)
      eapply man_gen_old_always_supports.
      eassumption.
      door.
      +
        subst.
        unfold places.
        left.
        eauto.
      +
        unfold places.
        right.
        eauto.
      +
        subst.
        eassumption.
  -
    rewrite H1; eauto. 
  Unshelve. eapply "PLC"%string.
Qed.

Require Import Manifest_Generator_Union.

Close Scope cop_ent_scope.

(* Global Hint Resolve manifest_subset_union_l : core. *)

Lemma manifest_env_union_works : forall env env' p m,
  map_get (Manifest_Union.environment_union env env') p = Some m ->
  (exists m', map_get env p = Some m' /\ manifest_subset m' m) \/
  (exists m', map_get env' p = Some m' /\ manifest_subset m' m).
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
  (map_get env p <> None \/ map_get env' p <> None) ->
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
  (map_get env p <> None \/ map_get env' p <> None).
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
  (map_get env p <> None \/ map_get env' p <> None).
Proof.
  split; eauto.
Qed.
Global Hint Resolve man_env_union_not_none : core.

Lemma manifest_env_union_always_subset : forall env env' p m,
  map_get (Manifest_Union.environment_union env env') p = Some m ->
  (forall m', map_get env p = Some m' -> manifest_subset m' m) /\
  (forall m', map_get env' p = Some m' -> manifest_subset m' m).
Proof.
  induction env; simpl in *; intuition; eauto.
  - eexists; intuition; try congruence.
  - find_rewrite; find_injection; eapply manifest_subset_refl.
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
  (exists m', (map_get env p = Some m' \/
  map_get env' p = Some m')).
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
  (exists m', (map_get env p = Some m' \/
  map_get env' p = Some m')).
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
  map_get env_start p = Some m' ->
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
    eapply manifest_subset_trans; eauto.
Qed.
Global Hint Resolve manifest_part_of_fold_impl_fold : core.

Lemma manifest_part_of_fold_ind_impl_fold : forall envs env p m',
  In env envs ->
  map_get env p = Some m' ->
  (forall env_start, 
    exists m,
    map_get (fold_right Manifest_Union.environment_union env_start envs) p = Some m /\
    manifest_subset m' m
  ).
Proof.
  induction envs; intros; eauto with *; simpl in *; eauto; intuition;
  subst; eauto.
  - pose proof (manifest_env_union_map_one env (fold_right Manifest_Union.environment_union env_start envs) p). 
    assert ((exists m' : Manifest, map_get env p = Some m' \/ map_get (fold_right Manifest_Union.environment_union env_start envs) p = Some m')) by (rewrite H0; eauto).
    rewrite <- H in H1.
    break_exists.
    eapply manifest_env_union_always_subset in H1 as H'';
    destruct H''.
    eapply H2 in H0 as H'.
    exists x; intuition; eauto.
  - pose proof (IHenvs _ _ _ H1 H0 env_start).
    break_exists; intuition; eauto.
    pose proof (manifest_env_union_map_one a (fold_right Manifest_Union.environment_union env_start envs) p).
    assert ((exists m' : Manifest, map_get a p = Some m' \/ map_get (fold_right Manifest_Union.environment_union env_start envs) p = Some m')) by (rewrite H2; eauto).
    rewrite <- H in H4.
    break_exists.
    eapply manifest_env_union_always_subset in H4 as H'.
    destruct H'.
    eapply H6 in H2 as H''.
    exists x0; intuition; eauto.
    eapply manifest_subset_trans; eauto.
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
    map_get env_start p = Some m' ->
    manifest_subset m' m) /\
  (forall env m', 
    In env envs ->
    map_get env p = Some m' ->
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
    map_get env p = Some m' ->
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
    forall ls al env, 
      end_to_end_mangen' ls ts al = resultC env ->
      map_get env p = Some m ->
      manifest_subset m' m
  ).
Proof.
  intuition; unfold end_to_end_mangen' in *; ff;
  find_eapply_lem_hyp manifest_env_union_always_subset; intuition.
Qed.
Global Hint Resolve mangen_plcTerm_subset_end_to_end_mangen : core.

Lemma mangen_subset_end_to_end_mangen : forall ts t tp,
  In (t, tp) ts ->
  (forall m m' p,
    map_get (manifest_generator t tp) p = Some m' ->
    forall ls al env, 
      end_to_end_mangen' ls ts al = resultC env ->
      map_get env p = Some m ->
      manifest_subset m' m
  ).
Proof.
  intuition.
  assert (exists m'', map_get (mangen_plcTerm_list_union ts) p = Some m''). eapply mangen_plcTerm_list_exists; eauto.
  break_exists.
  pose proof (mangen_plcTerm_list_subsumes ts p x H3 t tp H _ H0).
  eapply manifest_subset_trans; eauto.
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
  forall al env,
    end_to_end_mangen' ls ts al = resultC env ->
    map_get env p = Some m ->
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

Lemma lib_supports_manifest_subset : forall al m m',
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

Lemma supports_am_mancomp_subset: forall al m m' ac aspBin,
  supports_am (manifest_compiler m al aspBin) ac -> 
  manifest_subset m' m ->
  supports_am (manifest_compiler m' al aspBin) ac.
Proof.
  intuition.
  unfold supports_am, manifest_subset,
    generate_Plc_dispatcher, generate_PubKey_dispatcher in *;
  intuition; simpl in *; eauto;
  repeat break_match; simpl in *; repeat ff; intuition; subst; eauto;
  unfold supports_am, manifest_subset,
    generate_Plc_dispatcher, generate_PubKey_dispatcher in *;
  try congruence; eauto; try find_injection;
  repeat break_match; simpl in *; intuition; subst; eauto;
  try congruence;
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
Global Hint Resolve supports_am_mancomp_subset : core.

Lemma end_to_end_mangen_supports_all : forall ts ls p m,
  forall al env,
    end_to_end_mangen' ls ts al = resultC env ->
    map_get env p = Some m ->
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

Theorem manifest_generator_compiler_soundness_distributed_multiterm' : forall t ts ls tp p absMan amLib amConf aspBin,
forall env,
  end_to_end_mangen' ls ts amLib = resultC env ->
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
  (* Search place_terms. *)
  intros.
  (* assert (In p (places tp t)) by 
            (eapply has_manifest_env_places_env_has_manifest; eauto). *)
  eapply well_formed_am_config_impl_executable.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config.
    * eapply manifest_support_am_config_compiler; eauto.
    * (* NOTE: This is the important one, substitute proof of any manifest here *)
      assert (In p (places tp t)). {
        eapply in_plc_term; intuition; subst.
        find_rewrite; eauto.
      }
      eapply end_to_end_mangen_supports_all; eauto.
  - match goal with
    | H : manifest_compiler _ _ _ = _ |- _ => rewrite H
  end; eauto.
  Unshelve. eapply "Plc"%string.
  (* eapply end_to_end_mangen_subsumes in H0; eauto;
  destruct_conjs; rewrite <- H2 in H3.
  
  eapply manifest_generator_compiler_soundness_distributed; eauto. *)
Qed.

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
Definition end_to_end_mangen (ls:list (Evidence*Plc)) (ts: list (Term*Plc)) : EnvironmentM := 
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
  (forall t' att_sess aspBin uuid conf ev,
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
      simpl in *; intuition; eauto; try monad_unfold; try congruence).
    unfold generate_ASP_dispatcher, generate_ASP_dispatcher' in *; simpl in *; intuition.
    * unfold generate_ASP_dispatcher, generate_ASP_dispatcher' in *; simpl in *; intuition.  
      ff; simpl in *.
      build_cvm; simpl in *.

  subst.
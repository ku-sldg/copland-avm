(*  Primary results for Manifest Compiler Soundness (for Appraisal).
      Namely, that the compiler outputs a collection of manifests that support 
      appraisal execution over the input evidence.  *)

Require Import Manifest Manifest_Compiler Manifest_Generator ID_Type
  Maps Term_Defs List Cvm_St Cvm_Impl ErrorStMonad_Coq StructTactics 
  Cvm_Monad EqClass Manifest_Admits Auto.
Require Import Manifest_Generator_Facts Eqb_Evidence ManCompSoundness.

Require Import Coq.Program.Tactics Lia.

Import ListNotations.

Fixpoint am_config_support_exec_app (e : Evidence) (ac : AM_Config) : Prop :=
    match e with
    | mt => True 
    | nn _ => True (* TODO: how to account for nonce handling? *)
    | uu p fwd ps e' => 
        let need_appr_asp :=
          let '(asp_paramsC att_id arg targ targ_id) := ps in
          match map_get (ASP_to_APPR_ASP_Map ac) att_id with
          | Some appr_asp => 
            (forall rawEv, 
            (exists res, ac.(aspCb) (asp_paramsC appr_asp arg targ targ_id) rawEv = resultC res)
            \/
            (exists errStr, ac.(aspCb) (asp_paramsC appr_asp arg targ targ_id) rawEv = errC (Runtime errStr))
            )
          | None => False
          end
        in
        match fwd with 
        | ENCR => 
            match ps with 
            | asp_paramsC _ _ p _ => 
                ((exists res, 
                  ac.(pubKeyCb) p = resultC res) \/ 
                (exists errStr, ac.(pubKeyCb) p = errC (Runtime errStr))) /\ 
                am_config_support_exec_app e' ac /\
                need_appr_asp
            end
        | (EXTD n) => 
            am_config_support_exec_app e' ac /\
            need_appr_asp
        | KEEP => 
            am_config_support_exec_app e' ac /\
            need_appr_asp
        | _ => True
        end
    | ss e1 e2 => 
        exists ac1 ac2, 
        (am_config_support_exec_app e1 ac1) /\ 
        (am_config_support_exec_app e2 ac1) /\ 
        supports_am ac1 ac /\
        supports_am ac2 ac
    end.

Require Import AM_St Impl_appraisal.

Fixpoint nonce_ids_et' (et:Evidence) (ls:list N_ID) : list N_ID :=
  match et with
  | mt => ls
  | nn nid => nid :: ls 
  | ss et1 et2 => (nonce_ids_et' et2 (nonce_ids_et' et1 ls))
  | uu _ _ _ et' => nonce_ids_et' et' ls
  end.

Definition nonce_ids_et (et:Evidence) : list N_ID :=
  nonce_ids_et' et [].

Definition has_nonces (nids: list N_ID) (m:MapC N_ID BS) : Prop := 
  forall nid, 
  In nid nids -> 
  (
    exists bs, 
    map_get m nid = Some bs
  ).

Lemma peel_bs_am_contra : forall ls st st' e (P:Prop),
  length ls > 0 -> 
  peel_bs_am ls st = (errC e, st') -> 
  P. 
Proof.
  intros.
  assert (exists v, ls = [v]).
  {
    destruct ls; ff.
  }
  destruct_conjs.
  subst.
  unfold peel_bs_am in *.
  solve_by_inversion.
Qed.

Lemma peel_bs_am_immut : forall ls st x st',
peel_bs_am ls st = (x, st') -> 
st = st'.
Proof.
intros.
destruct ls; ff.
Qed.

Lemma peel_n_am_immut : forall n ls st x st',
peel_n_am n ls st = (x, st') -> 
st = st'.
Proof.
induction n; intuition; repeat ff; eauto.
Qed.
Local Hint Resolve peel_n_am_immut : core.

Require Import Appraisal_Defs.


Lemma firstn_works{A:Type}: forall (ls:list A) n,
length ls >= n -> 
n = length (firstn n ls).
Proof.
intros.
symmetry.
eapply firstn_length_le.
lia.
Qed.

Lemma decrypt_amst_immut : forall st st' b ps et res,
decrypt_bs_to_rawev' b ps et st = (res, st') -> 
st = st'.
Proof.
intros.
unfold decrypt_bs_to_rawev' in *.
monad_unfold.
repeat (ff; try unfold am_falim in * ; eauto).
Qed.
Local Hint Resolve decrypt_amst_immut : core.

Lemma peel_bs_am_works : forall ls st st' r,
length ls > 0 -> 
peel_bs_am ls st = (r,st') ->
exists res, 
r = resultC res.
Proof.
intros.
destruct ls; ff.
eexists. eauto.
Qed.

Lemma peel_n_am_works : forall n ls st st' r,
length ls >= n -> 
peel_n_am n ls st = (r,st') ->
exists res, 
r = resultC res.
Proof.
  induction n; intuition; repeat ff; eauto.
  assert (length l >= n) by lia. eauto.
Qed.

Lemma peel_n_am_res_spec : forall n ls st st' r0 r1,
  peel_n_am n ls st = (resultC (r0, r1),st') ->
  ls = r0 ++ r1 /\ length r0 = n.
Proof.
  induction n; intuition; repeat ff; eauto;
  find_eapply_hyp_hyp; intuition; ff.
Qed.

Lemma peel_n_am_err_spec : forall n ls st st' s,
  peel_n_am n ls st = (errC s,st') ->
  length ls < n.
Proof.
  induction n; intuition; repeat ff; eauto; subst; 
  try find_eapply_hyp_hyp; lia.
Qed.

Lemma has_nonces_cumul : forall et ls m,
has_nonces (nonce_ids_et' et ls) m -> 
has_nonces ls m.
Proof.
  induction et; intros; ff.
  unfold has_nonces in *.
  ff.
  intros.
  ff.
Qed.

Lemma has_nonces_cumul' : forall et ls ls' m,
has_nonces (nonce_ids_et' et ls) m -> 
has_nonces ls' m ->
has_nonces (nonce_ids_et' et ls') m.
Proof.
  induction et; intros; ff.
  -
  unfold has_nonces in *.
  ff.
  intros.
  ff.
  -
  unfold has_nonces in *.
  ff.
  intros.
  ff.
  eauto.
  -
    assert (has_nonces (nonce_ids_et' et1 ls) m).
    eapply has_nonces_cumul.
    eassumption.

    eapply IHet2.
    eassumption.
    eapply has_nonces_cumul; eauto.
Qed.

Lemma peel_bs_am_st_immut : forall ls st r st',
  peel_bs_am ls st = (r, st') -> 
  st = st'.
Proof.
  induction ls; simpl in *; intuition; eauto.
  - invc H; eauto. 
  - invc H; eauto. 
Qed.
Local Hint Resolve peel_bs_am_st_immut : core.

Lemma checkNonce'_st_immut : forall n b st r st',
  checkNonce' n b st = (r, st') -> 
  st = st'.
Proof.
  unfold checkNonce'; repeat (ff; intuition; eauto).
Qed.
Local Hint Resolve checkNonce'_st_immut : core.

Lemma check_asp_EXTD' : forall a p r1 r2 st st' r,
  Appraisal_Defs.check_asp_EXTD' a p r1 r2 st = (r, st') -> 
  st = st'.
Proof.
  unfold check_asp_EXTD'; repeat (ff; intuition; eauto).
Qed.
Local Hint Resolve check_asp_EXTD' : core.

Lemma gen_appraise_AM_immut : forall et ls st st' r,
gen_appraise_AM et ls st = (r, st') -> 
st = st'.
Proof.
  intros.
  generalizeEverythingElse et. 
  induction et; intros; simpl in *; intuition; eauto.
  - ff.
  - repeat ff; simpl in *; eauto;
    eapply peel_bs_am_st_immut in Heqp; subst; eauto. 
  - repeat (break_match; try unfold res_bind, ";;", ret, am_failm in *; 
      simpl in *; subst; intuition; eauto; 
      try find_injection; try congruence); eauto;
    repeat match goal with
    | H : peel_n_am _ _ ?a = (_, ?a') |- _ =>
        assert (a = a') by eauto; subst; eauto;
        clear H
    | H : Appraisal_Defs.check_asp_EXTD' _ _ _ _ ?a = (_, ?a') |- _ =>
        assert (a = a') by eauto; subst; eauto;
        clear H
    | H : peel_bs_am _ ?a = (_, ?a') |- _ =>
        assert (a = a') by eauto; subst; eauto;
        clear H
    | H : decrypt_bs_to_rawev' _ _ _ ?a = (_, ?a') |- _ =>
        assert (a = a') by eauto; subst; eauto;
        clear H
    end.
  - repeat ff;
    repeat find_eapply_hyp_hyp; subst; eauto.
Qed.

Theorem well_formed_am_config_impl_executable_app : forall et amConf ls,
  am_config_support_exec_app et amConf ->
  et_size et = length ls -> 
  forall st,
  supports_am amConf (st.(amConfig)) ->
  has_nonces (nonce_ids_et et) (st.(am_nonceMap)) -> 
    (exists ec st',
        (gen_appraise_AM et ls) st = (resultC ec, st')) \/ 
    (exists st' errStr,
        (gen_appraise_AM et ls) st = (errC (am_dispatch_error (Runtime errStr)), st')).
Proof.
  intros.
  generalizeEverythingElse et.
  induction et; intros; intuition; subst; eauto.
  - (* mt case *)
    ff; eauto.
  - (* nn case *)
    ff.
    destruct r.
    + eapply peel_bs_am_contra; try eauto; try lia.
    + repeat ff; intuition; eauto.
      unfold has_nonces, Appraisal_Defs.checkNonce' in *.
      repeat ff; intuition; eauto.
      assert (exists bs, map_get (am_nonceMap st) n = Some bs) by eauto.
        assert (st = a0).
        {
          intuition; eauto.
          unfold am_failm in *.
          ff.
          eapply peel_bs_am_immut; eauto.
        }
        subst.
        unfold am_failm in *.
        ff.
        find_rewrite; break_exists; congruence.
  - (* uu case *)

    simpl in *.
    repeat break_match; simpl in *; subst; cbn;
    intuition; eauto;
    try (left; repeat eexists; eauto; congruence);
    simpl in *; destruct_conjs; 
    simpl in *; intuition; eauto;
    monad_unfold;
    simpl in *; repeat break_let;
    assert (st = a) by eauto; subst;
    assert (exists res, r = resultC res) by (
      try (eapply peel_bs_am_works; eauto; lia);
      try (find_apply_lem_hyp peel_n_am_works; eauto; lia));
    destruct_conjs; subst; repeat break_let;
    break_match; intuition; eauto; repeat find_injection;
    repeat find_rewrite; eauto;
    unfold decrypt_bs_to_rawev' in *;
    monad_unfold; repeat ff; eauto;
    unfold am_failm, check_et_size, check_asp_EXTD in *;
    simpl in *;
    try match goal with
    | H : forall _ : RawEv, _ \/ _,
      H' : aspCb _ _ ?rawev = _ |- _ => 
      let H'' := fresh "H" in
      let H''' := fresh "H" in
      let res := fresh "res" in
      destruct (H rawev) as [H'' | H''];
      destruct H'' as [res H''']; eauto
    end; ff;
    simpl in *; repeat find_injection; eauto;
    unfold supports_am in *; intuition;
    repeat (find_eapply_hyp_hyp; try find_rewrite; try find_injection);
    try congruence; eauto;
    try (find_apply_lem_hyp decrypt_prim_runtime; subst; eauto; congruence); eauto.
    * rewrite PeanoNat.Nat.eqb_eq in *;
      edestruct IHet; intuition; eauto;
      break_exists; find_rewrite; repeat find_injection;
      eauto; congruence.
    * find_rewrite; find_injection; eauto.
    * edestruct IHet with (ls := r1); intuition; eauto;
      break_exists; find_rewrite; repeat find_injection;
      eauto; try congruence.
      find_eapply_lem_hyp peel_n_am_res_spec; intuition; subst.
      rewrite app_length in *; lia.
  - (* ss case *)
    cbn in *.
    destruct_conjs.

    edestruct IHet1 with (ls := firstn (et_size et1) ls).
    eassumption.
    2: {
      eapply supports_am_trans; eauto.
    }
    2: {
      unfold nonce_ids_et.
      eapply has_nonces_cumul.
      eassumption.
    }

    (* 
    firstn_length_le:
  forall [A : Type] (l : list A) [n : nat],
  n <= length l -> length (firstn n l) = n
    
    *)

    eapply firstn_works.
    lia.

    destruct_conjs.

    monad_unfold.
    break_let.
    rewrite H10 in *.

    break_match.
    subst.
    solve_by_inversion.

    break_let.
    break_let.

    edestruct IHet2 with (ls := skipn (et_size et1) ls).
    eassumption.

    2: {
      unfold supports_am in *.
      destruct_conjs; repeat ff; intuition; eauto.
    }

    2: {
      eapply has_nonces_cumul'.
      eassumption.
      unfold has_nonces.
      intros.
      solve_by_inversion.
    }

    assert (length (skipn (et_size et1) ls) = length ls - (et_size et1)).
    {
      eapply skipn_length.
    }
    lia.

    destruct_conjs.

      assert (st = H12).
      {
        eapply gen_appraise_AM_immut; eauto.
      }
      subst.

      assert (a = a2).
      {
        eapply gen_appraise_AM_immut; eauto.
      }
      subst.
      invc H10.
      
      assert (H12 = H9).
      {
        eapply gen_appraise_AM_immut; eauto.
      }
      subst.

      find_rewrite.
      ff.
      
      left.
      eauto.


      destruct_conjs.


      invc H10.

      assert (H9 = a2).
      {
        eapply gen_appraise_AM_immut; eauto.
      }
      subst.

      assert (st = a2).
      {
        eapply gen_appraise_AM_immut; eauto.
      }
      subst.

      find_rewrite.

      ff.

      right. eauto.

      destruct_conjs.

      monad_unfold.

      break_let.
      right.
      ff.
      eauto.
Qed.

Fixpoint manifest_support_term_app (m : Manifest) (al : AM_Library) (e : Evidence) : Prop :=
    match e with
    | mt => True 
    | nn _ => True (* TODO: should we account for nonce presence here? *)
    | uu p fwd ps e' => 
        let appr_asp_sup :=
          let '(asp_paramsC att_id arg targ targ_id) := ps in
          match map_get (ASP_Compat_Map al) att_id with
          | Some appr_asp => 
            In_set appr_asp m.(asps)
          | None => False
          end
        in
        match fwd with 
        | (EXTD n) => 
          match ps with 
          | asp_paramsC a _ targ  _ => 
              manifest_support_term_app m al e' /\
              appr_asp_sup
          end
        | ENCR => 
        match ps with 
        | asp_paramsC _ _ p _ =>
            In_set p m.(pubKeyPlcs) /\ 
            manifest_support_term_app m al e' /\
            appr_asp_sup
        end

        | KEEP => 
            manifest_support_term_app m al e' /\
            appr_asp_sup

        | _ => True
        end
        (* TODO:  support other fwd types here in the future... *)
    | ss e1 e2 => 
        manifest_support_term_app m al e1 /\ 
        manifest_support_term_app m al e2
    end.

Definition lib_config_compatible (al : AM_Library) (ac : AM_Config) : Prop :=
  forall a0 a',
    map_get (ASP_Compat_Map al) a0 = Some a' ->
    map_get (ASP_to_APPR_ASP_Map ac) a0 = Some a'.

Theorem manifest_support_am_config_impl_am_config_app: forall et absMan amConf al,
    manifest_support_am_config absMan amConf ->
    lib_config_compatible al amConf ->
    manifest_support_term_app absMan al et ->
    am_config_support_exec_app et amConf.
Proof.
  induction et; simpl in *; intuition; eauto;
  unfold manifest_support_am_config in *; intuition; eauto.
  - repeat (try break_match; simpl in *; intuition; eauto);
    unfold lib_config_compatible in *; intuition; 
    repeat (find_eapply_hyp_hyp; try find_rewrite; try find_injection);
    simpl in *; intuition; eauto; try congruence.
  - repeat (try break_match; simpl in *; intuition; eauto).  
    pose proof (IHet1 absMan amConf al); 
      pose proof (IHet2 absMan amConf); intuition.
      repeat eexists; eauto.
  Unshelve.
  all: eauto.
  all: eapply nil.
Qed.

Lemma manifest_supports_term_sub_app : forall m1 m2 et al,
  manifest_subset m1 m2 ->
  manifest_support_term_app m1 al et -> 
  manifest_support_term_app m2 al et.
Proof.
  intros.
  generalizeEverythingElse et.
  induction et; intros; ff.
  - (* asp case *)
    subst.
    unfold manifest_subset in H. 
    destruct_conjs.
    ff; subst; intuition; eauto;
    eapply IHet; eauto; unfold manifest_subset; eauto.
  -
    split; 
    destruct_conjs; ff; eauto.
Qed.

Lemma manifest_generator_app_cumul : forall et m1 m1' m2 al,
  manifest_subset m1 m2 ->
  manifest_generator_app'' et al m2 = resultC m1' ->
  manifest_subset m1 m1'.
Proof.
  intros.
  generalizeEverythingElse et.
  induction et; intros; ff; eauto.
  - (* uu case *)
    subst; ff; eauto.
    + (* ENCR *)

    subst.

    unfold pubkey_manifest_update in *.
    break_let.
    subst.
    unfold manifest_subset in *.
    simpl in *.
    destruct_conjs.

    edestruct IHet; eauto;
    simpl in *; intuition; eauto;
    find_apply_hyp_hyp; eauto.
    * eapply H4; eauto;
      eapply in_set_add; eauto.
    * eapply H5; eauto;
      eapply in_set_add; eauto.

    + (* EXTD *)

    unfold aspid_manifest_update in *.
    break_let.
    subst.
    unfold manifest_subset in *.
    simpl in *.
    destruct_conjs.

    edestruct IHet; intuition; eauto;
    simpl in *.
    find_apply_hyp_hyp; eauto.
    eapply H4.
    eapply in_set_add; eauto.
    + subst; unfold aspid_manifest_update in *;
    break_let.
    subst.
    unfold manifest_subset in *.
    simpl in *.
    destruct_conjs.

    edestruct IHet; eauto;
    simpl in *; intuition; eauto;
    find_apply_hyp_hyp; eauto.
    eapply H4; eauto.
    eapply in_set_add; eauto.
    
  - (* ss case *)
    ff; eauto.
Qed.

Lemma manifest_generator_app_cumul' : forall et m1 al m1',
  manifest_generator_app'' et al m1 = resultC m1' ->
  manifest_subset m1 m1'.
Proof.
  intros.
  eapply manifest_generator_app_cumul.
  eapply manifest_subset_refl.
  eauto.
Qed.


Lemma asdf_app : forall et1 et2 absMan m m' al,
  manifest_generator_app'' et1 al m = resultC m' ->
  manifest_generator_app'' et2 al m' = resultC absMan ->
  exists m'',
  manifest_generator_app'' et1 al m = resultC m'' /\ 
  manifest_subset m'' absMan.
  Proof.
    intros.
    eexists.
    split; try reflexivity.
    rewrite <- H; eauto.
    eapply manifest_generator_app_cumul'; eauto.
Qed.

Theorem man_gen_old_always_supports_app : forall et oldMan absMan al,
  manifest_generator_app'' et al oldMan = resultC absMan ->
  manifest_support_term_app absMan al et.
Proof.
  induction et; intuition;
    repeat (try break_match; 
      unfold app_aspid_manifest_update in *;
      (*
      unfold manifest_generator_app' in *;
      unfold manifest_generator_app'' in *; *)
      unfold aspid_manifest_update, pubkey_manifest_update in *;
      subst; simpl in *; intuition; eauto; try congruence;
      repeat find_rewrite;
      repeat find_injection;
      simpl in * );
    try (rewrite mapC_get_works in *; simpl in *; repeat find_injection; simpl in *; intuition; eauto; congruence); 
    repeat (ff; simpl in *; subst; intuition; eauto);
  match goal with
  | H : manifest_generator_app'' _ _ ?m' = resultC ?m |- _ =>
      assert (manifest_subset m' m) by (eapply manifest_generator_app_cumul'; eauto);
      unfold manifest_subset in *;
      intuition; simpl in *; eauto
  end.
  - eapply H2; simpl in *.
    unfold pubkey_manifest_update;
    ff; eauto;
    eapply manadd_In_add.
  - repeat find_eapply_hyp_hyp.
    eapply manifest_supports_term_sub_app; eauto;
    unfold manifest_subset; intuition.
Qed.

Lemma lib_config_compatible_man_comp : forall al aspBin absMan,
  lib_config_compatible al (manifest_compiler absMan al aspBin).
Proof.
  destruct absMan, al;
  simpl in *.
  unfold lib_config_compatible; intuition.
Qed.


Theorem manifest_generator_compiler_soundness_app : forall et ls oldMan absMan amLib amConf aspBin,
  (* map_get (manifest_generator t tp) p = Some absMan -> *)
  manifest_generator_app'' et amLib oldMan = resultC absMan ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib aspBin = amConf ->
  et_size et = length ls ->
  forall st,

  st.(amConfig) = amConf ->

  has_nonces (nonce_ids_et et) (st.(am_nonceMap)) -> 

    ( 

    exists ec st',
         (gen_appraise_AM et ls) st = (resultC ec, st')) \/ 
    (exists st' errStr,
         (gen_appraise_AM et ls) st = (errC (am_dispatch_error (Runtime errStr)), st')
    ).
Proof.
  intros.
  assert (supports_am amConf (st.(amConfig))) by (find_rewrite; eauto using supports_am_refl).

  eapply well_formed_am_config_impl_executable_app.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config_app.
    * eapply manifest_support_am_config_compiler; eauto.
    * eapply lib_config_compatible_man_comp.


    * (* NOTE: This is the important one, substitute proof of any manifest here *)
      eapply man_gen_old_always_supports_app; 
      eassumption.

  -
  eassumption.
  - 
    rewrite H1; eauto.
  - 
   eassumption.
Qed. 

Require Import Manifest_Generator_Union Manifest_Generator_Helpers.

Lemma mangen_plcEvidence_list_exists : forall ls et tp p m al env,
  In (et, tp) ls ->
  manifest_generator_app et tp al = resultC env ->
  map_get env p = Some m ->
  forall env',
    mangen_plcEvidence_list_union ls al = resultC env' ->
    exists m', map_get env' p = Some m'.
Proof.
  intuition.
  unfold mangen_plcEvidence_list_union in *;
  induction ls; simpl in *; intuition; subst; eauto;
  ff; try (eexists; intuition; congruence);
  unfold res_bind in *; ff; eauto;
  erewrite manifest_env_union_map_one; eauto. 
  - unfold manifest_generator_plcEvidence_list in Heqr;
    congruence. 
  - unfold manifest_generator_plcEvidence_list in *;
    repeat find_rewrite; repeat find_injection. 
    pose proof (result_map_spec _ _ _ _ H3 Heqr2).
    break_exists; intuition; eauto;
    repeat find_rewrite; repeat find_injection.
    clear H Heqr2.
    unfold env_list_union.
    eauto.
    pose proof (manifest_part_of_fold_ind_impl_fold _ _ _ _ H5 H1 e_empty).
    break_exists; intuition.
    eauto.
Qed.
Global Hint Resolve mangen_plcTerm_list_exists : core.

Lemma mangen_plcEvidence_list_spec : forall ls et tp env envL al,
  In (et, tp) ls ->
  manifest_generator_plcEvidence_list ls al = resultC envL ->
  manifest_generator_app et tp al = resultC env ->
  In env envL.
Proof.
  induction ls; simpl in *; intuition; subst; eauto;
  simpl in *;
  unfold manifest_generator_plcEvidence_list in *; simpl in *;
  ff;
  unfold res_bind in *; repeat ff; eauto.
Qed.
Global Hint Resolve mangen_plcTerm_list_spec : core.

Lemma mangen_plcEvidence_list_subsumes : forall ls p m envL al,
  mangen_plcEvidence_list_union ls al = resultC envL ->
  map_get envL p = Some m ->
  (forall et tp,
    In (et,tp) ls ->
    (forall env' m', 
      manifest_generator_app et tp al = resultC env' ->
      map_get env' p = Some m' ->
      manifest_subset m' m
    )
  ).
Proof.
  intuition; unfold mangen_plcEvidence_list_union in *.
  ff.
  eapply manifest_env_list_union_subsumes; eauto.
  eapply mangen_plcEvidence_list_spec; eauto.
Qed.
Global Hint Resolve mangen_plcTerm_list_subsumes : core.


Lemma mangen_plcEvidence_subset_end_to_end_mangen : forall ls et tp al,
  In (et, tp) ls ->
  (forall m m' p,
    forall envL, 
      mangen_plcEvidence_list_union ls al = resultC envL ->
      map_get envL p = Some m' ->
      forall ts envL', 
        end_to_end_mangen' ls ts al = resultC envL' ->
        map_get envL' p = Some m ->
        manifest_subset m' m
  ).
Proof.
  intuition; unfold end_to_end_mangen' in *.
  ff.
  pose proof (manifest_env_union_always_subset).
  find_eapply_lem_hyp manifest_env_union_always_subset.
  intuition.
Qed.
Global Hint Resolve mangen_plcTerm_subset_end_to_end_mangen : core.

Lemma mangen_subset_end_to_end_mangen_app : forall ls et tp,
  In (et, tp) ls ->
  (forall m m' p al env,
    manifest_generator_app et tp al = resultC env ->
    map_get env p = Some m' ->
    forall ts env', 
      end_to_end_mangen' ls ts al = resultC env' ->
      map_get env' p = Some m ->
      manifest_subset m' m
  ).
Proof.
  intuition; unfold end_to_end_mangen' in *; ff.
  find_eapply_lem_hyp manifest_env_union_always_subset; intuition.
  unfold mangen_plcEvidence_list_union in *.
  ff.
  pose proof (mangen_plcEvidence_list_spec _ _ _ _ _ _ H Heqr0 H0).
  destruct (map_get (env_list_union l) p) eqn:E; ff.
  - pose proof (H2 _ eq_refl).
    clear H2 H4.
    unfold env_list_union in E.
    pose proof (manifest_part_of_fold_ind_impl_fold _ _ _ _ H3 H1 e_empty); break_exists; intuition; repeat find_rewrite; 
    try find_injection; eapply manifest_subset_trans; eauto.
  - unfold env_list_union in *.
    pose proof (manifest_part_of_fold_ind_impl_fold _ _ _ _ H3 H1 e_empty); break_exists; intuition; congruence.
Qed.
Global Hint Resolve mangen_subset_end_to_end_mangen : core.
(*
Lemma mangen_exists_end_to_end_mangen : forall ts ls p m,
  map_get (end_to_end_mangen ls ts) p = Some m ->
  (forall et tp,
    In (et, tp) ls ->
   (* In p (places tp t) -> *)
    ((* forall t',
      In t' (place_terms t tp p) -> *)
      exists m', map_get (manifest_generator_app et tp) p = Some m'
    )
  ).
Proof.
  intuition.
Qed.
Global Hint Resolve mangen_exists_end_to_end_mangen : core.
*)

(*
Lemma mangen_exists_end_to_end_mangen_app : forall ts ls p m,
  map_get (end_to_end_mangen ls ts) p = Some m ->
  (forall et tp,
    In (et, tp) ls ->
    (* In p (places tp t) -> *)
    ((* forall t',
      In t' (place_terms t tp p) -> *)
      exists m', map_get (manifest_generator_app et tp) tp = Some m'
    )
  ).
Proof.
  intuition.
  Admitted.
Global Hint Resolve mangen_exists_end_to_end_mangen_app : core.
*)

Lemma mangen_exists_end_to_end_mangen_app :
  (forall et tp al env,
    manifest_generator_app et tp al = resultC env ->
    exists m', map_get env tp = Some m'
  ).
Proof.
  intuition.
  unfold manifest_generator_app in *.
  ff.
  assert (String.eqb tp tp = true).
  {
    rewrite String.eqb_eq.
    auto.
  }
  unfold manifest_generator_app', manifest_update_env_res in *.
  simpl in *; ff; find_rewrite; eauto.
Qed.
Global Hint Resolve mangen_exists_end_to_end_mangen_app : core.



Lemma mangen_app_tp_get : forall et tp x al env,
  manifest_generator_app et tp al = resultC env ->
  map_get env tp = Some x ->
  manifest_generator_app'' et al (myPlc_manifest_update tp empty_Manifest) = resultC x.
Proof.
  intros.
  unfold manifest_generator_app in *.
  unfold manifest_generator_app' in *.
  unfold manifest_update_env_res in *.
  unfold e_empty in *.
  ff.
  assert (String.eqb tp tp = true).
  {
    rewrite String.eqb_eq.
    trivial.
  }
  repeat find_rewrite.
  ff.
Qed.

Lemma end_to_end_mangen_supports_all_app : forall ts ls tp m env al,
  end_to_end_mangen' ls ts al = resultC env ->
  map_get env tp = Some m ->
  (forall et, 
    In (et, tp) ls ->
    (* In p (places tp t) -> *)
    ((* forall t',
      In t' (place_terms t tp p) -> *)
      manifest_support_term_app m al et
    )
  ).
Proof.
  intuition.
  
  destruct (manifest_generator_app et tp al) eqn:E.
  - unfold end_to_end_mangen' in *; ff.
    unfold mangen_plcEvidence_list_union in *; ff.
    unfold manifest_generator_plcEvidence_list in *; ff.
    pose proof (result_map_spec _ _ _ _ H1 Heqr0);
    break_exists; intuition; congruence.
  - pose proof (mangen_exists_end_to_end_mangen_app et tp al _ E).
    break_exists.
    pose proof (mangen_subset_end_to_end_mangen_app _ _ _ H1 _ _ _ _ _ E H2 _ _ H H0). 
    eapply manifest_supports_term_sub_app; eauto.
    eapply man_gen_old_always_supports_app.
    eapply mangen_app_tp_get; eauto.
Qed.
Global Hint Resolve end_to_end_mangen_supports_all : core.



Theorem manifest_generator_compiler_soundness_distributed_multiterm_app : forall et ts ls bs tp absMan amLib amConf aspBin env,
  end_to_end_mangen' ls ts amLib = resultC env ->
  map_get env tp = Some absMan -> 
  In (et,tp) ls ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib aspBin = amConf ->
  et_size et = length bs ->
  forall st,

  supports_am amConf st.(amConfig)  ->

  has_nonces (nonce_ids_et et) (st.(am_nonceMap)) -> 

    ( 
    exists ec st',
         (gen_appraise_AM et bs) st = (resultC ec, st')) \/ 
    (exists st' errStr,
         (gen_appraise_AM et bs) st = (errC (am_dispatch_error (Runtime errStr)), st')
    ).
Proof.
  intros.
  eapply well_formed_am_config_impl_executable_app.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config_app.
    * eapply manifest_support_am_config_compiler; eauto.
    * eapply lib_config_compatible_man_comp.
    * (* NOTE: This is the important one, substitute proof of any manifest here *)
      eapply end_to_end_mangen_supports_all_app; eauto.
  - find_rewrite; eauto.
  - match goal with
    | H: manifest_compiler _ _ _ = _ |- _ => rewrite H; eauto
    end.
  - eauto.
Qed.

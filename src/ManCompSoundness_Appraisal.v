(*  Primary results for Manifest Compiler Soundness (for Appraisal).
      Namely, that the compiler outputs a collection of manifests that support 
      appraisal execution over the input evidence.  *)

Require Import Manifest Manifest_Compiler Manifest_Generator AbstractedTypes
  Maps Term_Defs List Cvm_St Cvm_Impl ErrorStMonad_Coq StructTactics 
  Cvm_Monad EqClass Manifest_Admits Auto.
Require Import Manifest_Generator_Facts Eqb_Evidence.

Require Import Coq.Program.Tactics Lia.

Import ListNotations.

(*
Set Nested Proofs Allowed.
*)


Definition supports_am_app (ac1 ac2 : AM_Config) : Prop :=
  (forall aid l targ targid p' ev ev',
      (forall res, 
      ac1.(app_aspCb) (asp_paramsC aid l targ targid) p' ev ev' = resultC res ->
      ac2.(app_aspCb) (asp_paramsC aid l targ targid) p' ev ev' = resultC res)) /\
  (forall aid l targ targid p' ev ev' errStr,
      ac1.(app_aspCb) (asp_paramsC aid l targ targid) p' ev ev' = errC (Runtime errStr) ->
      ac2.(app_aspCb) (asp_paramsC aid l targ targid) p' ev ev' = errC (Runtime errStr)) /\ 
  (forall p,
      (forall res, 
      ac1.(pubKeyCb) p = resultC res ->
      ac2.(pubKeyCb) p = resultC res)) /\
  (forall p errStr,
      ac1.(pubKeyCb) p = errC (Runtime errStr) ->
      ac2.(pubKeyCb) p = errC (Runtime errStr)).

Theorem supports_am_app_refl : forall ac1,
  supports_am_app ac1 ac1.
Proof.
  unfold supports_am_app; intuition.
Qed.

Theorem supports_am_app_trans : forall ac1 ac2 ac3,
  supports_am_app ac1 ac2 ->
  supports_am_app ac2 ac3 ->
  supports_am_app ac1 ac3.
Proof.
  unfold supports_am_app; intuition.
Qed.

Local Hint Resolve supports_am_app_refl : core.
Local Hint Resolve supports_am_app_trans : core.


Fixpoint am_config_support_exec_app (e : Evidence) (ac : AM_Config) : Prop :=
    match e with
    | mt => True 
    | nn _ => True (* TODO: how to account for nonce handling? *)
    | uu p fwd ps e' => 
        match fwd with 
        | ENCR => 
            match ps with 
            | asp_paramsC _ _ p _ => 
                ((exists res, 
                  ac.(pubKeyCb) p = resultC res) \/ 
                (exists errStr, ac.(pubKeyCb) p = errC (Runtime errStr))) /\ 
                am_config_support_exec_app e' ac
            end
        | EXTD => 
            forall bs ls, 
            (
            ( exists res, ac.(app_aspCb) ps p bs ls = resultC res) \/
              (exists errStr, ac.(app_aspCb) ps p bs ls = errC (Runtime errStr))) /\ 

            am_config_support_exec_app e' ac
        | KEEP => 
            am_config_support_exec_app e' ac
        | _ => True
        end
    | ss e1 e2 => 
        exists ac1 ac2, 
        (am_config_support_exec_app e1 ac1) /\ 
        (am_config_support_exec_app e2 ac1) /\ 
        supports_am_app ac1 ac /\
        supports_am_app ac2 ac
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

Lemma gen_appraise_AM_immut : forall et ls st st' r,
gen_appraise_AM et ls st = (r, st') -> 
st = st'.
Proof.
  intros.
  generalizeEverythingElse et. 
  induction et; intros.
  -
    ff.
  -
    ff.
    ff.
      +
        eapply peel_bs_am_immut; eauto.
      +
        assert (st = a).
        {
          eapply peel_bs_am_immut; eauto.
        }
        subst.

        unfold checkNonce' in *.
        repeat ff.
      +
      assert (st = a).
      {
        eapply peel_bs_am_immut; eauto.
      }
      subst.

      unfold checkNonce' in *.
      repeat ff.
  -
    cbn in *.
    break_match.
    +
    ff.
    + (* ENCR *)
    monad_unfold.
    break_let.
    break_match.
    ++
    ff.
    eapply peel_bs_am_immut; eauto.
    ++
    break_let.
    break_let.
    break_let.
    subst.
    invc H.
    break_match.
    +++
    assert (st = a0) by (eapply peel_bs_am_immut; eauto).
    subst.
    invc Heqp1.
    eapply decrypt_amst_immut; eauto.
    +++
    break_let.
    break_let.
    invc Heqp1.
    assert (a0 = a2).
    {
      eapply decrypt_amst_immut; eauto.
    }
    subst.
    assert (st = a2) by (eapply peel_bs_am_immut; eauto).
    subst.
    break_match.
    ++++
      invc Heqp2.
      eauto.
    ++++
      invc Heqp2.
      eauto.
  + (* EXTD *)
  monad_unfold.
  break_let.
  break_match.
  ++
  ff.
  eapply peel_bs_am_immut; eauto.
  ++
  break_let.
  break_let.
  break_let.
  subst.
  invc H.
  break_match.
  +++
  assert (st = a0) by (eapply peel_bs_am_immut; eauto).
  subst.
  invc Heqp1.
  unfold check_asp_EXTD' in *.
  monad_unfold.
  break_let.
  ff.
  unfold am_failm in *.
  ff.
  +++
  break_let.
  break_let.
  invc Heqp1.
  assert (a0 = a2).
  {
    invc Heqp3.
    unfold check_asp_EXTD' in *.
    monad_unfold.
    break_let.
    repeat (ff;   unfold am_failm in * ; eauto).
  }
  subst.
  assert (st = a2) by (eapply peel_bs_am_immut; eauto).
  subst.
  break_match.
  ++++
    invc Heqp2.
    eauto.
  ++++
    invc Heqp2.
    eauto.

  +
  subst.
  ff.
  +
  eauto.

  -
  ff.
  ff.
  eauto.
  assert (st = a) by eauto.
  subst.
  eauto.
  assert (st = a) by eauto.
  subst.
  eauto.
Qed.


Theorem well_formed_am_config_impl_executable_app : forall et amConf ls,
  am_config_support_exec_app et amConf ->
  et_size et = length ls -> 
  forall st,
  supports_am_app amConf (st.(amConfig)) ->
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
    repeat eexists.
    left.
    ff.
    repeat eexists.
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
    try (left; eauto; congruence).

    + (* COMP case *)
      left.
      repeat eexists.
    + (* ENCR case *)
      simpl in *.
      destruct_conjs;
      simpl in *; intuition; eauto.

      (* pubkey configured/available *)
      simpl in *.
      monad_unfold.
      break_let.

      assert (st = a).
      {
        eapply peel_bs_am_immut; eauto.
      }
      subst.

      assert (exists res, r = resultC res).
      {

        eapply peel_bs_am_works; eauto; lia.

      }

      destruct_conjs.
      subst.
      repeat break_let.

      break_match.
      +++ (* decrypt error *)
        invc Heqp0.
        unfold decrypt_bs_to_rawev' in *.
        monad_unfold.
        ff.

        ++++
          unfold supports_am_app in *.
          destruct_conjs.
          specialize H6 with (p:=p0) (res:=H).
          find_apply_hyp_hyp.
          find_rewrite.
          solve_by_inversion.

        ++++
          ff.
          pose decrypt_prim_runtime.
          subst.
          find_apply_hyp_hyp.
          unfold am_failm in *.
          ff.
          repeat eexists.
          eauto.
        ++++
          unfold check_et_size in *.
          ff.
          unfold am_failm in *.
          ff.
          repeat eexists.
          eauto.
    +++ (* decrypt success *)
      break_let.
      break_let.
      invc Heqp0.

      break_match.
      ++++
        subst.
        invc Heqp3.

        assert (a = a2).
        {
          eapply decrypt_amst_immut; eauto.
        }
        subst.

        assert ((exists ec st', 
                  gen_appraise_AM et r2 a2  = (resultC ec, st')) \/ 
                (exists st' errStr, 
                  gen_appraise_AM et r2 a2 = (errC (am_dispatch_error (Runtime errStr)), st'))
        ).
        {
          eapply IHet.
          3: {
            eassumption.
          }
          3: {
            eauto.
          }
          eassumption.

          unfold decrypt_bs_to_rawev' in *.
          monad_unfold.
          break_let.
          ff.
          unfold am_failm in *.
          ff.
          unfold check_et_size in *.
          ff.
          unfold am_failm in *.
          ff.
          unfold am_failm in *.
          ff.
          unfold check_et_size in *.
          ff.
          rewrite PeanoNat.Nat.eqb_eq in Heqb0; eauto.
        }
        destruct_conjs.
        door.
        +++++
          find_rewrite.
          solve_by_inversion.
        +++++
        find_rewrite.
        find_injection.
        eauto.
    ++++
    find_injection.
    eauto.
  +   
    ++ (* pubkey NOT configured/available *)
      monad_unfold.
      break_let.

      assert (st = a).
      {
        eapply peel_bs_am_immut; eauto.
      }
      subst.

      assert (exists res, r = resultC res).
      {
        eapply peel_bs_am_works; eauto; lia.
      }
      destruct_conjs.
      subst.
      break_let.
      break_let.
      unfold decrypt_bs_to_rawev' in *.
      monad_unfold.
      break_let.
      invc Heqp2.

      assert (pubKeyCb (amConfig a) p0 = errC (Runtime H)). (* TODO: add errStr *)
      {
        unfold supports_am_app in *.
        destruct_conjs.
        specialize H6 with (p:=p0).
        eauto.
      }
      find_rewrite.
      ff.
      unfold am_failm in *.
      ff.
      eauto.
  + (* EXTD case *)
    ff.

    assert (st = a0).
    {
      eapply peel_bs_am_immut; eauto.
    }
    subst.

    assert (exists res, r = resultC res).
    {
      eapply peel_bs_am_works; eauto; lia.
    }
    destruct_conjs.
    subst.
    repeat break_let.
    invc Heqp2.

    break_match.
    ++ (* check_asp_EXTD error *)
      ff.
      unfold check_asp_EXTD in *.

      specialize H with (bs:= b) (ls:=r0).
      destruct_conjs.
      door.
      +++
        ff.
        unfold supports_am_app in *.
        destruct_conjs.
        destruct a.
        specialize H5 with (aid:=a) (l:=l) (targ:=p0) (targid:=t) (p':=p) (ev:=b) (ev':=r0).
        find_apply_hyp_hyp.
        find_rewrite.
        solve_by_inversion.
      +++
      ff.
      unfold supports_am_app in *.
      destruct_conjs.
      destruct a.
      specialize H1 with (aid:=a) (l:=l) (targ:=p0) (targid:=t) (p':=p) (ev:=b) (ev':=r0).
      find_apply_hyp_hyp.
      find_rewrite.
      ff.
      unfold am_failm in *.
      ff.
      eauto.
    ++ (* check_asp_EXTD succeeds *)
      subst.
      break_let.
      invc Heqp1.

      assert (a0 = a2).
      {
        ff.
      }
      subst.

      specialize H with (bs:=b) (ls:=r0).
      destruct_conjs.
      edestruct IHet.
      eassumption.
      2: {
        eassumption.
      }
      2: {
        eassumption.
      }

      assert (et_size et = length r0).
      {
        assert (length ls = S (length r0)).
        {
          unfold peel_bs_am in *.
          destruct ls; ff.
        }
        lia.
      }
      eassumption.

      destruct_conjs.
      destruct H5.
      +++
        find_rewrite.
        ff.
        eauto.
      +++
      find_rewrite.
      ff.
      eauto.
  + (* KILL case *)
    repeat eexists.
    ff.
    eauto.

  - (* ss case *)
    cbn in *.
    destruct_conjs.

    edestruct IHet1 with (ls := firstn (et_size et1) ls).
    eassumption.
    2: {
      unfold supports_am_app in *.
      destruct_conjs.
      split; try eauto.
      split.
      eauto.
      split; eauto.
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
      unfold supports_am_app in *.
      destruct_conjs.
      split; try eauto.
      split.
      eauto.
      split; eauto.
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

Require Import ManCompSoundness.

Fixpoint manifest_support_term_app (m : Manifest) (e : Evidence) : Prop :=
    match e with
    | mt => True 
    | nn _ => True (* TODO: should we account for nonce presence here? *)
    | uu p fwd ps e' => 
        match fwd with 
        | EXTD => 
          match ps with 
          | asp_paramsC a _ _ _ => 
              In_set (p,a) m.(appraisal_asps) /\ 
              manifest_support_term_app m e'
          end
        | ENCR => 
        match ps with 
        | asp_paramsC _ _ p _ =>
            In_set p m.(pubKeyPlcs) /\ 
            manifest_support_term_app m e'
        end

        | KEEP => 
            manifest_support_term_app m e'

        | _ => True
        end
        (* TODO:  support other fwd types here in the future... *)
    | ss e1 e2 => 
        manifest_support_term_app m e1 /\ 
        manifest_support_term_app m e2
    end.


Theorem manifest_support_am_config_impl_am_config_app: forall et absMan amConf,
    manifest_support_am_config absMan amConf ->
    manifest_support_term_app absMan et ->
    am_config_support_exec_app et amConf.
Proof.
    induction et; simpl in *; intuition; eauto;
    unfold manifest_support_am_config in *; intuition; eauto;
    repeat (try break_match; simpl in *; intuition; eauto).

    - pose proof (IHet1 absMan amConf); 
        pose proof (IHet2 absMan amConf); intuition;
        exists amConf, amConf; eauto.
Qed.

Lemma manifest_supports_term_sub_app : forall m1 m2 et,
manifest_subset m1 m2 ->
manifest_support_term_app m1 et -> 
manifest_support_term_app m2 et.
Proof.
  intros.
  generalizeEverythingElse et.
  induction et; intros; ff.
  - (* asp case *)
    subst.
    unfold manifest_subset in H. 
    destruct_conjs.
    ff.
    + (* ENCR *)
      subst.
      destruct_conjs.
      split; eauto.
      eapply IHet with (m1:=m1).
      unfold manifest_subset.
      eauto.
      ff.  
    +
      subst.
      subst.
      destruct_conjs.
      split; eauto.
      eapply IHet with (m1:=m1).
      unfold manifest_subset.
      eauto.
      ff.
    + 
    subst.
    destruct_conjs.
    eapply IHet with (m1:=m1).
    unfold manifest_subset.
    eauto.
    ff.
  -
    split; 
    destruct_conjs; ff; eauto.
Qed.

Lemma manifest_generator_app_cumul : forall et m1 m2,
  manifest_subset m1 m2 ->
  manifest_subset m1 (manifest_generator_app'' et m2).
Proof.
  intros.
  generalizeEverythingElse et.
  induction et; intros; ff.
  - (* uu case *)
    subst.

    ff.
    + (* ENCR *)

    subst.

    unfold pubkey_manifest_update.
    break_let.
    subst.
    unfold manifest_subset in *.
    simpl in *.
    destruct_conjs.

    edestruct IHet.
    split; eauto.

    destruct_conjs.

    split; intros; eauto.

    split; intros; eauto.

    split; intros; eauto.

    split; intros; eauto.

    find_apply_hyp_hyp.

    eapply H7.
    ff.
    eapply in_set_add; eauto.

    + (* EXTD *)

    unfold app_aspid_manifest_update.
    break_let.
    subst.
    unfold manifest_subset in *.
    simpl in *.
    destruct_conjs.

    edestruct IHet.
    split; eauto.

    destruct_conjs.

    split.

    intros.
    eauto.

    split; intros; eauto.

    simpl in *.

    find_apply_hyp_hyp.

    eapply H5.
    eapply in_set_add; eauto.

    split; eauto.

    split; eauto.
    
  - (* ss case *)
    eauto.
Qed.

Lemma manifest_generator_app_cumul' : forall et m1, 
  manifest_subset m1 (manifest_generator_app'' et m1).
Proof.
  intros.
  eapply manifest_generator_app_cumul.
  eapply manifest_subset_refl.
Qed.


Lemma asdf_app : forall et1 et2 absMan m,
    manifest_generator_app'' et2 
        (manifest_generator_app'' et1 m) = absMan -> 
              
  exists m',
  manifest_generator_app'' et1 m = m' /\ 
  manifest_subset m' absMan.
  Proof.
    intros.
    eexists.
    split; try reflexivity.
    rewrite <- H.
    eapply manifest_generator_app_cumul'.
Qed.

Theorem man_gen_old_always_supports_app : forall et oldMan absMan,
  (*map_get (manifest_generator_app' tp et oldMan) tp = Some absMan -> *)
  manifest_generator_app'' et oldMan = absMan ->
  manifest_support_term_app absMan et.
Proof.
  induction et; intuition;
    repeat (try break_match; 
      unfold app_aspid_manifest_update in *;
      (*
      unfold manifest_generator_app' in *;
      unfold manifest_generator_app'' in *; *)
      unfold pubkey_manifest_update in *;
      subst; simpl in *; intuition; eauto; try congruence;
      repeat find_rewrite;
      repeat find_injection;
      simpl in * );
    try (rewrite mapC_get_works in *; simpl in *; repeat find_injection; simpl in *; intuition; eauto; congruence).

  - (* ENCR case *)
    ff.
    assert (manifest_subset {|
      my_abstract_plc := my_abstract_plc;
      asps := asps;
      appraisal_asps := appraisal_asps;
      uuidPlcs := uuidPlcs;
      pubKeyPlcs := manset_add p0 pubKeyPlcs;
      targetPlcs := targetPlcs;
      policy := policy
    |}
    
    (manifest_generator_app'' et
        {|
          my_abstract_plc := my_abstract_plc;
          asps := asps;
          appraisal_asps := appraisal_asps;
          uuidPlcs := uuidPlcs;
          pubKeyPlcs := manset_add p0 pubKeyPlcs;
          targetPlcs := targetPlcs;
          policy := policy
        |})


    ).
    eapply manifest_generator_app_cumul'.
    unfold manifest_subset in *.
    destruct_conjs.
    eapply H2.
    simpl.
    eapply manadd_In_add.

    - (* EXTD case *)

    ff.
    assert (manifest_subset  {|
      my_abstract_plc := my_abstract_plc;
      asps := asps;
      appraisal_asps := manset_add (p, a0) appraisal_asps;
      uuidPlcs := uuidPlcs;
      pubKeyPlcs := pubKeyPlcs;
      targetPlcs := targetPlcs;
      policy := policy
    |}
    
    (manifest_generator_app'' et
    {|
      my_abstract_plc := my_abstract_plc;
      asps := asps;
      appraisal_asps := manset_add (p, a0) appraisal_asps;
      uuidPlcs := uuidPlcs;
      pubKeyPlcs := pubKeyPlcs;
      targetPlcs := targetPlcs;
      policy := policy
    |})


    ).
    eapply manifest_generator_app_cumul'.
    unfold manifest_subset in *.
    destruct_conjs.
    eauto.
    eapply H0.
    simpl.
    eapply manadd_In_add.

  - (* ss case *)
    ff.
    pose (asdf_app et1 et2 (manifest_generator_app'' et2 
    (manifest_generator_app'' et1 oldMan)) oldMan).

    assert (
      manifest_generator_app'' et2
     (manifest_generator_app'' et1 oldMan) =
   manifest_generator_app'' et2
     (manifest_generator_app'' et1 oldMan)
    ) by reflexivity.

    apply e in H.
    destruct_conjs.

    assert (manifest_support_term_app H et1).
    {
      eauto.
    }

    eapply manifest_supports_term_sub_app.
    eapply H1.
    eassumption.
Qed.

Theorem manifest_generator_compiler_soundness_app : forall et ls oldMan absMan amLib amConf,
  (* map_get (manifest_generator t tp) p = Some absMan -> *)
  manifest_generator_app'' et oldMan = absMan ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
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
  assert (supports_am_app amConf (st.(amConfig))) by ff.

  eapply well_formed_am_config_impl_executable_app.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config_app.
    * eapply manifest_support_am_config_compiler; eauto.


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

Lemma mangen_plcEvidence_list_exists : forall ls et tp p m,
  In (et, tp) ls ->
  map_get (manifest_generator_app et tp) p = Some m ->
  exists m', map_get (mangen_plcEvidence_list_union ls) p = Some m'.
Proof.
  intuition.
  unfold mangen_plcEvidence_list_union.
  induction ls; simpl in *; intuition; subst; eauto.
  - erewrite manifest_env_union_map_one; eauto. 
  - erewrite manifest_env_union_map_one; 
    break_exists; eauto. 
Qed.
Global Hint Resolve mangen_plcTerm_list_exists : core.

Lemma mangen_plcEvidence_list_spec : forall ls et tp,
  In (et, tp) ls ->
  In (manifest_generator_app et tp) (manifest_generator_plcEvidence_list ls).
Proof.
  induction ls; simpl in *; intuition; subst; eauto;
  find_injection; eauto.
Qed.
Global Hint Resolve mangen_plcTerm_list_spec : core.

Lemma mangen_plcEvidence_list_subsumes : forall ls p m,
  map_get (mangen_plcEvidence_list_union ls) p = Some m ->
  (forall et tp,
    In (et,tp) ls ->
    (forall m', 
      map_get (manifest_generator_app et tp) p = Some m' ->
      manifest_subset m' m
    )
  ).
Proof.
  intuition; unfold mangen_plcEvidence_list_union in *.
  eapply (manifest_env_list_union_subsumes _ _ _ H
    (manifest_generator_app et tp) m'); eauto.
    + eapply mangen_plcEvidence_list_spec; eauto.
Qed.
Global Hint Resolve mangen_plcTerm_list_subsumes : core.


Lemma mangen_plcEvidence_subset_end_to_end_mangen : forall ls et tp,
  In (et, tp) ls ->
  (forall m m' p,
    map_get (mangen_plcEvidence_list_union ls) p = Some m' ->
    forall ts, map_get (end_to_end_mangen ls ts) p = Some m ->
    manifest_subset m' m
  ).
Proof.
  intuition; unfold end_to_end_mangen in *;
  eapply manifest_env_union_always_subset in H1; intuition.
Qed.
Global Hint Resolve mangen_plcTerm_subset_end_to_end_mangen : core.

Lemma mangen_subset_end_to_end_mangen_app : forall ls et tp,
  In (et, tp) ls ->
  (forall m m' p,
    map_get (manifest_generator_app et tp) p = Some m' ->
    forall ts, map_get (end_to_end_mangen ls ts) p = Some m ->
    manifest_subset m' m
  ).
Proof.
  intuition.
  assert (exists m'', map_get (mangen_plcEvidence_list_union ls) p = Some m''). eapply mangen_plcEvidence_list_exists; eauto.
  break_exists.
  pose proof (mangen_plcEvidence_list_subsumes ls p x H2 et tp H _ H0).
  pose proof (mangen_plcEvidence_subset_end_to_end_mangen ls et tp H m x p H2 ts H1).
  eapply manifest_subset_trans; eauto.
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
  (forall et tp,
      exists m', map_get (manifest_generator_app et tp) tp = Some m'
  ).
Proof.
  intuition.
  unfold manifest_generator_app.
  ff.
  assert (eqb tp tp = true).
  {
    rewrite eqb_eq_plc.
    auto.
  }
  ff.
  eauto.
Qed.
Global Hint Resolve mangen_exists_end_to_end_mangen_app : core.



Lemma mangen_app_tp_get : forall et tp x,
  map_get (manifest_generator_app et tp) tp = Some x ->
  manifest_generator_app'' et (myPlc_manifest_update tp empty_Manifest) = x.
Proof.
  intros.
  unfold manifest_generator_app in *.
  unfold manifest_generator_app' in *.
  unfold manifest_update_env in *.
  unfold e_empty in *.
  ff.
  assert (eqb tp tp = true).
  {
    rewrite eqb_eq_plc.
    trivial.
  }
  rewrite H0 in *.
  ff.
Qed.

Lemma end_to_end_mangen_supports_all_app : forall ts ls tp m,
  map_get (end_to_end_mangen ls ts) tp = Some m ->
  (forall et, 
    In (et, tp) ls ->
    (* In p (places tp t) -> *)
    ((* forall t',
      In t' (place_terms t tp p) -> *)
      manifest_support_term_app m et
    )
  ).
Proof.
  intuition.

  (*
  eapply man_gen_old_always_supports_app.
  *)

  (*
  Lemma mangen_subset_end_to_end_mangen_app : forall ls et tp,
  In (et, tp) ls ->
  (forall m m' p,
    map_get (manifest_generator_app et tp) p = Some m' ->
    forall ts, map_get (end_to_end_mangen ls ts) p = Some m ->
    manifest_subset m' m
  ).
  *)



  pose proof (mangen_exists_end_to_end_mangen_app et tp).
  break_exists.
  pose proof (mangen_subset_end_to_end_mangen_app _ _ _ H0 _ _ _ H1 _ H).
  pose proof manifest_supports_term_sub_app.
  eapply H3.
  eassumption.
  eapply man_gen_old_always_supports_app.



  eapply mangen_app_tp_get. eassumption.
Qed.
Global Hint Resolve end_to_end_mangen_supports_all : core.



Theorem manifest_generator_compiler_soundness_distributed_multiterm_app : forall et ts ls bs tp absMan amLib amConf,
  map_get (end_to_end_mangen ls ts) tp = Some absMan -> 
  In (et,tp) ls ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  et_size et = length bs ->
  forall st,

  supports_am_app amConf st.(amConfig)  ->

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
    * (* NOTE: This is the important one, substitute proof of any manifest here *)
      eapply end_to_end_mangen_supports_all_app; eauto.
  - find_rewrite; eauto.
  - ff.
  - eassumption.
Qed.

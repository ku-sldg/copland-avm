Require Import Manifest Manifest_Compiler Manifest_Generator AbstractedTypes
  Maps Term_Defs List Cvm_St Cvm_Impl ErrorStMonad_Coq StructTactics 
  Cvm_Monad EqClass Manifest_Admits Auto.
Require Import Manifest_Generator_Facts Executable_Defs_Prop 
  Executable_Facts_Dist Eqb_Evidence.

Require Import Coq.Program.Tactics.

Import ListNotations.

(* Set Nested Proofs Allowed. *)




Definition supports_am_app (ac1 ac2 : AM_Config) : Prop :=
  (forall aid l targ targid p' ev ev',
      (forall res, 
      ac1.(app_aspCb) (asp_paramsC aid l targ targid) p' ev ev' = resultC res ->
      ac2.(app_aspCb) (asp_paramsC aid l targ targid) p' ev ev' = resultC res)) /\
  (forall aid l targ targid p' ev ev',
      ac1.(app_aspCb) (asp_paramsC aid l targ targid) p' ev ev' = errC Runtime ->
      ac2.(app_aspCb) (asp_paramsC aid l targ targid) p' ev ev' = errC Runtime).

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

Definition lib_supports_manifest_app (al : AM_Library) (am : Manifest) : Prop :=
  (forall (a : (Plc*ASP_ID)), In a am.(appraisal_asps) -> exists cb, Maps.map_get al.(Local_Appraisal_ASPS) a = Some cb).

(*
Inductive Evidence: Set :=
| mt: Evidence
| nn: N_ID -> Evidence
| uu: Plc -> FWD -> ASP_PARAMS -> Evidence -> Evidence
| ss: Evidence -> Evidence -> Evidence.
*)

(*
  | lseq t1 t2 =>
      exists ac1 ac2,
      (am_config_support_exec t1 p ac1) /\
      (am_config_support_exec t2 p ac2) /\
      supports_am ac1 ac /\
      supports_am ac2 ac
*)



Fixpoint am_config_support_exec_app (e : Evidence) (ac : AM_Config) : Prop :=
    match e with
    | mt => True 
    | nn _ => True (* TODO: how to account for nonce handling? *)
    | uu p fwd ps e' => True 
            (*
            | ASPC _ _ (asp_paramsC aspid _ _ _) =>
            (forall l targ targid p' ev ev',
            ((exists res, 
            ac.(aspCb) (asp_paramsC aspid l targ targid) p' ev ev' = resultC res) \/ 
            ac.(aspCb) (asp_paramsC aspid l targ targid) p' ev ev' = errC Runtime))
            *)
    | ss e1 e2 => 
        exists ac1 ac2, 
        (am_config_support_exec_app e1 ac1) /\ 
        (am_config_support_exec_app e1 ac1) /\ 
        supports_am_app ac1 ac /\
        supports_am_app ac2 ac
    end.

Require Import AM_St Impl_appraisal.

Fixpoint nonce_ids_et (et:Evidence) : list N_ID.
Admitted.

Definition has_nonces (nids: list N_ID) (m:MapC N_ID BS) : Prop.
Admitted.


Theorem well_formed_am_config_impl_executable_app : forall et amConf ls,
  am_config_support_exec_app et amConf ->
  length ls = et_size et -> 
  forall st,
  supports_am_app amConf (st.(amConfig)) ->
  has_nonces (nonce_ids_et et) (st.(am_nonceMap)) -> 
    exists ec st',
        (gen_appraise_AM et ls) st = (resultC ec, st') \/ 
        (gen_appraise_AM et ls) st = (errC (dispatch_error Runtime), st'). 
Proof.
Admitted.

Require Import ManCompSoundness.

Definition manifest_support_am_config_app (m : Manifest) (ac : AM_Config) : Prop :=
  (forall p a, In (p,a) (m.(appraisal_asps)) -> 
    forall l targ targid ev ev',
    (exists res, ac.(app_aspCb) (asp_paramsC a l targ targid) p ev ev' = resultC res) \/
    (ac.(app_aspCb) (asp_paramsC a l targ targid) p ev ev' = errC Runtime)).

Theorem manifest_support_am_config_compiler_app : forall absMan amLib,
    lib_supports_manifest_app amLib absMan ->
    manifest_support_am_config_app absMan (manifest_compiler absMan amLib).
Proof.
  unfold lib_supports_manifest_app, manifest_support_am_config_app, 
    manifest_compiler, generate_PubKey_dispatcher, generate_Plc_dispatcher, generate_appraisal_ASP_dispatcher in *;
  simpl in *; intuition;
  repeat break_match; simpl in *; intuition; eauto;
  match goal with
  | H:  context[ map_get (minify_mapC ?l ?filt) ?a],
    H1: forall a' : (Plc*ASP_ID), _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
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
Qed.

Fixpoint manifest_support_term_app (m : Manifest) (e : Evidence) : Prop :=
    match e with
    | mt => True 
    | nn _ => True (* TODO: should we account for nonce presence here? *)
    | uu p fwd ps e' => 
        match ps with 
        | asp_paramsC a _ _ _ => 
            In (a,p) m.(appraisal_asps)
        end
        (* TODO:  support other fwd types here in the future... *)
    | ss e1 e2 => 
        manifest_support_term_app m e1 /\ 
        manifest_support_term_app m e2
    end.


Theorem manifest_support_am_config_impl_am_config_app: forall et absMan amConf,
    manifest_support_am_config_app absMan amConf ->
    manifest_support_term_app absMan et ->
    am_config_support_exec_app et amConf.
Proof.
    induction et; simpl in *; intuition; eauto;
    unfold manifest_support_am_config_app in *; intuition; eauto;
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
  -
    subst.
    unfold manifest_subset in H. 
    destruct_conjs.
    ff.  
  -
    split; 
    destruct_conjs; ff; eauto.
Qed.

Fixpoint manifest_generator_app' (et:Evidence) : Manifest. 
Admitted.

Theorem man_gen_old_always_supports_app : forall et absMan,
  (* map_get (manifest_generator' tp t backMan) p = Some absMan -> *)
  manifest_generator_app' et = absMan ->
  manifest_support_term_app absMan et.
Proof.
Admitted.

Theorem manifest_generator_compiler_soundness_app : forall et ls absMan amLib amConf,
  (* map_get (manifest_generator t tp) p = Some absMan -> *)
  manifest_generator_app' et = absMan ->
  lib_supports_manifest_app amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  length ls = et_size et ->
  forall st,

  st.(amConfig) = amConf ->

  has_nonces (nonce_ids_et et) (st.(am_nonceMap)) -> 

    ( 

    exists ec st',
         (gen_appraise_AM et ls) st = (resultC ec, st') \/ 
         (gen_appraise_AM et ls) st = (errC (dispatch_error Runtime), st')
    ).
Proof.
  intros.
  assert (supports_am_app amConf (st.(amConfig))) by ff.

  eapply well_formed_am_config_impl_executable_app.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config_app.
    * eapply manifest_support_am_config_compiler_app; eauto.


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

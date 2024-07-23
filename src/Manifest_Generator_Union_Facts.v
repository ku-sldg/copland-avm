Require Import Term_Defs_Core Params_Admits Manifest Eqb_Evidence
               Manifest_Generator_Helpers Term_Defs ErrorStMonad_Coq.

Require Import EqClass Maps StructTactics.

Require Import EnvironmentM Manifest_Set.

Require Import Manifest_Union Manifest_Generator Cvm_St Cvm_Impl.

Require Import Manifest ManCompSoundness Manifest_Compiler Manifest_Generator_Facts.

Require Import Manifest_Generator_Union ManCompSoundness_Appraisal.
Require Import AM_St Impl_appraisal.

Require Import Coq.Program.Tactics.
Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)

Theorem manifest_generator_compiler_soundness_distributed_list' : 
          forall t tp ets ts p absMan amLib amConf,
  In (t,tp) ts -> 
  map_get (end_to_end_mangen ets ts) p = Some absMan -> 
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->

  forall st,

    supports_am amConf (st.(st_config)) ->  

    (  forall t', 
         In t' (place_terms t tp p) -> 
        (exists st', 
        
        build_cvm (copland_compile t') st = (resultC tt, st')) \/
        
        (exists st' errStr,
        build_cvm (copland_compile t') st = (errC (dispatch_error (Runtime errStr)), st'))
    ).
Proof.
(* 
    ...
    eapply ManCompSoundness.manifest_generator_compiler_soundness_distributed
    ...
*)
Admitted.



Theorem manifest_generator_compiler_soundness_distributed_list : 
          forall t tp ets ts p absMan amLib amConf,
  In (t,tp) ts -> 
  map_get (end_to_end_mangen ets ts) p = Some absMan -> 
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  forall st,

  st.(st_config) = amConf ->

    (  forall t', 
         In t' (place_terms t tp p) -> 
        (exists st', 
        
        build_cvm (copland_compile t') st = (resultC tt, st')) \/
        
        (exists st' errStr,
        build_cvm (copland_compile t') st = (errC (dispatch_error (Runtime errStr)), st'))
    ).
Proof.
  intros.
  eapply manifest_generator_compiler_soundness_distributed_list'; eauto.
  find_rewrite.
  eapply supports_am_refl.
Qed.




Theorem manifest_generator_compiler_soundness_app_list' : 
      forall ets ts et tp ls absMan amLib amConf,
  In (et,tp) ets -> 
  map_get (end_to_end_mangen ets ts) tp = Some absMan -> 
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  et_size et = length ls ->

  forall st,

  supports_am amConf (st.(amConfig)) ->  

  has_nonces (nonce_ids_et et) (st.(am_nonceMap)) -> 

    ( 

    exists ec st',
         (gen_appraise_AM et ls) st = (resultC ec, st')) \/ 
    (exists st' errStr,
         (gen_appraise_AM et ls) st = (errC (am_dispatch_error (Runtime errStr)), st')
    ).
Proof.
(* 
    ...
    eapply ManCompSoundness_Appraisal.manifest_generator_compiler_soundness_app
    ...
*)
Admitted.



Theorem manifest_generator_compiler_soundness_app_list : forall ets ts et tp ls absMan amLib amConf,
  In (et,tp) ets -> 
  map_get (end_to_end_mangen ets ts) tp = Some absMan -> 
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
  eapply manifest_generator_compiler_soundness_app_list'; eauto.
  find_rewrite.
  eapply supports_am_refl.
Qed.
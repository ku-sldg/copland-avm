Require Import Manifest Manifest_Compiler Manifest_Generator 
  Maps Term_Defs List Cvm_St Cvm_Impl ErrorStMonad_Coq StructTactics Cvm_Monad EqClass Manifest_Admits.
Require Import Manifest_Generator_Facts Executable_Defs_Prop Executable_Facts_Dist.

Require Import Auto.
Import ListNotations.


(* map_get (minify_mapD Local_Plcs (fun _ : Plc => false)) p1 *)

Fixpoint knowsOf_asps (tp : Plc) (p : Plc) (t : Term) : list ASP_ID :=
  match t with
  | asp a =>
    if (eqb tp p)
    then 
      (match a with
      | ASPC _ _ par =>
          match par with
          | asp_paramsC i _ targp targid => [i]
          end
      | SIG => [sig_aspid]
      | HSH => [hsh_aspid]
      | ENC p => [enc_aspid]
      | _ => nil
      end)
    else nil
  | att p' t' => knowsOf_asps tp p' t'
  | lseq t1 t2 =>
      knowsOf_asps tp p t1 ++ knowsOf_asps tp p t2
  | bseq _ t1 t2 =>
      knowsOf_asps tp p t1 ++ knowsOf_asps tp p t2
  | bpar _ t1 t2 =>
      knowsOf_asps tp p t1 ++ knowsOf_asps tp p t2
  end.

Fixpoint knowsOf_uuid' (tp : Plc) (p:Plc) (t:Term)  : list Plc :=
  match t with
  | asp a => nil
  | att p' t' => 
      if (eqb tp p)
      then (* We are the top-level place, we need to know this *) 
        p' :: knowsOf_uuid' tp p' t'
      else knowsOf_uuid' tp p' t'
  | lseq t1 t2 =>
     knowsOf_uuid' tp p t1 ++ knowsOf_uuid' tp p t2
  | bseq _ t1 t2 =>
     knowsOf_uuid' tp p t1 ++ knowsOf_uuid' tp p t2
  | bpar _ t1 t2 =>
     knowsOf_uuid' tp p t1 ++ knowsOf_uuid' tp p t2
  end.

Fixpoint knowsOf_uuid'' (tp : Plc) (p:Plc) (t:Term)  : list Plc :=
  match t with
  | asp a => nil
  | att p' t' => 
      if (eqb tp p)
      then (* We are the top-level place, we need to know this *) 
        p' :: knowsOf_uuid'' p' p t'
      else knowsOf_uuid'' p' p t'
  | lseq t1 t2 =>
     knowsOf_uuid'' tp p t1 ++ knowsOf_uuid'' tp p t2
  | bseq _ t1 t2 =>
     knowsOf_uuid'' tp p t1 ++ knowsOf_uuid'' tp p t2
  | bpar _ t1 t2 =>
     knowsOf_uuid'' tp p t1 ++ knowsOf_uuid'' tp p t2
  end.

Fixpoint mentioned_places (t : Term) : list Plc :=
  match t with
  | asp a => nil
  | att p' t' => 
      p' :: mentioned_places t'
  | lseq t1 t2 =>
      mentioned_places t1 ++ mentioned_places t2
  | bseq _ t1 t2 =>
      mentioned_places t1 ++ mentioned_places t2
  | bpar _ t1 t2 =>
      mentioned_places t1 ++ mentioned_places t2
  end.

Fixpoint knowsOf_pubkey' (tp : Plc) (p : Plc) (t : Term) : list ASP_ID :=
  match t with
  | asp a =>
    match a with
    | ENC p => if (eqb tp p) then [p] else nil
    | _ => nil
    end
  | att p' t' => knowsOf_pubkey' tp p' t'
  | lseq t1 t2 =>
      knowsOf_pubkey' tp p t1 ++ knowsOf_pubkey' tp p t2
  | bseq _ t1 t2 =>
      knowsOf_pubkey' tp p t1 ++ knowsOf_pubkey' tp p t2
  | bpar _ t1 t2 =>
      knowsOf_pubkey' tp p t1 ++ knowsOf_pubkey' tp p t2
  end.

Fixpoint static_executable_manifest (t : Term) (m : Manifest) : Prop :=
  match t with
  | asp a => 
      match a with
      | ASPC _ _ par =>
          match par with
          | asp_paramsC i _ targp targid => 
              In i (asps m)
          end
      | SIG => In sig_aspid (asps m)
      | HSH => In hsh_aspid (asps m)
      | ENC p => In enc_aspid (asps m) /\ In p (pubKeyPlcs m)
      | NULL => True
      | CPY => True 
      end
  | att p' t => In p' (uuidPlcs m)
  | lseq t1 t2 => static_executable_manifest t1 m /\ static_executable_manifest t2 m
  | bseq _ t1 t2 => static_executable_manifest t1 m /\ static_executable_manifest t2 m
  | bpar _ t1 t2 => static_executable_manifest t1 m /\ static_executable_manifest t2 m
  end.

Ltac grind :=
  repeat (try break_match; simpl in *; intuition; subst; eauto; try congruence);
  repeat find_injection; subst;
  simpl in *; intuition; eauto.

Ltac breq l r :=
  let E := fresh "Heq" in
  destruct (eqb l r) eqn:E;
  try rewrite E in *;
  try (rewrite eqb_leibniz in *; subst; simpl in *; intuition; eauto; try congruence);
  try (rewrite eqb_refl in *; subst; simpl in *; intuition; eauto; try congruence);
  try (assert (l <> r) by (intros HC; rewrite <- eqb_leibniz in *; congruence)).

Ltac unf :=
  repeat (unfold asp_manifest_generator,
    at_manifest_generator, knowsof_manifest_update,
    asp_manifest_update, manifest_update_env,
    aspid_manifest_update, update_manifest_policy_targ,
    empty_Manifest in *
  ); simpl in *; try (intuition; eauto; congruence).
(* 

Theorem man_gen_only_available_if_known : forall t p backEnv envM p',
  map_get backEnv p' = None ->
  manifest_generator' p t backEnv = envM ->
  ((exists man, map_get envM p' = Some man) <-> In p' (knowsOf_uuid' p p' t)).
Proof.
  induction t; simpl in *; intuition; eauto; subst.
  - unfold asp_manifest_generator, manifest_update_env, 
      asp_manifest_update, aspid_manifest_update, update_manifest_policy_targ,
      pubkey_manifest_update in *; simpl in *; destruct H1.
    destruct a; simpl in *;
    break_match; subst;
    breq p p';
    erewrite mapC_get_distinct_keys_from_set in H; intuition; eauto; try congruence.
  - unfold asp_manifest_generator, manifest_update_env, 
      asp_manifest_update, aspid_manifest_update, update_manifest_policy_targ,
      pubkey_manifest_update in *; simpl in *.
    destruct a; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence;
    try rewrite mapC_get_works; eexists; eauto.
  - breq p0 p'.
    unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *;
    simpl in *.
    destruct (manifest_generator' p t
            (map_set backEnv p0
               (let
                '{|
                   my_abstract_plc := oldPlc;
                   asps := oldasps;
                   uuidPlcs := oldKnowsOf;
                   pubKeyPlcs := oldContext;
                   targetPlcs := oldTargets;
                   policy := oldPolicy
                 |} := match map_get backEnv p0 with
                       | Some mm => mm
                       | None => empty_Manifest
                       end in
                 {|
                   my_abstract_plc := oldPlc;
                   asps := oldasps;
                   uuidPlcs := p :: oldKnowsOf;
                   pubKeyPlcs := oldContext;
                   targetPlcs := oldTargets;
                   policy := oldPolicy
                 |}))) eqn:E;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail).
    repeat break_match; simpl in *; eauto;
    repeat break_match; simpl in *.
    * destruct H1; repeat find_injection; simpl in *.
      rewrite eqb_leibniz in *; subst.
      assert (map_get (map_set backEnv p0
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) p' = None). admit.
      pose proof (IHt _ _ _ _ H1 E).
      assert (exists man, map_get ((p',x) :: e) p' = Some man). admit.
      rewrite H2 in H3; intuition; eauto; subst.

Theorem man_gen_only_available_if_known : forall t p backEnv envM p',
  map_get backEnv p' = None ->
  manifest_generator' p t backEnv = envM ->
  ((exists man, map_get envM p' = Some man) <-> (In p' (knowsOf_uuid' p p' t) \/ p = p')).
Proof.
  induction t; simpl in *; intuition; eauto; subst.
  - unfold asp_manifest_generator, manifest_update_env, 
      asp_manifest_update, aspid_manifest_update, update_manifest_policy_targ,
      pubkey_manifest_update in *; simpl in *. destruct H1.
    destruct a; simpl in *;
    break_match; subst;
    breq p p';
    erewrite mapC_get_distinct_keys_from_set in H; intuition; eauto; try congruence.
  - unfold asp_manifest_generator, manifest_update_env, 
      asp_manifest_update, aspid_manifest_update, update_manifest_policy_targ,
      pubkey_manifest_update in *; simpl in *.
    destruct a; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence;
    try rewrite mapC_get_works; eexists; eauto.
  - breq p0 p'.
    unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *;
    simpl in *.
    destruct (manifest_generator' p t
            (map_set backEnv p0
               (let
                '{|
                   my_abstract_plc := oldPlc;
                   asps := oldasps;
                   uuidPlcs := oldKnowsOf;
                   pubKeyPlcs := oldContext;
                   targetPlcs := oldTargets;
                   policy := oldPolicy
                 |} := match map_get backEnv p0 with
                       | Some mm => mm
                       | None => empty_Manifest
                       end in
                 {|
                   my_abstract_plc := oldPlc;
                   asps := oldasps;
                   uuidPlcs := p :: oldKnowsOf;
                   pubKeyPlcs := oldContext;
                   targetPlcs := oldTargets;
                   policy := oldPolicy
                 |}))) eqn:E;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail).
    repeat break_match; simpl in *; eauto;
    repeat break_match; simpl in *.
    * destruct H1; repeat find_injection; simpl in *.
      rewrite eqb_leibniz in *; subst.
      assert (map_get (map_set backEnv p0
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) p' = None). admit.
      pose proof (IHt _ _ _ _ H1 E).
      assert (exists man, map_get ((p',x) :: e) p' = Some man). admit.
      rewrite H2 in H3; intuition; eauto; subst. *)

    

(* Theorem manifest_generator_impl_static_executable_manifest : forall t p backEnv envM,
  (forall p' man,
    map_get backEnv p' = Some man ->
    static_executable_manifest t man) ->
  manifest_generator' p t backEnv = envM ->
  (forall p' man,
    map_get envM p' = Some man ->
    static_executable_manifest t man
  ).
Proof.
  induction t; simpl in *; intuition; eauto.
  - destruct a; simpl in *; intuition; eauto.
    * destruct a; simpl in *; eauto.
      unfold asp_manifest_generator, manifest_update_env, 
        asp_manifest_update, aspid_manifest_update, 
        update_manifest_policy_targ in *; simpl in *;
      repeat break_match; simpl in *;
      repeat find_injection.
      ** eapply H in Heqo; simpl in *.
  
Qed. *)


(* Theorem manifest_generator_works : forall t p backEnv envM,
  manifest_generator' p t backEnv = envM ->
  forall p' absMan,
    map_get envM p' = Some absMan ->
    ((forall (a : ASP_ID), In a (knowsOf_asps p p' t) -> In a (asps absMan)) /\ 
     (forall (u : Plc), In u (knowsOf_uuid' p p' t) -> In u (uuidPlcs absMan)) /\
     (forall (u : Plc), In u (knowsOf_pubkey' p p' t) -> In u (pubKeyPlcs absMan))).
Proof.
  intros t p stEnv.
  pose proof (manifest_generator_executability_static' t p stEnv).
  generalizeEverythingElse t.
  induction t; simpl in *; intros.
  - destruct a; simpl in *;
    repeat break_match; simpl in *; intuition; eauto;
    subst.
    unfold canRunAsp_Env in *.


  simpl in *.

  induction t; simpl in *; intros.
  - repeat break_match; simpl in *; intuition; subst; eauto; 
    try congruence; unfold canRunAsp_Env in *; simpl in *; eauto;
    try break_if; try (rewrite eqb_leibniz in *; subst; eauto); admit.
  - eapply IHt in H as IH; simpl in *; intuition; eauto;
    break_if; eauto; clear IHt; rewrite <- H in H0. clear H.
    rewrite eqb_leibniz in *.
    rewrite Heqb in *; clear Heqb; eauto; simpl in *;
    intuition; rewrite H in *. clear H.
    unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update 
      in *; repeat break_match; subst; simpl in *; intuition; eauto;
    pose proof (man_gen_map_getter t u p'
             {|
               my_abstract_plc := my_abstract_plc;
               asps := asps;
               uuidPlcs := u :: uuidPlcs;
               pubKeyPlcs := pubKeyPlcs;
               targetPlcs := targetPlcs;
               policy := policy
             |} backEnv); destruct H; intuition; simpl in *; 
    find_rewrite; find_injection; eauto.
  - 
    destruct (manifest_generator' p t1 backEnv) eqn:E1;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
    destruct (map_get (manifest_generator' p t1 backEnv) p') eqn:E2.
    * rewrite E1 in E2;
      pose proof (IHt1 p backEnv (p0 :: e) E1 _ _ E2).
      pose proof (IHt2 p (p0 :: e) envM H _ _ H0);
      intuition; rewrite in_app_iff in *; intuition; eauto;
      clear IHt1 IHt2; admit.
    * 
    pose proof (man_gen_map_getter).
    intuition; rewrite in_app_iff in *; intuition.
    * destruct (manifest_generator' p t1 backEnv) eqn:E1;
      try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
      destruct p0; simpl in *.
      pose proof (IHt1 _ _ _ E1 p'); simpl in *;
      break_if; try (rewrite eqb_leibniz in *; subst; intuition; eauto).
      admit.
      pose proof (man_gen_doesnt_kill_info).
    pose proof (IHt1 _ _ _ E1). clear IHt1 E1.
    destruct p0.
    destruct (manifest_generator' p t2 ((p0, m) :: e)) eqn:E2;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail).
    pose proof (IHt2 _ _ _ E2); destruct p1; simpl in *. clear IHt2; simpl in *; subst.
    simpl in *.
    break_if; try (rewrite eqb_leibniz in *; subst; eauto; find_injection).
    * intuition; eauto; rewrite in_app_iff in *; intuition; eauto.
    simpl in *; intuition; eauto.
    * eapply IHt1 in E1 as E'.
    eapply IHt1 in E1.
    destruct H; eapply IHt1 in H; eapply IHt2 in H1; eauto;
    intuition; rewrite in_app_iff in *; intuition; eauto.
  - destruct H; eapply IHt1 in H; eapply IHt2 in H1; eauto;
    intuition; rewrite in_app_iff in *; intuition; eauto.
  - destruct H; eapply IHt1 in H; eapply IHt2 in H1; eauto;
    intuition; rewrite in_app_iff in *; intuition; eauto.
Qed. *)


Ltac cunf :=
  repeat (unfold asp_manifest_generator,
    asp_manifest_update,
    aspid_manifest_update,
    at_manifest_generator,
    manifest_update_env,
    knowsof_manifest_update,
    update_manifest_policy_targ,
    pubkey_manifest_update,
    map_set;
  simpl in *; eauto);
  repeat break_match;
  repeat find_injection;
  subst;
  repeat find_inversion;
  try congruence;
  simpl in *;
  eauto.
(* 
Lemma man_gen_map_getter : forall t u preEnv p st postEnv,
  map_get preEnv p = None ->
  exists st', 
    (map_get (manifest_generator' u t (preEnv ++ (p, st) :: postEnv)) p = Some st') /\
    (forall x, In x st.(uuidPlcs) -> In x st'.(uuidPlcs)) /\
    (forall x, In x st.(asps) -> In x st'.(asps)) /\
    (forall x, In x st.(pubKeyPlcs) -> In x st'.(pubKeyPlcs)).
Proof.

  induction t; simpl in *; intuition; eauto.
  - break_if.
    * rewrite eqb_leibniz in *; subst;
      break_match; try (edestruct @map_sandwich_not_none; eauto; fail);
      eapply map_app_unfolder in Heqo; subst; eauto;
      eexists; intuition; cunf.
    * destruct (map_has_buried preEnv p st postEnv);
      pose proof (map_app_unfolder preEnv p st postEnv _ H0 H); subst;
      eexists; intuition; cunf.
  - cunf.
    * pose proof (IHt p ((u,
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) :: preEnv) p0 ).
    cunf; eexists; intuition; eauto.
      break_match.
      admit.
      
      exfalso. eapply map_sandwich_not_none; eauto.
      admit.
      break_match; eexists; intuition; cunf; destruct a; 
      pose proof (map_app_unfolder preEnv u st postEnv _ Heqo H); subst. *)

(* Definition knowsOf_pubkey (p : Plc) (t : Term) : list ASP_ID :=
  p :: (knowsOf_pubkey' p t). *)
(* Lemma man_gen_doesnt_kill_info : forall t u p st absMan preEnv postEnv,
  map_get 
    (manifest_generator' u t
      (preEnv ++ (p, st) :: postEnv)) p = Some absMan ->
  map_get preEnv p = None ->
  forall x,
  In x (st.(uuidPlcs)) ->
  In x (absMan.(uuidPlcs)).
Proof.
  induction t; simpl in *; intuition; eauto.
  - break_if; unfold asp_manifest_update, aspid_manifest_update,
      update_manifest_policy_targ, pubkey_manifest_update in *; simpl in *;
    repeat break_match; repeat find_injection; simpl in *; eauto; try congruence;
    try (rewrite eqb_leibniz in *; subst; simpl in *; eauto);
    try (eapply map_app_unfolder in Heqo; subst; eauto; fail);
    try (eapply map_sandwich_not_none in Heqo; exfalso; eauto; fail).
    * eapply map_app_unfolder in H; subst; simpl in *; eauto.
  - unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update, map_set in *.
    break_match.
    destruct (eqb u p0) eqn:E.
    * rewrite eqb_leibniz in *; subst.
      pose proof (IHt p p0 {|
             my_abstract_plc := my_abstract_plc;
             asps := asps;
             uuidPlcs := p :: uuidPlcs;
             pubKeyPlcs := pubKeyPlcs;
             targetPlcs := targetPlcs;
             policy := policy
           |} absMan nil (preEnv ++ (p0, st) :: postEnv)); simpl in *.
      break_match; subst; simpl in *; intuition; eauto.
      ** eapply map_app_unfolder in Heqo; eauto; destruct st; find_injection; eauto.
      ** eapply map_sandwich_not_none in Heqo; exfalso; eauto.
    * pose proof (IHt p p0 st absMan ((u,
           {|
             my_abstract_plc := my_abstract_plc;
             asps := asps;
             uuidPlcs := p :: uuidPlcs;
             pubKeyPlcs := pubKeyPlcs;
             targetPlcs := targetPlcs;
             policy := policy
           |}) :: preEnv) postEnv). rewrite app_comm_cons in *;
           intuition; eapply H3; eauto.
      simpl in *. rewrite eqb_symm. rewrite E; eauto.
  - destruct (manifest_generator' u t1 (preEnv ++ (p, st) :: postEnv)) eqn:E;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
    destruct p0.
    destruct (map_get ((p0, m) :: e) p) eqn:E1.
    destruct (manifest_generator' u t2 (p0 :: e))

    eapply (IHt1 u p st absMan preEnv postEnv); eauto.
    destruct (manifest_generator' u t1 (preEnv ++ (p, st) :: postEnv)) eqn:E;
    


    (* * pose proof (IHt p p0 {|
             my_abstract_plc := my_abstract_plc;
             asps := asps;
             uuidPlcs := p :: uuidPlcs;
             pubKeyPlcs := pubKeyPlcs;
             targetPlcs := targetPlcs;
             policy := policy
           |} absMan nil (preEnv ++ (p0, st) :: postEnv)); simpl in *;
      eapply H2; eauto.
      break_match; subst; simpl in *; intuition; eauto.
      ** eapply map_app_unfolder in Heqo; eauto; destruct st; find_injection; eauto.
      ** eapply map_sandwich_not_none in Heqo; exfalso; eauto.
      intuition; eapply H2; intuition; eauto.
     rewrite app_comm_cons in *; eapply IHt in H; eauto.
    simpl in *.
    pose proof (IHt p p0 st absMan ((u,
           {|
             my_abstract_plc := my_abstract_plc;
             asps := asps;
             uuidPlcs := p :: uuidPlcs;
             pubKeyPlcs := pubKeyPlcs;
             targetPlcs := targetPlcs;
             policy := policy
           |}) :: preEnv ) ).
    rewrite <- H.
    pose proof (IHt p u {|
             my_abstract_plc := my_abstract_plc;
             asps := asps;
             uuidPlcs := p :: uuidPlcs;
             pubKeyPlcs := pubKeyPlcs;
             targetPlcs := targetPlcs;
             policy := policy
           |} absMan ((p0, st) :: backEnv)); intuition.
    eapply IHt in H.
    repeat find_injection; try find_contradiction. *)
Admitted. *)

(* Global Hint Resolve man_gen_doesnt_kill_info : core. *)

(* Theorem executable_impl_precond : forall t p backEnv envM,
  manifest_generator' p t backEnv = envM ->
  (forall p' absMan,
    map_get envM p' = Some absMan ->
    ((forall (a : ASP_ID), In a (knowsOf_asps p p' t) -> In a (asps absMan)) /\ 
     (forall (u : Plc), In u (knowsOf_uuid' p p' t) -> In u (uuidPlcs absMan)) /\
     (forall (u : Plc), In u (knowsOf_pubkey' p p' t) -> In u (pubKeyPlcs absMan)))
  ).
Proof.
  induction t; simpl in *; intros.
  - repeat break_match; simpl in *; intuition; subst; eauto; 
    try congruence; unfold canRunAsp_Env in *; simpl in *;
    break_if; try (rewrite eqb_leibniz in *; subst; eauto);
    admit.
  - eapply IHt in H as IH; simpl in *; intuition; eauto;
    break_if; eauto; clear IHt; rewrite <- H in H0. clear H.
    rewrite eqb_leibniz in *.
    rewrite Heqb in *; clear Heqb; eauto; simpl in *;
    intuition; rewrite H in *. clear H.
    unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update,
      map_set in *; repeat break_match; subst; simpl in *; intuition; eauto;
    eapply man_gen_doesnt_kill_info with (preEnv := nil); eauto; simpl in *; eauto.
  - intuition; rewrite in_app_iff in *; intuition.
    * destruct (manifest_generator' p t1 backEnv) eqn:E1;
      try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
      destruct p0; simpl in *.
      pose proof (IHt1 _ _ _ E1 p'); simpl in *;
      break_if; try (rewrite eqb_leibniz in *; subst; intuition; eauto).
      pose proof (man_gen_doesnt_kill_info).
    pose proof (IHt1 _ _ _ E1). clear IHt1 E1.
    destruct p0.
    destruct (manifest_generator' p t2 ((p0, m) :: e)) eqn:E2;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail).
    pose proof (IHt2 _ _ _ E2); destruct p1; simpl in *. clear IHt2; simpl in *; subst.
    simpl in *.
    break_if; try (rewrite eqb_leibniz in *; subst; eauto; find_injection).
    * intuition; eauto; rewrite in_app_iff in *; intuition; eauto.
    simpl in *; intuition; eauto.
    * eapply IHt1 in E1 as E'.
    eapply IHt1 in E1.
    destruct H; eapply IHt1 in H; eapply IHt2 in H1; eauto;
    intuition; rewrite in_app_iff in *; intuition; eauto.
  - destruct H; eapply IHt1 in H; eapply IHt2 in H1; eauto;
    intuition; rewrite in_app_iff in *; intuition; eauto.
  - destruct H; eapply IHt1 in H; eapply IHt2 in H1; eauto;
    intuition; rewrite in_app_iff in *; intuition; eauto.
Admitted. *)

Definition lib_supports_manifest (al : AM_Library) (am : Manifest) : Prop :=
  (forall (a : ASP_ID), In a am.(asps) -> exists cb, Maps.map_get al.(Local_ASPS) a = Some cb) /\
  (forall (up : Plc), In up am.(uuidPlcs) -> exists b, Maps.map_get al.(Local_Plcs) up = Some b) /\
  (forall (pkp : Plc), In pkp am.(pubKeyPlcs) -> exists b, Maps.map_get al.(Local_PubKeys) pkp = Some b).

Ltac unfolds :=
  (* repeat monad_unfold; *)
  repeat unfold manifest_generator, manifest_compiler, generate_ASP_dispatcher, 
    generate_Plc_dispatcher, generate_PubKey_dispatcher,
    generate_UUID_dispatcher, lib_supports_manifest, aspid_manifest_update,
    sig_params, hsh_params, enc_params in *;
  simpl in *; 
  repeat (match goal with
      | x : cvm_st |- _ => destruct x
      | x : AM_Config |- _ => destruct x
      | x : AM_Library |- _ => destruct x
      | x : CallBackErrors |- _ => destruct x
  end; simpl in *; eauto);
  intuition.

Theorem man_gen_aspid_in : forall a m,
  In a (asps (aspid_manifest_update a m)).
Proof.
  induction m; simpl in *; eauto.
Qed.



(* Lemma stupid_map_killer : forall a Local_ASPS st_pl st_ev p t m l d,
  (exists cb : CakeML_ASPCallback CallBackErrors, map_get Local_ASPS a = Some cb) ->
  (match
      map_get
        (minify_mapC Local_ASPS
            (fun x : ASP_ID =>
            if
              in_dec (EqClass_impl_DecEq ASP_ID) x (asps (aspid_manifest_update a (update_manifest_policy_targ p t m)))
            then true
            else false)) a
        with
        | Some cb =>
            match cb (asp_paramsC a l p t) st_pl (encodeEvRaw (get_bits st_ev)) (get_bits st_ev) with
            | errC c => match c with
                        | messageLift _ => errC Runtime
                        end
            | resultC r => resultC r
            end
        | None => errC Unavailable
        end = errC d) ->
  d = Runtime.
Proof.
  destruct d; eauto; intros; repeat break_match; 
  try congruence; clear H0.
  destruct H; pose proof man_gen_aspid_in; eauto.
  pose proof (H0 a). clear H0.
  assert (Some x = None). {
    rewrite <- H, <- Heqo.
    clear Heqo H st_pl st_ev x l.
    induction Local_ASPS; simpl in *; eauto.
    rewrite IHLocal_ASPS. clear IHLocal_ASPS.
    simpl in *.
    destruct a0, (eqb a a0) eqn:E; simpl in *; eauto;
    try (rewrite eqb_leibniz in E; subst; eauto).
    - destruct (in_dec (EqClass_impl_DecEq ASP_ID) a0 (asps (aspid_manifest_update a0 (update_manifest_policy_targ p t m)))); simpl in *; try rewrite eqb_refl in *; eauto; try (pose proof (H1 (update_manifest_policy_targ p t m))); try congruence.
    - destruct (in_dec (EqClass_impl_DecEq ASP_ID) a0 (asps (aspid_manifest_update a (update_manifest_policy_targ p t m)))); simpl in *; eauto; rewrite E; eauto.
  }
  congruence.
Qed.


Global Hint Resolve stupid_map_killer : core. *)
Global Hint Resolve man_gen_aspid_in : core.

(* 
Lemma generated_uuid_plcs_not_none : forall (l : MapD Plc UUID) (p : Plc) t p0 backEnv p' absMan,
  (map_get (manifest_generator' p t (at_manifest_generator p0 p backEnv)) p' = Some absMan) ->
  (forall up : Plc, In up (uuidPlcs absMan) -> exists b : UUID, map_get l up = Some b) ->
  (map_get (minify_mapD l 
    (fun x : Plc => if in_dec (EqClass_impl_DecEq Plc) x (uuidPlcs absMan) then true else false)) p = None) ->
  False.
Proof.
  induction l; simpl in *; intuition; eauto.
  - admit.
  - repeat (break_if; simpl in *; eauto; try congruence).
    * admit.
    * 
    * pose proof (IHl _ _ _ _ _ _ H).
      eapply IHl; eauto; intros.
      destruct (H0 _ H2); break_if; eauto; invc H3.
      rewrite eqb_leibniz in *; subst. *)

Theorem filter_resolver : forall {A B} `{EqClass A} (m : MapC A B) a (filt : A -> bool),
  (exists x, map_get m a = Some x) ->
  filt a = true ->
  exists x, map_get (minify_mapC m filt) a = Some x.
Proof.
  induction m; intuition; simpl in *;
  destruct (eqb a a0) eqn:E.
  - rewrite eqb_leibniz in E; subst. rewrite H1; simpl in *; rewrite eqb_refl; eauto.
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
  - rewrite eqb_leibniz in E; subst; destruct H1; simpl in *; 
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
  repeat break_if; eauto; try rewrite eqb_leibniz in Heqb1; 
  subst; eauto; congruence.
Qed.

Global Hint Resolve filter_resolver : core.

Require Import Helpers_CvmSemantics.

(* Lemma manifest_compiled_am_config_plcCb_only_unavailable : forall t st st' p, *)

(* Theorem man_gen_subterm : forall (t : Term) getPl backEnv p absMan,
  p <> getPl ->
  map_get backEnv getPl = None ->
  map_get (manifest_generator' p t backEnv) getPl = Some absMan ->
  In p (knowsOf_uuid' p getPl t).
Proof.
  induction t; intuition; try (simpl in *; eauto; fail).
  - unfold asp_manifest_generator, manifest_update_env, 
      asp_manifest_update, aspid_manifest_update, update_manifest_policy_targ in *;
    simpl in *.
    eapply (map_set_unfolder _ getPl p); [eauto | | eapply H1 ].
    erewrite map_get_none_iff_not_some; intros. 
    eapply (map_set_unfolder _ getPl); eauto.
  - admit.
  - simpl in *. rewrite in_app_iff.
    destruct (manifest_generator' p t1 backEnv) eqn:E1;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
    destruct (manifest_generator' p t2 (p0 :: e)) eqn:E2;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
    destruct (map_get (p0 :: e) getPl) eqn:E3.
    * left; eapply IHt1; eauto; find_rewrite; eauto.
    * right; eapply IHt2; eauto; find_rewrite; eauto.
  - simpl in *. rewrite in_app_iff.
    destruct (manifest_generator' p t1 backEnv) eqn:E1;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
    destruct (manifest_generator' p t2 (p0 :: e)) eqn:E2;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
    destruct (map_get (p0 :: e) getPl) eqn:E3.
    * left; eapply IHt1; eauto; find_rewrite; eauto.
    * right; eapply IHt2; eauto; find_rewrite; eauto.
  - simpl in *. rewrite in_app_iff.
    destruct (manifest_generator' p t1 backEnv) eqn:E1;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
    destruct (manifest_generator' p t2 (p0 :: e)) eqn:E2;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
    destruct (map_get (p0 :: e) getPl) eqn:E3.
    * left; eapply IHt1; eauto; find_rewrite; eauto.
    * right; eapply IHt2; eauto; find_rewrite; eauto.
Admitted. *)

Lemma callbacks_work_asps : forall absMan amLib amConf,
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  (forall x, In x absMan.(asps) -> 
    forall l p t p' ev ev' res,
      aspCb amConf (asp_paramsC x l p t) p' ev ev' = res ->
      res = errC Runtime \/ exists r, res = resultC r
  ).
Proof.
  induction absMan; simpl in *; intuition;
  destruct res; eauto; destruct d; eauto.
  destruct amConf; simpl in *;
  destruct amLib; simpl in *.
  unfold manifest_compiler in H0; repeat find_injection;
  simpl in *.
  repeat break_match; try congruence.
  unfold lib_supports_manifest in *; simpl in *;
  intuition.
  pose proof (H0 _ H1).
  assert ((fun x : ASP_ID =>
             if in_dec (EqClass_impl_DecEq ASP_ID) x asps
             then true
             else false) x = true).
  repeat break_match; eauto.
  pose proof (filter_resolver _ _ ((fun x : ASP_ID =>
             if in_dec (EqClass_impl_DecEq ASP_ID) x asps
             then true
             else false)) H3 H5).
  destruct H6. 
  assert (Some x0 = None). 
  rewrite <- H6. rewrite <- Heqo; eauto.
  congruence.
Qed.

Lemma add_to_list_works : forall {A} `{EqClass A} (l : list A) x,
  In x (add_to_list l x).
Proof.
  induction l; simpl in *; intuition; eauto;
  break_match; simpl in *; eauto.
  - rewrite eqb_leibniz in *; subst; eauto.
Qed.

Local Hint Resolve add_to_list_works : core.

Lemma never_change_am_conf : forall t st res st',
  build_cvm (copland_compile t) st = (res, st') ->
  st_AM_config st = st_AM_config st'.
Proof.
  induction t; simpl in *; 
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
  repeat (
    try (match goal with
    | H1 : build_cvm (copland_compile ?t1) _ = _ 
      |- _ =>
        try (eapply IHt1 in H1)
    | H2 : build_cvm (copland_compile ?t2) _ = _ 
      |- _ =>
        try (eapply IHt2 in H2)
    end); 
    try find_rewrite; eauto; 
    try find_injection;
    intuition; simpl in *; eauto
  );
  try (unfold remote_session, doRemote_session', do_remote in *;
    monad_unfold; simpl in *; ff; eauto; fail);
  try (
    try (eapply IHt1 in Heqp; simpl in *);
    try (eapply IHt1 in Heqp1; simpl in *);
    try (eapply IHt1 in Heqp0; simpl in *);
    try (eapply IHt2 in Heqp0; simpl in *);
    try (eapply IHt2 in Heqp1; simpl in *);
    find_rewrite; eauto).
  - destruct a; 
    repeat (try break_match; simpl in *; monad_unfold;
      try find_injection; eauto).
Qed.

Definition supports_am (ac1 ac2 : AM_Config) : Prop :=
  (forall aid l targ targid p' ev ev',
      (forall res, 
      ac1.(aspCb) (asp_paramsC aid l targ targid) p' ev ev' = resultC res ->
      ac2.(aspCb) (asp_paramsC aid l targ targid) p' ev ev' = resultC res)) /\
  (forall p, (forall res, 
      ac1.(pubKeyCb) p = resultC res ->
      ac2.(pubKeyCb) p = resultC res)) /\
  (forall p, (forall res, 
      ac1.(plcCb) p = resultC res ->
      ac2.(plcCb) p = resultC res)) /\
  (forall aid l targ targid p' ev ev',
      ac1.(aspCb) (asp_paramsC aid l targ targid) p' ev ev' = errC Runtime ->
      ac2.(aspCb) (asp_paramsC aid l targ targid) p' ev ev' = errC Runtime) /\
  (forall p, 
      ac1.(pubKeyCb) p = errC Runtime ->
      ac2.(pubKeyCb) p = errC Runtime) /\
  (forall p, 
      ac1.(plcCb) p = errC Runtime ->
      ac2.(plcCb) p = errC Runtime).

Fixpoint am_config_support_exec (t : Term) 
    (p : Plc) (ac : AM_Config) : Prop :=
  match t with
  | asp a =>
      match a with
      | NULL => True
      | CPY => True
      | SIG => 
          forall l targ targid p' ev ev',
          ((forall res, 
          ac.(aspCb) (asp_paramsC sig_aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC sig_aspid l targ targid) p' ev ev' = errC Runtime)
      | HSH =>
          forall l targ targid p' ev ev',
          ((forall res, 
          ac.(aspCb) (asp_paramsC hsh_aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC hsh_aspid l targ targid) p' ev ev' = errC Runtime)
      | ENC p =>
          (forall l targ targid p' ev ev',
          ((forall res, 
          ac.(aspCb) (asp_paramsC enc_aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC enc_aspid l targ targid) p' ev ev' = errC Runtime)) /\
          ((forall res, ac.(pubKeyCb) p = resultC res) \/ 
          ac.(pubKeyCb) p = errC Runtime)
      | ASPC _ _ (asp_paramsC aspid _ _ _) =>
          (forall l targ targid p' ev ev',
          ((forall res, 
          ac.(aspCb) (asp_paramsC aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC aspid l targ targid) p' ev ev' = errC Runtime)) 
      end
  | att p' t' =>
      ((forall res, ac.(plcCb) p' = resultC res) \/ 
      ac.(plcCb) p' = errC Runtime)
      (* /\ am_config_support_exec t' p' ac *)
  | lseq t1 t2 =>
      exists ac1 ac2,
      (am_config_support_exec t1 p ac1) /\
      (am_config_support_exec t2 p ac2) /\
      supports_am ac1 ac /\
      supports_am ac2 ac
  | bseq _ t1 t2 =>
      exists ac1 ac2,
      (am_config_support_exec t1 p ac1) /\
      (am_config_support_exec t2 p ac2) /\
      supports_am ac1 ac /\
      supports_am ac2 ac
  | bpar _ t1 t2 =>
      exists ac1 ac2,
      (am_config_support_exec t1 p ac1) /\
      (am_config_support_exec t2 p ac2) /\
      supports_am ac1 ac /\
      supports_am ac2 ac
  end.

Theorem well_formed_am_config_impl_executable : forall t p amConf,
  am_config_support_exec t p amConf ->
  forall st,
  supports_am amConf (st.(st_AM_config)) ->
  exists st', 
    build_cvm (copland_compile t) st = (resultC tt, st') \/
    build_cvm (copland_compile t) st = (errC (dispatch_error Runtime), st').
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
    unfold supports_am, sig_params, enc_params, hsh_params in *; intuition;
    try (match goal with
    | H1 : forall _, _,
      H2 : aspCb _ (asp_paramsC ?a ?l ?targ ?tid) ?p' ?ev ?ev' = _,
      H3 : context[ aspCb _ _ _ _ _ = errC Runtime -> _],
      H4 : context[ aspCb _ _ _ _ _ = resultC _ -> _]
      |- _ =>
        let H := fresh "H" in
        let H' := fresh "Hx" in
        destruct (H1 l targ tid p' ev ev') as [H | H]; 
        [
          (* result side *)
          pose proof (H4 a l targ tid p' ev ev') as H';
          erewrite H' in *; try congruence
          |
          (* err side *)
          pose proof (H3 a l targ tid p' ev ev') as H';
          intuition; find_rewrite; find_injection; eauto
        ]
        (* ;
        intuition; find_rewrite; try congruence;
        find_injection; eauto *)
    end).
  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      unfold remote_session, doRemote_session', do_remote in *;
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    unfold supports_am in *; intuition;
    erewrite H2 in *; try congruence.
  - subst; simpl in *; try rewrite eqb_refl in *;
    repeat (
      unfold remote_session, doRemote_session', do_remote in *;
      try break_match;
      try monad_unfold;
      try break_match
      try find_injection;
      try find_contradiction;
      try find_injection;
      (* repeat find_rewrite; *)
      simpl in *; subst; intuition; 
      eauto; try congruence);
    unfold supports_am in *; intuition;
    erewrite H6 in *; try congruence;
    find_injection; eauto.
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
      eauto; try congruence).
    * destruct H as [ac1 [ac2 H]]; intuition.
      pose proof (IHt1 _ _ H0).
      destruct (IHt1 _ _ H0).
      destruct (IHt2 _ _ H st eq_refl); 
      intuition; eauto;
      repeat find_rewrite;
      repeat find_injection; eauto.
    * destruct (IHt1 _ _ H0 st eq_refl);
      destruct H; find_rewrite; find_injection; eauto;
      assert (st_AM_config x = st_AM_config st) by
          (symmetry;
          eapply never_change_am_conf; eauto);
          destruct (IHt2 _ _ H1 x H); intuition; eauto;
         find_rewrite; find_injection; eauto.
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
      | H1 : am_config_support_exec t1 _ ?amConf,
        H2 : build_cvm (copland_compile t1) ?st = _
        |- _ =>
          pose proof (eq_sym (never_change_am_conf _ _ _ _ H2));
          simpl in *;
          pose proof (IHt1 _ _ H1 st); 
          repeat (
            try break_exists;
            intuition);
          try find_rewrite;
          try find_injection; eauto; try congruence
      end;
      match goal with
      | H1 : am_config_support_exec t2 _ ?amConf,
        H2 : build_cvm (copland_compile t2) ?st = _
        |- _ =>
          pose proof (eq_sym (never_change_am_conf _ _ _ _ H2));
          simpl in *;
          pose proof (IHt2 _ _ H1 st); 
          repeat (
            try break_exists;
            intuition);
          try find_rewrite;
          try find_injection; eauto; try congruence
      end; simpl in *.
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
      | H1 : am_config_support_exec t1 _ ?amConf,
        H2 : build_cvm (copland_compile t1) ?st = _
        |- _ =>
          pose proof (eq_sym (never_change_am_conf _ _ _ _ H2));
          simpl in *;
          pose proof (IHt1 _ _ H1 st); 
          repeat (
            try break_exists;
            intuition);
          try find_rewrite;
          try find_injection; eauto; try congruence
      end;
      match goal with
      | H1 : am_config_support_exec t2 _ ?amConf,
        H2 : build_cvm (copland_compile t2) ?st = _
        |- _ =>
          pose proof (eq_sym (never_change_am_conf _ _ _ _ H2));
          simpl in *;
          pose proof (IHt2 _ _ H1 st); 
          repeat (
            try break_exists;
            intuition);
          try find_rewrite;
          try find_injection; eauto; try congruence
      end; simpl in *.
Qed.

Lemma in_add_to_list : forall {A} `{EqClass A} (l : list A) x x',
  In x l ->
  In x (add_to_list l x').
Proof.
  induction l; simpl in *; intuition; eauto;
  subst; eauto.
  - break_match; simpl in *; eauto.
  - break_match; simpl in *; eauto.
Qed.

Local Hint Resolve in_add_to_list : core.

(* Theorem gen_man_preserves : forall (t : Term) (p : Plc) 
  (my_abstract_plc : Plc) asps uuidPlcs' pubKeyPlcs targetPlcs policy,
  (* In p (uuidPlcs (st)) -> *)
  In p (uuidPlcs
     (generate_manifest' t p
        {|
          my_abstract_plc := my_abstract_plc;
          asps := asps;
          uuidPlcs := add_to_list (uuidPlcs') p;
          pubKeyPlcs := pubKeyPlcs;
          targetPlcs := targetPlcs ;
          policy := policy 
        |})) .
        (* <->
  In p (add_to_list (uuidPlcs
     (generate_manifest' t p
        {|
          my_abstract_plc := my_abstract_plc ;
          asps := asps ;
          uuidPlcs := uuidPlcs' ;
          pubKeyPlcs := pubKeyPlcs ;
          targetPlcs := targetPlcs ;
          policy := policy 
        |})) p). *)
Proof.
  induction t.
  (* induction t; simpl in *; intuition; eauto.
  - destruct a; ff.
  - destruct (in_dec (EqClass_impl_DecEq _) p0 (uuidPlcs
            (generate_manifest' t p
               {|
                 my_abstract_plc := my_abstract_plc;
                 asps := asps;
                 uuidPlcs := add_to_list uuidPlcs' p;
                 pubKeyPlcs := pubKeyPlcs;
                 targetPlcs := targetPlcs;
                 policy := policy
               |}))).
    *  *)
Admitted. *)

(* Local Hint Resolve gen_man_preserves : core. *)

Theorem generate_manifest'_preserves_plc : forall t p st st',
  generate_manifest' t p st = st' ->
  st.(my_abstract_plc) = st'.(my_abstract_plc).
Proof.
  induction t; simpl in *; intuition; eauto;
  repeat break_match; subst; eauto;
  try (destruct (generate_manifest' t1 p st) eqn:E1;
    eapply IHt1 in E1; simpl in *;
    destruct (generate_manifest' t2 p {|
       my_abstract_plc := my_abstract_plc;
       asps := asps;
       uuidPlcs := uuidPlcs;
       pubKeyPlcs := pubKeyPlcs;
       targetPlcs := targetPlcs;
       policy := policy
     |}) eqn:E2;
    eapply IHt2 in E2; simpl in *; subst; eauto).
Qed.

Theorem generate_manifest'_preserves_asps : forall t p st x st',
  p = my_abstract_plc st ->
  In x (asps st) ->
  generate_manifest' t p st = st' ->
  In x (asps st').
Proof.
  induction t; simpl in *; intuition; eauto;
  subst; try rewrite eqb_refl in *; simpl in *;
    repeat break_match; simpl in *;
    try find_injection; eauto.
  - destruct (generate_manifest' t1 (my_abstract_plc st) st) eqn:E1;
    simpl in *.
    eapply IHt1 in E1 as H'; eauto.
    destruct (generate_manifest' t2 (Manifest.my_abstract_plc st) {|
          my_abstract_plc := my_abstract_plc;
          asps := asps;
          uuidPlcs := uuidPlcs;
          pubKeyPlcs := pubKeyPlcs;
          targetPlcs := targetPlcs;
          policy := policy
        |}) eqn:E2; simpl in *; eauto.
    eapply IHt2 in E2; eauto.
    simpl in *.
    eapply generate_manifest'_preserves_plc in E1;
    eapply generate_manifest'_preserves_plc in E2;
    simpl in *; subst; eauto.
  - destruct (generate_manifest' t1 (my_abstract_plc st) st) eqn:E1;
    simpl in *.
    eapply IHt1 in E1 as H'; eauto.
    destruct (generate_manifest' t2 (Manifest.my_abstract_plc st) {|
          my_abstract_plc := my_abstract_plc;
          asps := asps;
          uuidPlcs := uuidPlcs;
          pubKeyPlcs := pubKeyPlcs;
          targetPlcs := targetPlcs;
          policy := policy
        |}) eqn:E2; simpl in *; eauto.
    eapply IHt2 in E2; eauto.
    simpl in *.
    eapply generate_manifest'_preserves_plc in E1;
    eapply generate_manifest'_preserves_plc in E2;
    simpl in *; subst; eauto.
  - destruct (generate_manifest' t1 (my_abstract_plc st) st) eqn:E1;
    simpl in *.
    eapply IHt1 in E1 as H'; eauto.
    destruct (generate_manifest' t2 (Manifest.my_abstract_plc st) {|
          my_abstract_plc := my_abstract_plc;
          asps := asps;
          uuidPlcs := uuidPlcs;
          pubKeyPlcs := pubKeyPlcs;
          targetPlcs := targetPlcs;
          policy := policy
        |}) eqn:E2; simpl in *; eauto.
    eapply IHt2 in E2; eauto.
    simpl in *.
    eapply generate_manifest'_preserves_plc in E1;
    eapply generate_manifest'_preserves_plc in E2;
    simpl in *; subst; eauto.
Qed.

Theorem lib_supports_cumul : 
  forall t p st,
  forall amLib absMan,
  lib_supports_manifest amLib absMan ->
  generate_manifest' t p st = absMan ->
  lib_supports_manifest amLib st.
Proof.
  induction t; simpl in *; intuition; eauto;
  try (repeat break_match; subst; eauto;
  unfold lib_supports_manifest in *; intuition;
  simpl in *; eauto; fail).
Qed.

Theorem man_gen_comp_works : forall t p backMan absMan amLib,
  lib_supports_manifest amLib backMan ->
  p = backMan.(my_abstract_plc) ->
  generate_manifest' t p backMan = absMan ->
  (* forall amLib, *)
  lib_supports_manifest amLib absMan ->
  (forall amConf,
    manifest_compiler absMan amLib = amConf ->
    am_config_support_exec t p amConf
  ).
Proof.
  induction t; simpl in *; intros.
  - rewrite H0 in *;
    rewrite eqb_refl in *;
    unfold lib_supports_manifest, manifest_compiler in *;
    destruct amConf; find_injection; simpl in *;
    repeat (
      try unfold generate_PubKey_dispatcher in *;
      repeat break_match; repeat find_injection;
      simpl in *; intuition; eauto; try congruence
    );
    try (match goal with
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
    end).
  - unfold lib_supports_manifest, manifest_compiler in *;
    destruct amConf; find_injection; simpl in *;
    repeat (
      try unfold generate_Plc_dispatcher in *;
      repeat break_match; repeat find_injection;
      simpl in *; intuition; eauto; try congruence
    );
    try (match goal with
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
    end).
  - destruct (generate_manifest' t1 p backMan) eqn:E1.
    assert (lib_supports_manifest amLib
      {|
        my_abstract_plc := my_abstract_plc;
        asps := asps;
        uuidPlcs := uuidPlcs;
        pubKeyPlcs := pubKeyPlcs;
        targetPlcs := targetPlcs;
        policy := policy
      |}). {
        eapply lib_supports_cumul; eauto.
    }
    pose proof (IHt1 _ _ _ _ H H0 E1 H4).
    
    eapply lib_supports_cumul with (amLib := amLib) in E1 as HL1.
    pose proof (IHt1 _ _ _ H E1 amLib).
    eapply 

    (* pose proof (IHt1 _ _ _ H E1 amLib). *)
    assert (lib_supports_manifest amLib
       {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |}). {
       unfold lib_supports_manifest in *; simpl in *;
       intuition; eauto.
       - 
        eapply H3.
         pose proof (generate_manifest'_preserves_asps 
          t1 p backMan a ({|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            uuidPlcs := uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |})
         ). intuition.
          
    }


    pose proof (IHt2 _ _ _ H H0).
    repeat break_match; repeat find_injection;
    simpl in *; intuition; eauto; try congruence.
    * rewrite <- H0 in *; simpl in *;
      unfold lib_supports_manifest, manifest_compiler in *.
      destruct amConf; find_injection; simpl in *.


  induction t; simpl in *; intuition; subst; eauto;
  repeat rewrite eqb_refl in *.
  - unfold generate_PubKey_dispatcher;
    destruct a; intuition; simpl in *;
    try (try (destruct a); 
    simpl in *; intuition;
    repeat break_match; simpl in *; eauto;
    unfold lib_supports_manifest in *; simpl in *; intuition;
    (* pose proof (filter_resolver (Local_ASPS amLib)). *)
    try (match goal with
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
    end); fail).
    * unfold generate_PubKey_dispatcher, lib_supports_manifest in *; 
      simpl in *; intuition;
      repeat break_match; simpl in *; eauto;
      match goal with
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
  - repeat (
      unfold lib_supports_manifest, generate_Plc_dispatcher in *; simpl in *; intuition; eauto; try congruence).
    repeat break_match; simpl in *; eauto.
    match goal with
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
    end; eauto;
    pose proof (H1 _ (gen_man_preserves _ _ _ _ _ _ _ _));
    try (exfalso; eauto; fail); eauto.
    
  - pose proof (IHt (my_abstract_plc backMan) backMan).
    repeat (
      unfold lib_supports_manifest, generate_Plc_dispatcher in *; simpl in *; intuition; eauto; try congruence);
    repeat break_match; simpl in *; eauto.
    clear IHt.
    unfold am_config_support_exec; simpl in *.
    destruct ((generate_manifest' t p
          {|
            my_abstract_plc := my_abstract_plc backMan;
            asps := asps backMan;
            uuidPlcs := add_to_list (uuidPlcs backMan) p;
            pubKeyPlcs := pubKeyPlcs backMan;
            targetPlcs := targetPlcs backMan;
            policy := policy backMan
          |})) eqn:E; eauto.
    assert (p = Manifest.my_abstract_plc backMan). admit.
    destruct ((manifest_compiler
     {|
       my_abstract_plc := my_abstract_plc;
       asps := asps;
       uuidPlcs := uuidPlcs;
       pubKeyPlcs := pubKeyPlcs;
       targetPlcs := targetPlcs;
       policy := policy
     |} amLib)) eqn:E1.
    pose proof (IHt p {|
        my_abstract_plc := Manifest.my_abstract_plc backMan;
        asps := Manifest.asps backMan;
        uuidPlcs := add_to_list (Manifest.uuidPlcs backMan) p;
        pubKeyPlcs := Manifest.pubKeyPlcs backMan;
        targetPlcs := Manifest.targetPlcs backMan;
        policy := Manifest.policy backMan
      |} _ H E _ H1 _ E1). eauto.
    repeat (
      unfold lib_supports_manifest, generate_Plc_dispatcher in *; simpl in *; intuition; eauto; try congruence).
    repeat break_match; simpl in *; eauto.
    match goal with
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
    end; eauto;
    pose proof (H1 _ (gen_man_preserves _ _ _ _ _ _ _ _));
    try (exfalso; eauto; fail); eauto.

    
    

      eapply H1; eauto.
    try (destruct a); 
    simpl in *; intuition;
    repeat break_match; simpl in *; eauto;
    unfold lib_supports_manifest in *; simpl in *; intuition;
    (* pose proof (filter_resolver (Local_ASPS amLib)). *)
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
    end.
    * simpl in *; intuition;
      repeat break_match; simpl in *; eauto;
      unfold lib_supports_manifest in *; simpl in *; intuition;
      (* pose proof (filter_resolver (Local_ASPS amLib)). *)
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
      end.
      eapply filter_resolver.  eapply H; eauto.


   manifest_generator' p t backEnv = envM ->
  (forall p' absMan, 
    map_get backEnv p' = None ->
    map_get envM p' = Some absMan ->
    (forall amLib amConf, 
      lib_supports_manifest amLib absMan ->
      manifest_compiler absMan amLib = amConf ->
      
    )
  ).
.
Proof.
  
Qed.

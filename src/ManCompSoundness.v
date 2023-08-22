Require Import Manifest Manifest_Compiler Manifest_Generator AbstractedTypes
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

Theorem supports_am_refl : forall ac1,
  supports_am ac1 ac1.
Proof.
  unfold supports_am; intuition.
Qed.

Theorem supports_am_trans : forall ac1 ac2 ac3,
  supports_am ac1 ac2 ->
  supports_am ac2 ac3 ->
  supports_am ac1 ac3.
Proof.
  unfold supports_am; intuition.
Qed.

Local Hint Resolve never_change_am_conf : core.
Local Hint Resolve supports_am_refl : core.
Local Hint Resolve supports_am_trans : core.

Fixpoint am_config_support_exec (t : Term) 
    (p : Plc) (ac : AM_Config) : Prop :=
  match t with
  | asp a =>
      match a with
      | NULL => True
      | CPY => True
      | SIG => 
          forall l targ targid p' ev ev',
          ((exists res, 
          ac.(aspCb) (asp_paramsC sig_aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC sig_aspid l targ targid) p' ev ev' = errC Runtime)
      | HSH =>
          forall l targ targid p' ev ev',
          ((exists res, 
          ac.(aspCb) (asp_paramsC hsh_aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC hsh_aspid l targ targid) p' ev ev' = errC Runtime)
      | ENC p =>
          (forall l targ targid p' ev ev',
          ((exists res, 
          ac.(aspCb) (asp_paramsC enc_aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC enc_aspid l targ targid) p' ev ev' = errC Runtime)) /\
          ((exists res, ac.(pubKeyCb) p = resultC res) \/ 
          ac.(pubKeyCb) p = errC Runtime)
      | ASPC _ _ (asp_paramsC aspid _ _ _) =>
          (forall l targ targid p' ev ev',
          ((exists res, 
          ac.(aspCb) (asp_paramsC aspid l targ targid) p' ev ev' = resultC res) \/ 
          ac.(aspCb) (asp_paramsC aspid l targ targid) p' ev ev' = errC Runtime)) 
      end
  | att p' t' =>
      ((exists res, ac.(plcCb) p' = resultC res) \/ 
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
    match goal with
    | H1 : forall _, _,
      H2 : aspCb _ (asp_paramsC ?a ?l ?targ ?tid) ?p' ?ev ?ev' = _,
      H3 : context[ aspCb _ _ _ _ _ = errC Runtime -> _],
      H4 : context[ aspCb _ _ _ _ _ = resultC _ -> _]
      |- _ =>
        let H := fresh "H" in
        let H' := fresh "Hx" in
        let H'' := fresh "Hx" in
        let res := fresh "res" in
        destruct (H1 l targ tid p' ev ev') as [H | H]
        ; 
        [
          (* result side *)
          destruct H as [res H''];
          pose proof (H4 a l targ tid p' ev ev') as H';
          erewrite H' in *; eauto; congruence
          |
          (* err side *)
          pose proof (H3 a l targ tid p' ev ev') as H';
          intuition; find_rewrite; find_injection; eauto
        ]
    end.
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
    unfold supports_am in *; intuition.
    destruct H0;
    erewrite H2 in *; try congruence; eauto.
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
      eauto; try congruence);
      match goal with
      | H1 : exists _ _ : AM_Config, _
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
              assert (A : supports_am ac1 (st_AM_config st)); [ 
                simpl in *; eauto
                |
                destruct (IHt1 p ac1 AS1 st A);
                intuition; repeat find_rewrite;
                repeat find_injection;
                try congruence; eauto
              ]
          end;
          match goal with
          | H3 : build_cvm (copland_compile t2) ?st = _
            |- _ =>
              let A := fresh "A" in
              assert (A : supports_am ac2 (st_AM_config st)); [ 
                repeat find_eapply_lem_hyp never_change_am_conf;
                repeat find_rewrite;
                simpl in *; eauto
                |
                destruct (IHt2 p ac2 AS2 st A);
                intuition; repeat find_rewrite;
                repeat find_injection;
                try congruence; eauto
              ]
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
    | H1 : exists _ _ : AM_Config, _
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
            assert (A : supports_am ac1 (st_AM_config st)); [ 
              simpl in *; eauto
              |
              destruct (IHt1 p ac1 AS1 st A);
              intuition; repeat find_rewrite;
              repeat find_injection;
              try congruence; eauto
            ]
        end;
        match goal with
        | H3 : build_cvm (copland_compile t2) ?st = _
          |- _ =>
            let A := fresh "A" in
            assert (A : supports_am ac2 (st_AM_config st)); [ 
              repeat find_eapply_lem_hyp never_change_am_conf;
              repeat find_rewrite;
              simpl in *; eauto
              |
              destruct (IHt2 p ac2 AS2 st A);
              intuition; repeat find_rewrite;
              repeat find_injection;
              try congruence; eauto
            ]
        end;
        repeat find_rewrite; eauto
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
    | H1 : exists _ _ : AM_Config, _
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
            assert (A : supports_am ac1 (st_AM_config st)); [ 
              simpl in *; eauto
              |
              destruct (IHt1 p ac1 AS1 st A);
              intuition; repeat find_rewrite;
              repeat find_injection;
              try congruence; eauto
            ]
        end;
        match goal with
        | H3 : build_cvm (copland_compile t2) ?st = _
          |- _ =>
            let A := fresh "A" in
            assert (A : supports_am ac2 (st_AM_config st)); [ 
              repeat find_eapply_lem_hyp never_change_am_conf;
              repeat find_rewrite;
              simpl in *; eauto
              |
              destruct (IHt2 p ac2 AS2 st A);
              intuition; repeat find_rewrite;
              repeat find_injection;
              try congruence; eauto
            ]
        end;
        repeat find_rewrite; eauto
    end.
  (* Unshelve. (* Weirdly, we have trivial existentials left *)
  all: try (eapply default_bs); try (eapply default_UUID). *)
Qed.

Lemma in_add_to_list : forall {A} `{EqClass A} (l : list A) x x',
  In x l ->
  In x (add_to_list l x').
Proof.
  induction l; simpl in *; intuition; eauto;
  subst; eauto; break_match; simpl in *; eauto.
Qed.

Local Hint Resolve in_add_to_list : core.

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

Theorem generate_manifest'_preserves_pubKeyPlcs : forall t p st x st',
  p = my_abstract_plc st ->
  In x (pubKeyPlcs st) ->
  generate_manifest' t p st = st' ->
  In x (pubKeyPlcs st').
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


Theorem generate_manifest'_preserves_uuidPlcs : forall t p st x st',
  p = my_abstract_plc st ->
  In x (uuidPlcs st) ->
  generate_manifest' t p st = st' ->
  In x (uuidPlcs st').
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

Local Hint Resolve generate_manifest'_preserves_asps : core.
Local Hint Resolve generate_manifest'_preserves_plc : core.
Local Hint Resolve generate_manifest'_preserves_pubKeyPlcs : core. 
Local Hint Resolve generate_manifest'_preserves_uuidPlcs : core.

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

Lemma in_add_to_list_rev : forall {A} `{EqClass A} (l : list A) (a a' : A),
  a <> a' ->
  In a (add_to_list l a') ->
  In a l.
Proof.
  induction l; simpl in *; intuition; eauto.
  break_match; simpl in *; intuition; eauto.
Qed.

Lemma in_dec_add_to_list : forall {A} `{EqClass A} l a a',
  a <> a' ->
  (if (in_dec (EqClass_impl_DecEq A) a l) then true else false) =  
  if (in_dec (EqClass_impl_DecEq A) a (add_to_list l a')) then true else false.
Proof.
  intuition; repeat break_match; eauto.
  - destruct n; eapply in_add_to_list; eauto.
  - destruct n; eapply in_add_to_list_rev; eauto.
Qed.

Lemma cannot_be_in_filter_map : forall {A B} `{EqClass A} (l : MapC A B) l' a,
  ~ (In a l') ->
  map_get (minify_mapC l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x l' then true else false)) a = None.
Proof.
  induction l; simpl in *; intuition; eauto;
  repeat (break_match; simpl in *; eauto; try congruence);
  rewrite eqb_leibniz in *; congruence.
Qed.

Lemma cannot_be_in_filter_mapd : forall {A B} `{EqClass A, EqClass B} (l : MapD A B) l' a,
  ~ (In a l') ->
  map_get (minify_mapD l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x l' then true else false)) a = None.
Proof.
  induction l; simpl in *; intuition; eauto;
  repeat (break_match; simpl in *; eauto; try congruence);
  rewrite eqb_leibniz in *; congruence.
Qed.

Lemma map_get_minify_eq_under_add_to_list : forall {A B} `{EqClass A} (l : MapC A B) l' a a' v,
  map_get (minify_mapC l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x l' then true else false)) a = Some v ->
  map_get (minify_mapC l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x (add_to_list l' a') then true else false)) a = Some v.
Proof.
  induction l; simpl in *; intuition; eauto;
  repeat (break_match; simpl in *; auto with *; eauto; try congruence);
  rewrite eqb_leibniz in *; subst.
  - assert (Some v = None). {
      rewrite <- H0; eapply cannot_be_in_filter_map; eauto.
    }
    congruence.
Qed.


Lemma mapD_get_minify_eq_under_add_to_list : forall {A B} `{EqClass A, EqClass B} (l : MapD A B) l' a a' v,
  map_get (minify_mapD l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x l' then true else false)) a = Some v ->
  map_get (minify_mapD l 
    (fun x : A => if in_dec (EqClass_impl_DecEq A) x (add_to_list l' a') then true else false)) a = Some v.
Proof.
  induction l; simpl in *; intuition; eauto;
  repeat (break_match; simpl in *; auto with *; eauto; try congruence);
  rewrite eqb_leibniz in *; subst.
  - assert (Some v = None). {
      rewrite <- H1; eapply cannot_be_in_filter_mapd; eauto.
    }
    congruence.
Qed.

Lemma man_comp_cumul : forall t p absMan amLib amConf absMan' amConf',
  manifest_compiler absMan amLib = amConf ->
  generate_manifest' t p absMan = absMan' ->
  manifest_compiler absMan' amLib = amConf' ->
  supports_am amConf amConf'.
Proof.
  induction t; try (simpl in *; intuition; eauto; fail).
  - simpl in *; intuition; eauto;
    destruct a; repeat break_match; simpl in *; subst; eauto;
    rewrite eqb_leibniz in *; subst; eauto;
    unfold supports_am in *; simpl in *; intuition; eauto;
    unfold generate_PubKey_dispatcher in *; simpl in *; intuition; eauto;
    repeat break_match; simpl in *; intuition; eauto; try congruence;
    repeat find_injection; repeat find_rewrite; eauto; try congruence;
    try (
      try match goal with
      | H1 : map_get (minify_mapC ?l 
          (fun x : ASP_ID => 
            if in_dec (EqClass_impl_DecEq ASP_ID) x ?l' then true else false)) ?a = ?res1,
        H2 : map_get (minify_mapC ?l 
          (fun x : ASP_ID => 
            if in_dec (EqClass_impl_DecEq ASP_ID) x (add_to_list ?l' ?a') then true else false)) ?a = ?res2
        |- _ =>
          assert (res1 = res2) by (
            eapply (map_get_minify_eq_under_add_to_list _ _ _ a') in H1;
            rewrite <- H1, <- H2; eauto);
          try find_injection; congruence
      end;
      match goal with
      | H1 : map_get (minify_mapD ?l 
          (fun x : _ => 
            if in_dec (EqClass_impl_DecEq _) x ?l' then true else false)) ?a = ?res1,
        H2 : map_get (minify_mapD ?l 
          (fun x : _ => 
            if in_dec (EqClass_impl_DecEq _) x (add_to_list ?l' ?a') then true else false)) ?a = ?res2
        |- _ =>
          assert (res1 = res2) by (
            eapply (mapD_get_minify_eq_under_add_to_list _ _ _ a') in H1;
            rewrite <- H1, <- H2; eauto);
          try find_injection; congruence
      end
    ).
  - simpl in *; intuition; eauto; subst.
    unfold supports_am; simpl in *; intuition; eauto;
    unfold generate_Plc_dispatcher in *;
    repeat (repeat break_match; simpl in *; subst; eauto; try congruence);
    match goal with
      | H1 : map_get (minify_mapD ?l 
          (fun x : _ => 
            if in_dec (EqClass_impl_DecEq _) x ?l' then true else false)) ?a = ?res1,
        H2 : map_get (minify_mapD ?l 
          (fun x : _ => 
            if in_dec (EqClass_impl_DecEq _) x (add_to_list ?l' ?a') then true else false)) ?a = ?res2
        |- _ =>
          assert (res1 = res2) by (
            eapply (mapD_get_minify_eq_under_add_to_list _ _ _ a') in H1;
            rewrite <- H1, <- H2; eauto);
          try find_injection; congruence
    end.
Qed.

Theorem man_gen_comp_works : forall t p backMan absMan amLib,
  lib_supports_manifest amLib backMan ->
  p = backMan.(my_abstract_plc) ->
  generate_manifest' t p backMan = absMan ->
  (* forall amLib, *)
  lib_supports_manifest amLib absMan ->
  (forall amConf,
    manifest_compiler absMan amLib = amConf ->
    (forall amConf',
      supports_am amConf amConf' ->
      am_config_support_exec t p amConf'
    )
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
    ).
    * destruct amConf'; simpl in *;
      unfold supports_am in *; intuition; simpl in *;
      pose proof (H3 a1 l0 targ targid p' ev ev');
      pose proof (H8 a1 l0 targ targid p' ev ev');
      repeat break_match; simpl in *;
      repeat find_injection;
      simpl in *; intuition; eauto; try congruence;
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
    * destruct amConf'; simpl in *;
      unfold supports_am in *; intuition; simpl in *;
      pose proof (H3 sig_aspid l targ targid p' ev ev');
      pose proof (H8 sig_aspid l targ targid p' ev ev');
      repeat break_match; simpl in *;
      repeat find_injection;
      simpl in *; intuition; eauto; try congruence;
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
    * destruct amConf'; simpl in *;
      unfold supports_am in *; intuition; simpl in *;
      pose proof (H3 hsh_aspid l targ targid p' ev ev');
      pose proof (H8 hsh_aspid l targ targid p' ev ev');
      repeat break_match; simpl in *;
      repeat find_injection;
      simpl in *; intuition; eauto; try congruence;
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
    * destruct amConf'; simpl in *;
      unfold supports_am in *; intuition; simpl in *;
      pose proof (H3 enc_aspid l targ targid p' ev ev');
      pose proof (H8 enc_aspid l targ targid p' ev ev');
      repeat break_match; simpl in *;
      repeat find_injection;
      simpl in *; intuition; eauto; try congruence;
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
    * destruct amConf'; simpl in *;
      unfold supports_am in *; intuition; simpl in *.
      pose proof (H4 p);
      pose proof (H9 p);
      repeat break_match; simpl in *;
      repeat find_injection;
      simpl in *; intuition; eauto; try congruence;
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
  - unfold lib_supports_manifest, manifest_compiler in *;
    destruct amConf; find_injection; simpl in *;
    unfold supports_am in *; intuition; simpl in *;
    pose proof (H5 p);
    pose proof (H11 p);
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
    pose proof (IHt1 _ _ _ _ H H0 E1 H5).
    destruct (manifest_compiler {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |} amLib) eqn:M1.
    pose proof (H6 {| concMan := concMan; aspCb := aspCb; plcCb := plcCb; pubKeyCb := pubKeyCb; uuidCb := uuidCb |} eq_refl {| concMan := concMan; aspCb := aspCb; plcCb := plcCb; pubKeyCb := pubKeyCb; uuidCb := uuidCb |} (supports_am_refl _)).
    clear H6.
    pose proof (IHt2 p {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |} absMan amLib). intuition. simpl in *.
    intuition.
    assert (p = my_abstract_plc). {
      pose proof (generate_manifest'_preserves_plc _ _ _ _ E1);
      simpl in *. repeat find_rewrite. eauto.
    }
    intuition.
    pose proof (H9 _ H3 amConf'). intuition.
    exists ({| concMan := concMan; aspCb := aspCb; plcCb := plcCb; pubKeyCb := pubKeyCb; uuidCb := uuidCb |}), amConf';
    intuition; eauto.
    eapply supports_am_trans; [ | eapply H4].
    eapply man_comp_cumul. eauto.
    eapply H1; eauto.
    eapply H3.
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
    pose proof (IHt1 _ _ _ _ H H0 E1 H5).
    destruct (manifest_compiler {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |} amLib) eqn:M1.
    pose proof (H6 {| concMan := concMan; aspCb := aspCb; plcCb := plcCb; pubKeyCb := pubKeyCb; uuidCb := uuidCb |} eq_refl {| concMan := concMan; aspCb := aspCb; plcCb := plcCb; pubKeyCb := pubKeyCb; uuidCb := uuidCb |} (supports_am_refl _)).
    clear H6.
    pose proof (IHt2 p {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |} absMan amLib). intuition. simpl in *.
    intuition.
    assert (p = my_abstract_plc). {
      pose proof (generate_manifest'_preserves_plc _ _ _ _ E1);
      simpl in *. repeat find_rewrite. eauto.
    }
    intuition.
    pose proof (H9 _ H3 amConf'). intuition.
    exists ({| concMan := concMan; aspCb := aspCb; plcCb := plcCb; pubKeyCb := pubKeyCb; uuidCb := uuidCb |}), amConf';
    intuition; eauto.
    eapply supports_am_trans; [ | eapply H4].
    eapply man_comp_cumul. eauto.
    eapply H1; eauto.
    eapply H3.
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
    pose proof (IHt1 _ _ _ _ H H0 E1 H5).
    destruct (manifest_compiler {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |} amLib) eqn:M1.
    pose proof (H6 {| concMan := concMan; aspCb := aspCb; plcCb := plcCb; pubKeyCb := pubKeyCb; uuidCb := uuidCb |} eq_refl {| concMan := concMan; aspCb := aspCb; plcCb := plcCb; pubKeyCb := pubKeyCb; uuidCb := uuidCb |} (supports_am_refl _)).
    clear H6.
    pose proof (IHt2 p {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := uuidPlcs;
         pubKeyPlcs := pubKeyPlcs;
         targetPlcs := targetPlcs;
         policy := policy
       |} absMan amLib). intuition. simpl in *.
    intuition.
    assert (p = my_abstract_plc). {
      pose proof (generate_manifest'_preserves_plc _ _ _ _ E1);
      simpl in *. repeat find_rewrite. eauto.
    }
    intuition.
    pose proof (H9 _ H3 amConf'). intuition.
    exists ({| concMan := concMan; aspCb := aspCb; plcCb := plcCb; pubKeyCb := pubKeyCb; uuidCb := uuidCb |}), amConf';
    intuition; eauto.
    eapply supports_am_trans; [ | eapply H4].
    eapply man_comp_cumul. eauto.
    eapply H1; eauto.
    eapply H3.
Qed.

Theorem manifest_generator_compiler_soundess : forall t p absMan amLib amConf,
  generate_manifest t p = absMan ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  forall st,
    (* Note, this should be trivial typically as amConf = st.(st_AM_config) and refl works *)
    supports_am amConf (st.(st_AM_config)) ->  
    exists st', 
      build_cvm (copland_compile t) st = (resultC tt, st') \/
      build_cvm (copland_compile t) st = (errC (dispatch_error Runtime), st').
Proof.
  intros.
  eapply well_formed_am_config_impl_executable.
  - unfold generate_manifest in *; unfold empty_Manifest in *;
    simpl in *;
    assert (lib_supports_manifest amLib {| my_abstract_plc := p; asps := []; uuidPlcs := []; pubKeyPlcs := []; targetPlcs := []; policy := empty_PolicyT |}) by (unfold lib_supports_manifest; simpl in *; intuition; eauto);
    assert (p = my_abstract_plc {| my_abstract_plc := p; asps := []; uuidPlcs := []; pubKeyPlcs := []; targetPlcs := []; policy := empty_PolicyT |}) by (simpl in *; eauto);
    pose proof (man_gen_comp_works t _ _ _ _ H3 H4 H H0 _ H1); eauto.
  - eapply supports_am_refl.
Qed.

Definition manifest_support_am_config (m : Manifest) (ac : AM_Config) : Prop :=
  (forall a, In a (m.(asps)) -> 
    forall l targ targid p' ev ev',
    (exists res, ac.(aspCb) (asp_paramsC a l targ targid) p' ev ev' = resultC res) \/
    (ac.(aspCb) (asp_paramsC a l targ targid) p' ev ev' = errC Runtime)) /\
  (forall p, In p (m.(uuidPlcs)) ->
    (exists res, ac.(plcCb) p = resultC res) \/
    (ac.(plcCb) p = errC Runtime)) /\
  (forall p, In p (m.(pubKeyPlcs)) ->
    (exists res, ac.(pubKeyCb) p = resultC res) \/
    (ac.(pubKeyCb) p = errC Runtime)).
  
(* 

Theorem manifest_support_am_config_from_man_gen : forall t,
  generate_manifest' t p backMan = absMan ->

  manifest_support_am_config absMan () *)

Theorem manifest_support_am_config_compiler : forall absMan amLib,
  lib_supports_manifest amLib absMan ->
  manifest_support_am_config absMan (manifest_compiler absMan amLib).
Proof.
  unfold lib_supports_manifest, manifest_support_am_config, 
    manifest_compiler, generate_PubKey_dispatcher, generate_Plc_dispatcher in *;
  simpl in *; intuition;
  repeat break_match; simpl in *; intuition; eauto;
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
Qed.

Fixpoint manifest_support_term (m : Manifest) (t : Term) : Prop :=
  match t with
  | asp a =>
      match a with
      | NULL => True
      | CPY => True
      | SIG => 
          In sig_aspid (m.(asps))
      | HSH =>
          In hsh_aspid (m.(asps))
      | ENC p =>
          In enc_aspid (m.(asps)) /\
          In p (m.(pubKeyPlcs))
      | ASPC _ _ (asp_paramsC aspid _ _ _) =>
          In aspid (m.(asps))
      end
  | att p' t' =>
      In p' (m.(uuidPlcs))
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

Theorem manifest_support_am_config_impl_am_config: forall t p absMan amConf,
  manifest_support_am_config absMan amConf ->
  manifest_support_term absMan t ->
  am_config_support_exec t p amConf.
Proof.
  induction t; simpl in *; intuition; eauto;
  unfold manifest_support_am_config in *; intuition; eauto;
  repeat (try break_match; simpl in *; intuition; eauto).
  - pose proof (IHt1 p absMan amConf); 
    pose proof (IHt2 p absMan amConf); intuition;
    exists amConf, amConf; eauto.
  - pose proof (IHt1 p absMan amConf); 
    pose proof (IHt2 p absMan amConf); intuition;
    exists amConf, amConf; eauto.
  - pose proof (IHt1 p absMan amConf); 
    pose proof (IHt2 p absMan amConf); intuition;
    exists amConf, amConf; eauto.
Qed.

Lemma manifest_support_term_unfold : forall t p backMan t',
  manifest_support_term backMan t ->
  p = (my_abstract_plc backMan) ->
  manifest_support_term (generate_manifest' t' p backMan) t.
Proof.
  induction t; simpl in *; intuition; eauto;
  repeat break_match; simpl in *; intuition; eauto.
Qed.

Theorem man_gen_always_supports : forall t p backMan,
  p = (my_abstract_plc backMan) ->
  manifest_support_term (generate_manifest' t p backMan) t.
Proof.
  induction t; intuition; try (simpl in *; eauto; fail);
  try (simpl in *; intuition; eauto; [
    eapply manifest_support_term_unfold; eauto | ];
    rewrite H; eauto).
  - repeat (try break_match; simpl in *; try congruence; eauto);
    try (subst; rewrite eqb_refl in *; congruence).
Qed.

(* This proof tries to instead leverage the manifest_support notions *)
Theorem man_gen_soundness' : forall t p absMan amLib amConf,
  generate_manifest t p = absMan ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  forall st,
    (* Note, this should be trivial typically as amConf = st.(st_AM_config) and refl works *)
    supports_am amConf (st.(st_AM_config)) ->  
  exists st', 
    build_cvm (copland_compile t) st = (resultC tt, st') \/
    build_cvm (copland_compile t) st = (errC (dispatch_error Runtime), st').
Proof.
  intros.
  eapply well_formed_am_config_impl_executable.
  - unfold generate_manifest, empty_Manifest in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config.
    * eapply manifest_support_am_config_compiler; eauto.
    * (* NOTE: This is the important one, substitute proof of any manifest here *)
      rewrite <- H; eapply man_gen_always_supports; simpl in *; eauto.
  - rewrite H1; eauto.
  Unshelve. eapply min_id_type.
Qed.


Lemma manifest_support_term_unfold_old' : forall t p backEnv t' absMan absMan',
  map_get backEnv p = Some absMan ->
  manifest_support_term absMan t ->
  map_get (manifest_generator' p t' backEnv) p = Some absMan' ->
  manifest_support_term absMan' t.
Proof.
  induction t; intuition.
  - simpl in *;
    repeat break_match; simpl in *; intuition; eauto;
    eapply man_gen_self_map_getter in H;
    destruct H; intuition; eauto;
    find_rewrite; find_injection; eauto.
  - simpl in *;
    eapply man_gen_self_map_getter in H;
    destruct H; intuition; eauto;
    find_rewrite; find_injection; eauto.
  - simpl in *; intuition; eauto.
  - simpl in *; intuition; eauto.
  - simpl in *; intuition; eauto.
Qed.

Theorem map_get_man_gen_self_never_none : forall p t backMan,
  exists res, map_get (manifest_generator' p t backMan) p = Some res.
Proof.
  induction t; simpl in *; intuition; eauto.
  - unf; repeat break_match; simpl in *; eauto; subst; try congruence;
    try (rewrite mapC_get_works; eexists; intuition; eauto; congruence).
  - unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *.
    pose proof (man_gen_map_getter t p0 p (let
           '{|
              my_abstract_plc := oldPlc;
              asps := oldasps;
              uuidPlcs := oldKnowsOf;
              pubKeyPlcs := oldContext;
              targetPlcs := oldTargets;
              policy := oldPolicy
            |} := match map_get backMan p with
                  | Some mm => mm
                  | None => empty_Manifest
                  end in
            {|
              my_abstract_plc := oldPlc;
              asps := oldasps;
              uuidPlcs := p0 :: oldKnowsOf;
              pubKeyPlcs := oldContext;
              targetPlcs := oldTargets;
              policy := oldPolicy
            |}) backMan). destruct H; intuition; eauto.
Qed.


Require Import Coq.Program.Tactics.

Set Nested Proofs Allowed.

(*
Lemma asdf : forall t1 t2 tp p absMan e,
map_get (manifest_generator' tp t2 
            (manifest_generator' tp t1 e)) p = Some absMan -> 
exists m', 
map_get (manifest_generator' tp t1 e) p = Some m' /\ 
manifest_subset m' absMan.
Proof.
  intros. 
Admitted.
*)


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


Lemma places_env_has_manifest : forall t p tp e,
In p (places tp t) -> 
exists m, 
map_get (manifest_generator' tp t e) p = Some m.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    ff.
    door; try solve_by_inversion.
    subst.
    destruct a; 
    unfold asp_manifest_generator;
    unfold asp_manifest_update;
    unfold manifest_update_env;
    ff;
    eexists;
    eapply mapC_get_works.

  - (* at case *)

    ff.
    door; ff.
    subst.
    unfold at_manifest_generator.
    unfold knowsof_manifest_update.
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
            uuidPlcs := p :: uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |})

          (manifest_generator' p t
       (map_set e p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            uuidPlcs := p :: uuidPlcs;
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
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) p0 = Some {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := p :: uuidPlcs;
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
        uuidPlcs := p :: uuidPlcs;
        pubKeyPlcs := pubKeyPlcs;
        targetPlcs := targetPlcs;
        policy := policy
      |}) (p := p0).
      find_apply_hyp_hyp.
      destruct_conjs.

      exists H0.
      eauto.


      +

      subst.

      assert (Environment_subset 
      (map_set e p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            uuidPlcs := p :: uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |})

          (manifest_generator' p t
       (map_set e p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            uuidPlcs := p :: uuidPlcs;
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
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) p0 = Some {|
         my_abstract_plc := my_abstract_plc;
         asps := asps;
         uuidPlcs := p :: uuidPlcs;
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
        uuidPlcs := p :: uuidPlcs;
        pubKeyPlcs := pubKeyPlcs;
        targetPlcs := targetPlcs;
        policy := policy
      |}) (p := p0).
      find_apply_hyp_hyp.
      destruct_conjs.

      exists H0.
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
    (*
    Lemma manifest_generator_cumul : forall t p e1 e2,
    Environment_subset e1 e2 ->
    Environment_subset e1 (manifest_generator' p t e2).
Proof.
    
    *)
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

Lemma manifest_supports_term_sub : forall m1 m2 t,
manifest_subset m1 m2 ->
manifest_support_term m1 t -> 
manifest_support_term m2 t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* asp case *)
    ff.
    ff.
    subst.
    unfold manifest_subset in *.
    destruct_conjs.
    eauto.
  - (* at case *)
    ff.
    unfold manifest_subset in *.
    destruct_conjs.
    eauto.
  - (* lseq case *)
    ff.
    destruct_conjs.
    split; eauto.
  - (* bseq case *)
    ff.
    destruct_conjs.
    split; eauto.
  - (* bpar case *)
    ff.
    destruct_conjs.
    split; eauto.
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

Lemma fdsa : forall e e2 p p0 m absMan,
Environment_subset
  (map_set e p0 m) 
  (e2) -> 
map_get e2 p0 = Some absMan -> 
In p (uuidPlcs m) -> 
In p (uuidPlcs absMan).
Proof.
  intros.
  assert (map_get (map_set e p0 m) p0 = Some m).
  {
    eapply mapC_get_works; eauto.
  }
  assert (manifest_subset m absMan).
  {
    eapply env_subset_man_subset; eauto.
  }

  unfold manifest_subset in *.
  destruct_conjs.
  eauto.
Qed.

Require Import Eqb_Evidence.

Check places.
(*
places
	 : Plc -> Term -> list Plc
*)

(*
Check fromSome.
fromSome (map_get (manifest_generator' tp t backMan) p) empty_Manifest = absMan ->
*)

Theorem man_gen_old_always_supports : forall t t' tp p backMan absMan,
  map_get (manifest_generator' tp t backMan) p = Some absMan ->
  In p (places tp t) ->
  In t' (place_terms t tp p) ->
  manifest_support_term absMan t'.
Proof.
  (*
  intros.
  assert ((map_get (manifest_generator' tp t backMan) p) = Some absMan).
  {
    admit.
  }
  unfold fromSome in *.
  find_rewrite.

  generalizeEverythingElse t.

  *)



  induction t; intuition.
  - repeat (try break_match; 
      unfold asp_manifest_generator, manifest_update_env, knowsof_manifest_update,
        aspid_manifest_update, update_manifest_policy_targ, pubkey_manifest_update in *;
      subst; simpl in *; intuition; eauto; try congruence;
      repeat find_rewrite;
      repeat find_injection;
      simpl in * );
    try (rewrite mapC_get_works in *; simpl in *; repeat find_injection; simpl in *; intuition; eauto).

    (*
    +
    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    (*
    Theorem mapC_get_works{A B:Type} `{H : EqClass A} : forall m (x:A) (v:B),
  map_get (map_set m x v) x = Some v.
    *)

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.

    +

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.

    +

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.

    +

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.

    +

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.

    +

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.

    +

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.

    +

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.
   
    +

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.
    
    +

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    rewrite Maps.mapC_get_works in H.
    ff.
    eauto.
    *)


  - (* at case *)
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

    assert (Environment_subset 

    (map_set backMan p0
            {|
              my_abstract_plc := my_abstract_plc;
              asps := asps;
              uuidPlcs := p :: uuidPlcs;
              pubKeyPlcs := pubKeyPlcs;
              targetPlcs := targetPlcs;
              policy := policy
            |})
            (manifest_generator' p t
            (map_set backMan p0
               {|
                 my_abstract_plc := my_abstract_plc;
                 asps := asps;
                 uuidPlcs := p :: uuidPlcs;
                 pubKeyPlcs := pubKeyPlcs;
                 targetPlcs := targetPlcs;
                 policy := policy
               |}))
    ).

    {
      eapply manifest_generator_cumul'.
    }

    eapply fdsa; eauto.
    simpl.
    eauto.

    ++
    assert (tp = p0).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    assert (
      Environment_subset 
      ((map_set backMan p0
      {|
        my_abstract_plc := empty_Manifest_Plc;
        asps := [];
        uuidPlcs := [p];
        pubKeyPlcs := [];
        targetPlcs := [];
        policy := empty_PolicyT
      |}))

      (manifest_generator' p t
         (map_set backMan p0
            {|
              my_abstract_plc := empty_Manifest_Plc;
              asps := [];
              uuidPlcs := [p];
              pubKeyPlcs := [];
              targetPlcs := [];
              policy := empty_PolicyT
            |}))

    ).
    {
      eapply manifest_generator_cumul'.
    }

    eapply fdsa; eauto.
    simpl.
    eauto.
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

  (*

  Lemma in_plc_term : forall p p0 t,
place_terms t p p0 <> [] ->
In p0 (places p t).
  
  *)


  + (* tp <> p *)
    destruct H0.
    ++
      subst.
      rewrite eqb_plc_refl in *.
      solve_by_inversion.
    ++

(*
    find_apply_lem_hyp asdf.
    *)

    (*
    assert (In p (places' t1 []) \/ In p (places' t2 [])).
    {
      admit.
    }

    clear H0.
    *)

  
  

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
  
    (*
  
    Lemma in_plc_term : forall p p0 t,
  place_terms t p p0 <> [] ->
  In p0 (places p t).
    
    *)
  
  
    + (* tp <> p *)
      destruct H0.
      ++
        subst.
        rewrite eqb_plc_refl in *.
        solve_by_inversion.
      ++
  
  (*
      find_apply_lem_hyp asdf.
      *)
  
      (*
      assert (In p (places' t1 []) \/ In p (places' t2 [])).
      {
        admit.
      }
  
      clear H0.
      *)
  
    
    
  
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


  - (* bpar case *)

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

  (*

  Lemma in_plc_term : forall p p0 t,
place_terms t p p0 <> [] ->
In p0 (places p t).
  
  *)


  + (* tp <> p *)
    destruct H0.
    ++
      subst.
      rewrite eqb_plc_refl in *.
      solve_by_inversion.
    ++

(*
    find_apply_lem_hyp asdf.
    *)

    (*
    assert (In p (places' t1 []) \/ In p (places' t2 [])).
    {
      admit.
    }

    clear H0.
    *)

  
  

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


  (*

  - (* lseq case *) 
  ff.
  ff.
  +
  door; try solve_by_inversion.
  subst.
  ff.
  split.
    ++
    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    find_apply_lem_hyp asdf.
    destruct_conjs.

    eapply manifest_supports_term_sub.
    eassumption.


    eapply IHt1.
    eassumption.
    apply top_plc_refl.

  ++
  eapply IHt2.
  eassumption.

  assert (tp = p).
  {
    eapply eqb_eq_plc; eauto.
  }
  subst.


  apply top_plc_refl.



  + 
  assert ((In t' (place_terms t1 tp p)) \/ (In t' (place_terms t2 tp p))).
  {
    eapply in_app_or; eauto.
  }
  door.
    ++

    
    find_apply_lem_hyp asdf.
    destruct_conjs.

    eapply manifest_supports_term_sub.
    eassumption.


    eapply IHt1.
    eassumption.
    eassumption.

    ++

    eapply IHt2.
    eassumption.
    eassumption.

  - (* bseq case *)

    ff.
    ff.
    +
      door; try solve_by_inversion.
      subst.
      ff.
      split.
      ++

      assert (tp = p).
      {
        eapply eqb_eq_plc; eauto.
      }
      subst.
  
      find_apply_lem_hyp asdf.
      destruct_conjs.
  
      eapply manifest_supports_term_sub.
      eassumption.
  
  
      eapply IHt1.
      eassumption.
      apply top_plc_refl.
  
    ++
    eapply IHt2.
    eassumption.
  
    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.
  
  
    apply top_plc_refl.
  
    + 
    assert ((In t' (place_terms t1 tp p)) \/ (In t' (place_terms t2 tp p))).
    {
      eapply in_app_or; eauto.
    }
    door.
      ++

      assert (exists mm, map_get (manifest_generator' tp t1 backMan) p = Some mm).
      {
        admit.
      }
      destruct_conjs.

      eapply manifest_supports_term_sub with (m1:= H2).

      assert (Environment_subset 
      (manifest_generator' tp t1 backMan)
      (manifest_generator' tp t2 (manifest_generator' tp t1 backMan))
      ).
      {
        eapply manifest_generator_cumul'.
      }

      eapply env_subset_man_subset.
      apply H4.
      apply H3.

      eassumption.

      
      
      

      eapply IHt1.
      eassumption.
      eassumption.
  
      (*
      find_apply_lem_hyp asdf.
      destruct_conjs.
  
      eapply manifest_supports_term_sub.
      eassumption.
  
  
      eapply IHt1.
      eassumption.
      eassumption.
      *)
  
      ++
  
      eapply IHt2.
      eassumption.
      eassumption.


  - (* bpar case *)


  ff.
  ff.
  +
    door; try solve_by_inversion.
    subst.
    ff.
    split.
    ++

    assert (tp = p).
    {
      eapply eqb_eq_plc; eauto.
    }
    subst.

    find_apply_lem_hyp asdf.
    destruct_conjs.

    eapply manifest_supports_term_sub.
    eassumption.


    eapply IHt1.
    eassumption.
    apply top_plc_refl.

  ++
  eapply IHt2.
  eassumption.

  assert (tp = p).
  {
    eapply eqb_eq_plc; eauto.
  }
  subst.


  apply top_plc_refl.



  + 
  assert ((In t' (place_terms t1 tp p)) \/ (In t' (place_terms t2 tp p))).
  {
    eapply in_app_or; eauto.
  }
  door.
    ++

    find_apply_lem_hyp asdf.
    destruct_conjs.

    eapply manifest_supports_term_sub.
    eassumption.


    eapply IHt1.
    eassumption.
    eassumption.

    ++

    eapply IHt2.
    eassumption.
    eassumption.




Admitted.

*)


(*

  - simpl in *; unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence.
    * pose proof (man_gen_map_getter t p p0 {|
               my_abstract_plc := my_abstract_plc;
               asps := asps;
               uuidPlcs := p :: uuidPlcs;
               pubKeyPlcs := pubKeyPlcs;
               targetPlcs := targetPlcs;
               policy := policy
             |} backMan) as H'; simpl in *;
      destruct H'; intuition; simpl in *;
      repeat find_rewrite; find_injection; eauto.
    * unfold empty_Manifest in *; find_injection; simpl in *.
      pose proof (man_gen_map_getter t p p0 {|
               my_abstract_plc := empty_Manifest_Plc;
               asps := [];
               uuidPlcs := [p];
               pubKeyPlcs := [];
               targetPlcs := [];
               policy := empty_PolicyT
             |} backMan) as H'; simpl in *;
      destruct H'; intuition; simpl in *;
      repeat find_rewrite; find_injection; eauto.
  - simpl in *; unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence; intuition.
    * destruct (map_get (manifest_generator' p t1 backMan) p) eqn:M1.
      ** pose proof (manifest_support_term_unfold_old' t1 p (manifest_generator' p t1 backMan) t2 m absMan); eauto.
      ** destruct (map_get_man_gen_self_never_none p t1 backMan); congruence.
    * eapply IHt2 in H as H2'; eauto.
  - simpl in *; unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence; intuition.
    * destruct (map_get (manifest_generator' p t1 backMan) p) eqn:M1.
      ** pose proof (manifest_support_term_unfold_old' t1 p (manifest_generator' p t1 backMan) t2 m absMan); eauto.
      ** destruct (map_get_man_gen_self_never_none p t1 backMan); congruence.
    * eapply IHt2 in H as H2'; eauto.
  - simpl in *; unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence; intuition.
    * destruct (map_get (manifest_generator' p t1 backMan) p) eqn:M1.
      ** pose proof (manifest_support_term_unfold_old' t1 p (manifest_generator' p t1 backMan) t2 m absMan); eauto.
      ** destruct (map_get_man_gen_self_never_none p t1 backMan); congruence.
    * eapply IHt2 in H as H2'; eauto.
Qed.

*)



  (*
Theorem man_gen_old_always_supports : forall t p backMan absMan,
  map_get (manifest_generator' p t backMan) p = Some absMan ->
  manifest_support_term absMan t.
Proof.
  induction t; intuition.
  - repeat (try break_match; 
      unfold asp_manifest_generator, manifest_update_env, knowsof_manifest_update,
        aspid_manifest_update, update_manifest_policy_targ, pubkey_manifest_update in *;
      subst; simpl in *; intuition; eauto; try congruence;
      repeat find_rewrite;
      repeat find_injection;
      simpl in * );
    try (rewrite mapC_get_works in *; simpl in *; repeat find_injection; simpl in *; intuition; eauto).

  - simpl in *; unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence.
    * pose proof (man_gen_map_getter t p p0 {|
               my_abstract_plc := my_abstract_plc;
               asps := asps;
               uuidPlcs := p :: uuidPlcs;
               pubKeyPlcs := pubKeyPlcs;
               targetPlcs := targetPlcs;
               policy := policy
             |} backMan) as H'; simpl in *;
      destruct H'; intuition; simpl in *;
      repeat find_rewrite; find_injection; eauto.
    * unfold empty_Manifest in *; find_injection; simpl in *.
      pose proof (man_gen_map_getter t p p0 {|
               my_abstract_plc := empty_Manifest_Plc;
               asps := [];
               uuidPlcs := [p];
               pubKeyPlcs := [];
               targetPlcs := [];
               policy := empty_PolicyT
             |} backMan) as H'; simpl in *;
      destruct H'; intuition; simpl in *;
      repeat find_rewrite; find_injection; eauto.
  - simpl in *; unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence; intuition.
    * destruct (map_get (manifest_generator' p t1 backMan) p) eqn:M1.
      ** pose proof (manifest_support_term_unfold_old' t1 p (manifest_generator' p t1 backMan) t2 m absMan); eauto.
      ** destruct (map_get_man_gen_self_never_none p t1 backMan); congruence.
    * eapply IHt2 in H as H2'; eauto.
  - simpl in *; unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence; intuition.
    * destruct (map_get (manifest_generator' p t1 backMan) p) eqn:M1.
      ** pose proof (manifest_support_term_unfold_old' t1 p (manifest_generator' p t1 backMan) t2 m absMan); eauto.
      ** destruct (map_get_man_gen_self_never_none p t1 backMan); congruence.
    * eapply IHt2 in H as H2'; eauto.
  - simpl in *; unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *; simpl in *;
    repeat break_match; subst; simpl in *; eauto; try congruence; intuition.
    * destruct (map_get (manifest_generator' p t1 backMan) p) eqn:M1.
      ** pose proof (manifest_support_term_unfold_old' t1 p (manifest_generator' p t1 backMan) t2 m absMan); eauto.
      ** destruct (map_get_man_gen_self_never_none p t1 backMan); congruence.
    * eapply IHt2 in H as H2'; eauto.
Qed.
*)

(*

Theorem manifest_generator_compiler_soundness_old : forall t p absMan amLib amConf,
  map_get (manifest_generator t p) p = Some absMan ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  forall st,
    (* Note, this should be trivial typically as amConf = st.(st_AM_config) and refl works *)
    supports_am amConf (st.(st_AM_config)) ->  
  exists st', 
    build_cvm (copland_compile t) st = (resultC tt, st') \/
    build_cvm (copland_compile t) st = (errC (dispatch_error Runtime), st').
Proof.
  intros.
  eapply well_formed_am_config_impl_executable.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config.
    * eapply manifest_support_am_config_compiler; eauto.
    * (* NOTE: This is the important one, substitute proof of any manifest here *)
      eapply man_gen_old_always_supports; eauto.
      apply top_plc_refl.
  - rewrite H1; eauto.
  Unshelve. eapply min_id_type.
Qed.

*)

Theorem manifest_generator_compiler_soundness_distributed : forall t tp p absMan amLib amConf,
  map_get (manifest_generator t tp) p = Some absMan ->
  In p (places tp t) ->
  lib_supports_manifest amLib absMan ->
  manifest_compiler absMan amLib = amConf ->
  forall st,
    (* Note, this should be trivial typically as amConf = st.(st_AM_config) and refl works *)
    supports_am amConf (st.(st_AM_config)) ->  

    (  forall t', 
         In t' (place_terms t tp p) -> 
         st.(st_pl) = p -> 
        
         exists st', 
        
        build_cvm (copland_compile t') st = (resultC tt, st') \/
        build_cvm (copland_compile t') st = (errC (dispatch_error Runtime), st')
    ).
Proof.
  intros.
  eapply well_formed_am_config_impl_executable.
  - unfold manifest_generator, e_empty in *; simpl in *.
    eapply manifest_support_am_config_impl_am_config.
    * eapply manifest_support_am_config_compiler; eauto.
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
    find_rewrite; eauto.
  Unshelve. eapply min_id_type.
Qed.

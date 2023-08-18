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

Definition p1 : Plc. Admitted.
Definition p2 : Plc. Admitted.
Definition p3 : Plc. Admitted.
Definition asp1 : ASP_ID. Admitted.
Definition asp2 : ASP_ID. Admitted.
Example p1_neq_p2 : eqb p2 p1 = false. Admitted.
Example p1_neq_p2' : eqb p1 p2 = false. Admitted.
Definition test_term := (att p2 (att p1 ((att p2 (asp (ASPC ALL COMP (asp_paramsC asp1 nil p2 asp2))))))).

Compute (knowsOf_uuid' p1 p1 test_term).
Compute (knowsOf_uuid'' p1 p1 test_term).
(* Definition knowsOf_uuid (p : Plc) (t : Term) : list ASP_ID :=
  p :: (knowsOf_uuid' p t). *)

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

Theorem manifest_generator'_knows_plcs : forall t p backEnv envM,
  manifest_generator' p t backEnv = envM ->
  (forall p',
    map_get backEnv p' = None ->
    (In p' (p :: (knowsOf_uuid' p p' t)) <->
    exists absMan, map_get envM p' = Some absMan)
  ).
Proof.
  induction t; simpl in *; intros.
  - intuition; subst; eauto.
    * unf; break_match; subst; try congruence;
      try rewrite mapC_get_works; eauto.
    * unf; repeat break_match; subst; simpl in *;
      breq p p'; eauto;
      erewrite map_distinct_key_rw in *; eauto;
      try (eapply empty_Manifest); 
      try (find_rewrite); eauto; 
      try (destruct H1; congruence).
  - intuition; subst; eauto.
    * unf; repeat break_match; subst; simpl in *;
      try congruence; breq p p'; eauto;
      repeat find_injection; try congruence.
      ** pose proof (man_gen_map_getter t p' p' ({|
            my_abstract_plc := empty_Manifest_Plc;
            asps := [];
            uuidPlcs := [p'];
            pubKeyPlcs := [];
            targetPlcs := [];
            policy := empty_PolicyT
          |}) backEnv).
        destruct H; intuition; eauto.
      ** pose proof (man_gen_map_getter t p p' ({|
            my_abstract_plc := empty_Manifest_Plc;
            asps := [];
            uuidPlcs := [p];
            pubKeyPlcs := [];
            targetPlcs := [];
            policy := empty_PolicyT
          |}) backEnv).
        destruct H1; intuition; eauto.
    * unf. repeat break_match; subst;
      try (rewrite eqb_leibniz in *; subst; eauto; try congruence).
      ** destruct ((manifest_generator' p t
       (map_set backEnv p0
          {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            uuidPlcs := p :: uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |}))) eqn:E;
        try (exfalso; eapply manifest_generator_never_empty; eauto; fail).
        assert ( map_get
      (map_set backEnv p0
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) p' = None). erewrite map_distinct_key_rw; eauto;
         try (eapply empty_Manifest); intros HC;
         rewrite <- eqb_leibniz in *; try congruence.
        pose proof (IHt _ _ _ E p' H); intuition;
        breq p p'; eauto.
        eapply H5.
        destruct t; simpl in *; try congruence; eauto.
        assert ( map_get
      (map_set backEnv p0
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) p' = None). erewrite map_distinct_key_rw; eauto;
         try (eapply empty_Manifest); intros HC;
         rewrite <- eqb_leibniz in *; try congruence;
         

    ; repeat break_match; subst; simpl in *;
      try congruence; breq p p'; eauto;
      repeat find_injection; try congruence.
        destruct ((manifest_generator' p t
          (map_set backEnv p'
              {|
                my_abstract_plc := empty_Manifest_Plc;
                asps := [];
                uuidPlcs := [p];
                pubKeyPlcs := [];
                targetPlcs := [];
                policy := empty_PolicyT
              |}))) eqn:E; 
          try (exfalso; eapply manifest_generator_never_empty; eauto; fail).
          pose proof (IHt _ _ _ E p').

      erewrite map_distinct_key_rw in *; eauto;
      try (eapply empty_Manifest); 
      try (find_rewrite); eauto; 
      try (destruct H1; congruence).

    

Theorem man_gen_only_available_if_known : forall t p backEnv envM,
  map_get backEnv p = None ->
  manifest_generator' p t backEnv = envM ->
  (* manifest_generator t p = envM -> *)
  (forall p',
    map_get backEnv p' = None ->
    (exists man, map_get envM p' = Some man) <-> 
    (p = p' \/ In p' (mentioned_places t))
  ).
Proof.
  induction t; simpl in *; intros; unf; subst.
  - intuition; eauto.
    * repeat break_match; try congruence; subst;
      breq p p';
      rewrite map_distinct_key_rw in H0; eauto;
      try eapply empty_Manifest;
      find_rewrite;
      destruct H0; congruence.
    * subst; rewrite mapC_get_works; eauto.
  - repeat break_match; subst; simpl in *; try congruence;
    repeat find_injection; subst.
    destruct ((manifest_generator' p t
      (map_set backEnv p0
          {|
            my_abstract_plc := empty_Manifest_Plc;
            asps := [];
            uuidPlcs := [p];
            pubKeyPlcs := [];
            targetPlcs := [];
            policy := empty_PolicyT
          |}))) eqn:E;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail).
    intuition; eauto.
    * erewrite IHt in H0; eauto.
    assert (map_get (map_set backEnv p0
         {|
           my_abstract_plc := empty_Manifest_Plc;
           asps := [];
           uuidPlcs := [p];
           pubKeyPlcs := [];
           targetPlcs := [];
           policy := empty_PolicyT
         |}) p = None). admit.
    pose proof (IHt _ _ _ H0 E p').
      
    destruct ((manifest_generator' p t
        (map_set backEnv p0
           (let
            '{|
               my_abstract_plc := oldPlc;
               asps := oldasps;
               uuidPlcs := oldKnowsOf;
               pubKeyPlcs := oldContext;
               targetPlcs := oldTargets;
               policy := oldPolicy
             |} :=
             match map_get backEnv p0 with
             | Some mm => mm
             | None =>
                 {|
                   my_abstract_plc := empty_Manifest_Plc;
                   asps := [];
                   uuidPlcs := [];
                   pubKeyPlcs := [];
                   targetPlcs := [];
                   policy := empty_PolicyT
                 |}
             end in
             {|
               my_abstract_plc := oldPlc;
               asps := oldasps;
               uuidPlcs := p :: oldKnowsOf;
               pubKeyPlcs := oldContext;
               targetPlcs := oldTargets;
               policy := oldPolicy
             |})))) eqn:E;
    

  induction t; simpl in *; intuition; subst; eauto; try congruence;
  unf; grind; try (rewrite eqb_leibniz in *; subst; eauto);
  try (
    match goal with
    | H : exists m, None = Some _ |- _ => 
        destruct H; try (find_rewrite);
        intuition; congruence
    end
  );
  try (rewrite eqb_refl in *; congruence).

  induction t; simpl in *; intuition; subst; eauto; try congruence.
  - destruct a; simpl in *; 
    repeat break_match; intuition; eauto;
    try (rewrite eqb_leibniz in *; eauto);
    try (destruct H0; congruence).
  - destruct a; simpl in *;
    repeat break_match; intuition; eauto;
    rewrite eqb_refl in *; congruence.
  - unfold manifest_generator. simpl.
    destruct (eqb p p') eqn:E; eauto.
    destruct a; simpl in *; intuition.
    * admit.
    * 
    destruct a; simpl in *; 
    repeat break_match; intuition; eauto;
    try (rewrite eqb_leibniz in *; eauto).
    try (destruct H0; congruence);
    simpl in *; intuition; subst; eauto.

  induction t; intuition; eauto; subst; eauto;
  try (breq p p'; intuition; eauto; try congruence);
  try (repeat break_match; simpl in *; intuition; subst; unf;
    repeat break_match; simpl in *; intuition; eauto;
    try congruence;
    rewrite mapC_get_works; eauto; fail).
  - destruct a; simpl in *; unf; break_match; subst;
    try (erewrite map_distinct_key_rw in H2; eauto;
    try (eapply empty_Manifest);
    find_rewrite; 
    destruct H2; congruence; fail).
  - destruct a; simpl in *; try (exfalso; eauto; fail); unf;
    repeat break_match; simpl in *;
    repeat find_injection; intuition; eauto; subst;
    try congruence.
    * 
    rewrite mapC_get_works; eauto.
  - repeat break_match; simpl in *; intuition; subst; unf;
    repeat break_match; simpl in *; intuition; eauto;
    rewrite mapC_get_works; eauto.
  - 
    * unf.
      destruct a; simpl in *; intuition; subst; unf.
      unf; repeat break_match; repeat find_injection;
      simpl in *.
      ** 



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
      rewrite H2 in H3; intuition; eauto; subst.

    

Theorem manifest_generator_impl_static_executable_manifest : forall t p backEnv envM,
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
  
Qed.


Theorem manifest_generator_works : forall t p backEnv envM,
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
Qed.


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

Theorem executable_impl_precond : forall t p backEnv envM,
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
Admitted.

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



Lemma stupid_map_killer : forall a Local_ASPS st_pl st_ev p t m l d,
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


Global Hint Resolve stupid_map_killer : core.
Global Hint Resolve man_gen_aspid_in : core.

Lemma updated_map_includes_updated_asp : forall (l : MapC ASP_ID (CakeML_ASPCallback CallBackErrors)) a p t m,
  (exists cb : CakeML_ASPCallback CallBackErrors, map_get l a = Some cb) ->
  (map_get (minify_mapC 
    l (fun x : ASP_ID => if in_dec (EqClass_impl_DecEq ASP_ID) x (asps (aspid_manifest_update a (update_manifest_policy_targ p t m))) then true else false)) a = None) -> False.
Proof.
  intros.
  induction l; simpl in *.
  - destruct H; congruence.
  - destruct a0, (eqb a a0) eqn:E, 
    (in_dec (EqClass_impl_DecEq ASP_ID) a0 (asps (aspid_manifest_update a (update_manifest_policy_targ p t m))));
    simpl in *; try (rewrite E in *); try congruence; eauto.
    rewrite eqb_leibniz in *; subst; destruct n; eauto.
Qed.

Global Hint Resolve updated_map_includes_updated_asp : core.
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

Theorem man_gen_subterm : forall (t : Term) getPl backEnv p absMan,
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
Admitted.

Definition well_formed_am_config (t : Term) (tp : Plc) :=
  (forall x, (In x (knowsOf_asps tp tp t)) -> ())

Theorem well_formed_am_config_impl_executable : forall t,


Theorem manifest_compiler_sound : forall t p backEnv envM,
  manifest_generator' p t backEnv = envM ->
  (forall p' absMan, 
    map_get backEnv p' = None ->
    map_get envM p' = Some absMan ->
    (forall amLib amConf, 
      lib_supports_manifest amLib absMan ->
      manifest_compiler absMan amLib = amConf ->
      (forall st,
        st.(st_pl) = p' ->
        st.(st_AM_config) = amConf ->
        exists st', 
          build_cvm (copland_compile t) st = (resultC tt, st') \/
          build_cvm (copland_compile t) st = (errC (dispatch_error Runtime), st')
      )
    )
  ).
Proof.
  intros.
  pose proof (executable_impl_precond _ _ _ _ H _ _ H1); intuition.
  (* pose proof (manifest_generator_executability_static' t p backEnv).
  rewrite <- H in H0.
  pose proof (executable_impl_precond _ _ _ H4 _ _ H0); intuition. *)
  unfold lib_supports_manifest in *; intuition.
  assert (forall a : ASP_ID, In a (knowsOf_asps p p' t) -> exists cb : CakeML_ASPCallback CallBackErrors, map_get (Local_ASPS amLib) a = Some cb
  ); eauto.
  assert (forall up : Plc, In up (knowsOf_uuid' p p' t) -> exists b : UUID, map_get (Local_Plcs amLib) up = Some b); eauto.
  assert (forall u : Plc, In u (knowsOf_pubkey' p p' t) -> exists b : PublicKey, map_get (Local_PubKeys amLib) u = Some b); eauto.
  rewrite <- H in H1.
  generalizeEverythingElse t.
  induction t; intros.
  - admit.
    (*
    WORKS, BUT SLOW

    destruct a; 
    try (repeat monad_unfold; simpl in *; eauto; fail); (* NULL, CPY *)
    try (repeat (ff; simpl in *; intuition; eauto);
      unfolds; repeat (try break_match; try find_injection); eauto;
      try find_contradiction; try congruence; unfolds;
      repeat find_injection; simpl in *;
      match goal with
      | H:  context[ map_get (minify_mapC ?l ?filt) ?a],
        H1: forall a' : ASP_ID, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapC l filt) a = Some x)
        ;
        [
          eapply filter_resolver; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end). (* ASPC, SIG, HSH, ENC*)

      *)
  - simpl in *; break_if.
    * rewrite eqb_leibniz in *; rewrite Heqb in *; clear Heqb;
      unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *;
      pose proof (man_gen_map_getter t p p' (let
              '{|
                 my_abstract_plc := oldPlc;
                 asps := oldasps;
                 uuidPlcs := oldKnowsOf;
                 pubKeyPlcs := oldContext;
                 targetPlcs := oldTargets;
                 policy := oldPolicy
               |} := match map_get backEnv p' with
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
               |}) backEnv); simpl in *; intuition;
      destruct (H14); intuition; simpl in *; clear H14;
      find_rewrite; repeat find_injection; simpl in *;
      break_match; simpl in *; intuition; eauto;
      find_rewrite; unfold empty_Manifest in *; 
      repeat find_injection; simpl in *;
      ff; unfolds; simpl in *; eauto;
      repeat break_match; simpl in *; 
      repeat find_injection; repeat find_rewrite;
      repeat find_inversion; simpl in *; intuition; eauto; try congruence;
      unfold do_remote in *;
      repeat (break_match; simpl in *; intuition; eauto; try congruence);
      repeat find_injection; simpl in *; eauto;
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
    * (* p' : @ p0 t (generated from point of p) 
        p0 <> p' !
      *)
      assert (map_get (at_manifest_generator p0 p backEnv) p' = None). admit.
      pose proof (IHt _ _ _ H _ _ H14 H1 _ _ H3 _ H4 H5); intuition.
      destruct H16; intuition;
      unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *;
      ff; unfolds; simpl in *; eauto;
      repeat break_match; simpl in *; 
      repeat find_injection; repeat find_rewrite;
      repeat find_inversion; simpl in *; intuition; eauto; try congruence;
      unfold do_remote in *;
      repeat (break_match; simpl in *; intuition; eauto; try congruence);
      repeat find_injection; simpl in *; eauto; clear IHt;
      try (exfalso; clear H16;
      assert (p <> st_pl2); [ admit |
      pose proof (man_gen_subterm t _ _ _ absMan H H14); intuition;
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
      end]).
  - simpl in *.
    ff; 
    repeat (unfolds; simpl in *; repeat find_injection; simpl in *; intuition; eauto; try congruence);
    repeat break_match; simpl in *; subst;
    repeat find_injection.
    * destruct (manifest_generator' p t1 backEnv) eqn:E1;
      try (exfalso; eapply manifest_generator_never_empty; eauto; fail);
      destruct (map_get (p0 :: e) p') eqn:E2; 
      rewrite <- E1 in E2.
      ** pose proof (IHt1 _ _ _ E1 _ _ H0 E2).
         
      _ {|
                concMan :=
                  {|
                    my_plc := my_abstract_plc absMan;
                    Concrete_ASPs := asps absMan;
                    Concrete_Plcs := Local_Plcs;
                    Concrete_PubKeys := Local_PubKeys;
                    Concrete_Targets := targetPlcs absMan;
                    ASP_Server := ASPServer_Addr;
                    PubKey_Server := PubKeyServer_Addr;
                    Plc_Server := PlcServer_Addr;
                    UUID_Server := UUIDServer_Addr
                  |};
                aspCb :=
                  fun (par : ASP_PARAMS) (p : Plc) (bs : BS) (rawEv : RawEv) =>
                  let (aspid, _, _, _) := par in
                  match
                    map_get
                      (minify_mapC Local_ASPS
                         (fun x : ASP_ID => if in_dec (EqClass_impl_DecEq ASP_ID) x (asps absMan) then true else false)) aspid
                  with
                  | Some cb =>
                      match cb par p bs rawEv with
                      | errC c => match c with
                                  | messageLift _ => errC Runtime
                                  end
                      | resultC r => resultC r
                      end
                  | None => errC Unavailable
                  end;
                plcCb :=
                  fun p : Plc =>
                  match
                    map_get
                      (minify_mapD Local_Plcs
                         (fun x : Plc => if in_dec (EqClass_impl_DecEq Plc) x (uuidPlcs absMan) then true else false)) p
                  with
                  | Some uuid => resultC uuid
                  | None => errC Unavailable
                  end;
                pubKeyCb :=
                  fun p : Plc =>
                  match
                    map_get
                      (minify_mapD Local_PubKeys
                         (fun x : Plc => if in_dec (EqClass_impl_DecEq Plc) x (pubKeyPlcs absMan) then true else false)) p
                  with
                  | Some key => resultC key
                  | None => errC Unavailable
                  end;
                uuidCb :=
                  fun u : UUID => match mapD_get_key Local_Plcs u with
                                  | Some p => resultC p
                                  | None => errC Unavailable
                                  end
              |}).

    
    destruct (manifest_generator' p t1 backEnv) eqn:E1;
    try (exfalso; eapply manifest_generator_never_empty; eauto; fail).
    destruct (map_get (p0 :: e) p') eqn:E2. 
    rewrite <- E1 in E2.
    pose proof (IHt1 _ _ _ E1 _ m H0 E2 _ _ H3). _ H4 H5); intuition.
    pose proof (IHt1 _ _ _ H2 st H3); intuition.
    destruct H; intuition; 
    try (rewrite H0; eauto).
    assert (st_AM_config x = amConf). {
      destruct st; monad_unfold.
      pose proof (ac_immut (copland_compile t1) st_ev st_trace st_pl st_evid st_AM_config).
      monad_unfold.
      rewrite H0 in H.
      simpl in *; subst; eauto.
    }
    pose proof (IHt2 _ _ _ H2 x H); intuition.
    destruct H1; intuition; 
    try (rewrite H4; eauto).
  destruct s, s, s0; simpl in *; monad_unfold; intuition; eauto.
    * pose proof (IHt1 _ _ _ H2 {|
           st_ev := st_ev st;
           st_trace :=
             (st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil) ++
             cvm_thread_start 0 (st_pl st) (copland_compile t2) (get_et (st_ev st)) :: nil;
           st_pl := st_pl st;
           st_evid := st_evid st + 1;
           st_AM_config := st_AM_config st
         |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
    * pose proof (IHt1 _ _ _ H2 {|
                 st_ev := st_ev st;
                 st_trace :=
                   app (app (st_trace st) (cons (Term_Defs.split (st_evid st) (st_pl st)) nil))
                     (cons (cvm_thread_start 0 (st_pl st) (lseqc (aspc CLEAR) (copland_compile t2)) (get_et (st_ev st))) nil);
                 st_pl := st_pl st;
                 st_evid := Nat.add (st_evid st) 1;
                 st_AM_config := st_AM_config st
               |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
    * pose proof (IHt1 _ _ _ H2 {|
                  st_ev := mt_evc;
                  st_trace :=
                    app (app (st_trace st) (cons (Term_Defs.split (st_evid st) (st_pl st)) nil))
                      (cons (cvm_thread_start 0 (st_pl st) (copland_compile t2) (get_et (st_ev st))) nil);
                  st_pl := st_pl st;
                  st_evid := Nat.add (st_evid st) 1;
                  st_AM_config := st_AM_config st
                |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
    * pose proof (IHt1 _ _ _ H2 {|
                  st_ev := mt_evc;
                  st_trace :=
                    app (app (st_trace st) (cons (Term_Defs.split (st_evid st) (st_pl st)) nil))
                      (cons (cvm_thread_start 0 (st_pl st) (lseqc (aspc CLEAR) (copland_compile t2)) (get_et (st_ev st))) nil);
                  st_pl := st_pl st;
                  st_evid := Nat.add (st_evid st) 1;
                  st_AM_config := st_AM_config st
                |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
      ** exfalso. clear H16.
        assert (p <> st_pl2). admit.
        pose proof (man_gen_subterm t _ _ _ absMan H H14). intuition.
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
      ** exfalso; clear H16;
        assert (p <> st_pl2). admit.
        pose proof (man_gen_subterm t _ _ _ absMan H H14); intuition;
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
      ** exfalso; clear H16;
        assert (p <> st_pl2). admit.
        pose proof (man_gen_subterm t _ _ _ absMan H H14); intuition;
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
      ** exfalso; clear H16;
        assert (p <> st_pl2). admit.
        pose proof (man_gen_subterm t _ _ _ absMan H H14); intuition;
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
      
      


      ff; unfolds; simpl in *; eauto;
      repeat break_match; simpl in *; 
      repeat find_injection; repeat find_rewrite;
      repeat find_inversion; simpl in *; intuition; eauto; try congruence;
      unfold do_remote in *;
      repeat (break_match; simpl in *; intuition; eauto; try congruence);
      repeat find_injection; simpl in *; eauto.
      ** clear IHt. exfalso.
          pose proof (man_gen_map_getter).
        match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x)
        (* ;
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ] *)
        end.
        eapply filter_resolver_mapd; eauto. admit.
        repeat break_match; intuition.
        intuition.
        admit.


    
      assert (map_get (at_manifest_generator p0 p backEnv) p' = None). {
        unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *.
        pose proof (mapC_get_distinct_keys backEnv p0 ).
        admit.
      }
      pose proof (IHt _ _ _ H _ _ H14 H1 _ _ H3 _ H4 H5);
      intuition.
      destruct H16; intuition.
      ** 

      unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *.
      ff; unfolds; simpl in *; eauto;
      repeat break_match; simpl in *; 
      repeat find_injection; repeat find_rewrite;
      repeat find_inversion; simpl in *; intuition; eauto; try congruence;
      unfold do_remote in *;
      repeat (break_match; simpl in *; intuition; eauto; try congruence);
      repeat find_injection; simpl in *; eauto.
      *** 
          
          
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
      ** 
      pose proof (man_gen_map_getter t p p0 (let
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
               |}) backEnv); simpl in *; intuition;
      destruct (H14); intuition; simpl in *; clear H14;
      find_rewrite; repeat find_injection; simpl in *;
      break_match; simpl in *; intuition; eauto.
      repeat find_rewrite; simpl in *.
      
      find_rewrite; unfold empty_Manifest in *; 
      repeat find_injection; simpl in *;
      ff; unfolds; simpl in *; eauto;
      repeat break_match; simpl in *; 
      repeat find_injection; repeat find_rewrite;
      repeat find_inversion; simpl in *; intuition; eauto; try congruence;
      unfold do_remote in *;
      repeat (break_match; simpl in *; intuition; eauto; try congruence);
      repeat find_injection; simpl in *; eauto;
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


      admit. (* ISSUE< cannot satisfy below *)
      (* assert (map_get (at_manifest_generator p' p backEnv) p' = None). simpl in *. *)
    * 
      assert (map_get (at_manifest_generator p0 p backEnv) p' = None). simpl in *; 
      rewrite eqb_symm; rewrite Heqb; eauto. 
      pose proof (IHt p (at_manifest_generator p0 p backEnv) envM H p' _ H14 H1 _ _ H3 _ H4 H5);
      intuition.
      destruct H16; intuition; ff;
      repeat break_match; repeat find_injection; repeat find_inversion; eauto;
      try congruence.
      ** unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update, map_set in *;
          simpl in *.
      pose proof (man_gen_doesnt_kill_info t p (st_pl st)).
      pose proof (man_gen_doesnt_kill_info).
      ** unfolds; simpl in *.
        unfold do_remote in *. 
        repeat (repeat break_match; simpl in *; eauto;
        repeat find_injection; simpl in *; intuition; eauto; try congruence).
        match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x)
        (* ;
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ] *)
        end.
        *** eapply filter_resolver_mapd. eapply H2.

      destruct H16; intuition; monad_unfold; 
      unfold remote_session, doRemote_session', do_remote; simpl in *; eauto.
      (* assert (map_get (at_manifest_generator p0 p backEnv) p' = None); simpl in *; *)
    (* try (rewrite eqb_symm in Heqb; rewrite Heqb; eauto). *)
    (* break_if; simpl in *. *)
    pose proof (IHt p (at_manifest_generator (st_pl st) p backEnv)). envM H p' _ H14 H1 _ _ H3 _ H4); intuition.

    simpl in *; unfolds; intuition; eauto;
    repeat find_injection; simpl in *; monad_unfold; simpl in *; intuition; eauto;
    repeat monad_unfold; simpl in *; eauto.
    repeat break_if; try (rewrite eqb_leibniz in *; subst; simpl in *; eauto);
    try congruence;
    unfold remote_session in *; simpl in *; monad_unfold;
    repeat break_match; repeat find_injection; simpl in *; eauto;
    repeat break_match; repeat break_if;
    repeat find_injection; repeat find_inversion;
    repeat find_rewrite; simpl in *; eauto;
    try congruence;
    unfold doRemote_session' in *; repeat break_match;
    simpl in *; eauto; repeat monad_unfold;
    repeat break_match; simpl in *; repeat find_injection;
    repeat find_inversion; intuition; eauto; try congruence;
    unfold do_remote in *; simpl in *; repeat break_match;
    repeat find_injection; try congruence; eauto;
    try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
    end; fail).

    unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update, map_set in *;
    simpl in *; repeat break_match; simpl in *; subst; intuition; eauto.
    * destruct ((manifest_generator' p t
          ((p0,
            {|
              my_abstract_plc := my_abstract_plc;
              asps := asps;
              uuidPlcs := p :: uuidPlcs;
              pubKeyPlcs := pubKeyPlcs;
              targetPlcs := targetPlcs;
              policy := policy
            |}) :: backEnv))) eqn:E1;
      try (exfalso; eapply manifest_generator_never_empty; eauto; fail).
    pose proof (IHt _ _ _ E1).
    



    * repeat break_match.
      edestruct IHt; intuition; eauto;
    repeat break_match; repeat break_if;
    repeat find_injection; repeat find_inversion;
    repeat find_rewrite; simpl in *; eauto; 
    repeat (monad_unfold; unfolds; simpl in *; eauto; try congruence);
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto;
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto.
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence; eauto.
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence;
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.
    * edestruct IHt; intuition; eauto;
    repeat break_match; repeat break_if;
    repeat find_injection; repeat find_inversion;
    repeat find_rewrite; simpl in *; eauto; 
    repeat (monad_unfold; unfolds; simpl in *; eauto; try congruence);
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto;
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto.
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence; eauto.
      match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end. eapply H11; simpl in *.

      unfold knowsOf_uuid'.
      
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence;
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.

    * edestruct IHt; intuition; eauto;
    repeat break_match; repeat break_if;
    repeat find_injection; repeat find_inversion;
    repeat find_rewrite; simpl in *; eauto; 
    repeat (monad_unfold; unfolds; simpl in *; eauto; try congruence);
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto;
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto.
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence; eauto.
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence;
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.

    * admit.
    * (* SIG *)
      
      ** eapply filter_resolver; eauto.
        repeat break_match; intuition.
      ** rewrite Heqo0 in CO; destruct CO; congruence.
      ** find_injection.










  generalizeEverythingElse t.
  induction t; simpl in *; unfolds; intuition; eauto;
  repeat find_injection; simpl in *; monad_unfold; simpl in *; intuition; eauto;
  repeat monad_unfold; simpl in *; eauto.
  - destruct a; 
    try (repeat monad_unfold; simpl in *; eauto; fail). (* NULL, CPY *)
    * admit.
    * (* SIG *)
      break_if; try (rewrite eqb_leibniz in *; subst; eauto).
      ** (* p = p' *) admit.
      ** (* p <> p' *)
         assert (eqb p' p = false). admit.
         erewrite H in *; simpl in *; eauto.
      unfold asp_manifest_generator, asp_manifest_update, manifest_update_env, 
        map_set, aspid_manifest_update in *; simpl in *; subst; simpl in *;
      destruct st; simpl in *; try find_injection; subst.
      break_if; simpl in *; intuition; eauto.
      ** monad_unfold; repeat break_match; repeat find_injection; simpl in *; eauto.
  
  
  destruct a; 
    repeat (try break_if; try monad_unfold; try break_match; simpl in *; intuition; 
    repeat find_injection; repeat find_inversion; eauto; try congruence);
    destruct st, st_AM_config; simpl in *; find_injection; eauto;
    repeat break_match;
    try unfold sig_params in *; try unfold hsh_params in *; try unfold enc_params in *;
    simpl in *; repeat find_injection; repeat find_inversion; eauto; try congruence;
    try (rewrite eqb_leibniz in *; subst; simpl in *; intuition; eauto; try congruence);
    try (match goal with
      | H:  context[ map_get (minify_mapC ?l ?filt) ?a],
        H1: forall a' : ASP_ID, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapC l filt) a = Some x)
        ;
        [
          eapply filter_resolver; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
    end; fail).
  
  destruct a; 
    try (repeat monad_unfold; simpl in *; eauto; fail). (* NULL, CPY *)
    * admit.
    * (* SIG *)
      unfold asp_manifest_generator, asp_manifest_update, manifest_update_env, 
        map_set, aspid_manifest_update in *; simpl in *; subst; simpl in *;
      destruct st; simpl in *; try find_injection; subst.
      break_if; simpl in *; intuition; eauto.
      ** monad_unfold; repeat break_match; repeat find_injection; simpl in *; eauto.
          
      repeat (monad_unfold; break_match; try find_injection; simpl in *; eauto).
    destruct a; 
    repeat (try break_if; try monad_unfold; try break_match; simpl in *; intuition; 
    repeat find_injection; repeat find_inversion; eauto; try congruence);
    destruct st, st_AM_config; simpl in *; find_injection; eauto;
    repeat break_match;
    try unfold sig_params in *; try unfold hsh_params in *; try unfold enc_params in *;
    simpl in *; repeat find_injection; repeat find_inversion; eauto; try congruence;
    try (rewrite eqb_leibniz in *; subst; simpl in *; intuition; eauto; try congruence);
    try (match goal with
      | H:  context[ map_get (minify_mapC ?l ?filt) ?a],
        H1: forall a' : ASP_ID, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapC l filt) a = Some x)
        ;
        [
          eapply filter_resolver; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
    end; fail);
    try (rewrite eqb_refl in *; congruence).
    * 
  - repeat break_if; try (rewrite eqb_leibniz in *; subst; simpl in *; eauto);
    try congruence.
    * edestruct IHt; intuition; eauto;
    repeat break_match; repeat break_if;
    repeat find_injection; repeat find_inversion;
    repeat find_rewrite; simpl in *; eauto; 
    repeat (monad_unfold; unfolds; simpl in *; eauto; try congruence);
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto;
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto.
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence; eauto.
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence;
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.
    * edestruct IHt; intuition; eauto;
    repeat break_match; repeat break_if;
    repeat find_injection; repeat find_inversion;
    repeat find_rewrite; simpl in *; eauto; 
    repeat (monad_unfold; unfolds; simpl in *; eauto; try congruence);
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto;
    repeat find_injection; repeat find_inversion;
    repeat find_contradiction; repeat (try rewrite eqb_leibniz in *; subst; simpl in *);
    simpl in *; eauto.
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence; eauto.
      match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end. eapply H11; simpl in *.

      unfold knowsOf_uuid'.
      
    ** unfold remote_session in *; simpl in *; monad_unfold;
      repeat break_match; repeat break_if;
      repeat find_injection; repeat find_inversion;
      repeat find_rewrite; simpl in *; eauto;
      try congruence.
      unfold doRemote_session' in *; repeat break_match;
      simpl in *; eauto; repeat monad_unfold;
      repeat break_match; simpl in *; repeat find_injection;
      repeat find_inversion; intuition; eauto; try congruence.
      unfold do_remote in *; simpl in *; repeat break_match;
      repeat find_injection; try congruence;
      try (match goal with
      | H:  context[ map_get (minify_mapD ?l ?filt) ?a],
        H1: forall a' : Plc, _ -> (exists x : _, map_get _ _ = Some x) |- _ => 
        assert (CO : exists x, map_get (minify_mapD l filt) a = Some x);
        [
          eapply filter_resolver_mapd; eauto;
          repeat break_match; intuition; try congruence
          | 
          rewrite H in CO; destruct CO; congruence
        ]
      end); eauto.
  - pose proof (IHt1 _ _ _ H2 st H3); intuition.
    destruct H; intuition; 
    try (rewrite H0; eauto).
    assert (st_AM_config x = amConf). {
      destruct st; monad_unfold.
      pose proof (ac_immut (copland_compile t1) st_ev st_trace st_pl st_evid st_AM_config).
      monad_unfold.
      rewrite H0 in H.
      simpl in *; subst; eauto.
    }
    pose proof (IHt2 _ _ _ H2 x H); intuition.
    destruct H1; intuition; 
    try (rewrite H4; eauto).
  - destruct s, s, s0; simpl in *; monad_unfold; intuition; eauto.
    * pose proof (IHt1 _ _ _ H2 {|
          st_ev := st_ev st;
          st_trace := st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil;
          st_pl := st_pl st;
          st_evid := st_evid st + 1;
          st_AM_config := st_AM_config st
        |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
      assert (st_AM_config x = amConf). {
      destruct st; monad_unfold.
      pose proof (ac_immut (copland_compile t1) st_ev (st_trace ++ Term_Defs.split st_evid st_pl :: nil) 
        st_pl (st_evid + 1) st_AM_config).
      monad_unfold.
      rewrite H0 in H.
      simpl in *; subst; eauto.
      }
      pose proof (IHt2 _ _ _ H2 {|
              st_ev := st_ev st; st_trace := st_trace x; st_pl := st_pl x; st_evid := st_evid x; st_AM_config := st_AM_config x
            |} H); intuition.
      destruct H1; intuition; 
      try (rewrite H4; eauto).
    * pose proof (IHt1 _ _ _ H2 {| 
            st_ev := st_ev st;
            st_trace := st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil;
            st_pl := st_pl st;
            st_evid := st_evid st + 1;
            st_AM_config := st_AM_config st
          |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto);
      assert (st_AM_config x = amConf). {
        destruct st; monad_unfold;
        pose proof (ac_immut (copland_compile t1) st_ev (st_trace ++ Term_Defs.split st_evid st_pl :: nil) 
          st_pl (st_evid + 1) st_AM_config);
        monad_unfold;
        rewrite H0 in H;
        simpl in *; subst; eauto.
      }
      pose proof (IHt2 _ _ _ H2 {|
                st_ev := mt_evc; st_trace := st_trace x; st_pl := st_pl x; st_evid := st_evid x; st_AM_config := st_AM_config x
              |} H); intuition;
      destruct H1; intuition; 
      try (rewrite H4; eauto).
    * pose proof (IHt1 _ _ _ H2 {| 
            st_ev := mt_evc;
            st_trace := st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil;
            st_pl := st_pl st;
            st_evid := st_evid st + 1;
            st_AM_config := st_AM_config st
          |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto);
      assert (st_AM_config x = amConf). {
        destruct st; monad_unfold;
        pose proof (ac_immut (copland_compile t1) mt_evc (st_trace ++ Term_Defs.split st_evid st_pl :: nil) 
          st_pl (st_evid + 1) st_AM_config);
        monad_unfold;
        rewrite H0 in H;
        simpl in *; subst; eauto.
      }
      pose proof (IHt2 _ _ _ H2 {|
                st_ev := st_ev st; st_trace := st_trace x; st_pl := st_pl x; st_evid := st_evid x; st_AM_config := st_AM_config x
              |} H); intuition;
      destruct H1; intuition; 
      try (rewrite H4; eauto).
    * pose proof (IHt1 _ _ _ H2 {| 
            st_ev := mt_evc ;
            st_trace := st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil;
            st_pl := st_pl st;
            st_evid := st_evid st + 1;
            st_AM_config := st_AM_config st
          |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto);
      assert (st_AM_config x = amConf). {
        destruct st; monad_unfold;
        pose proof (ac_immut (copland_compile t1) mt_evc (st_trace ++ Term_Defs.split st_evid st_pl :: nil) 
          st_pl (st_evid + 1) st_AM_config);
        monad_unfold;
        rewrite H0 in H;
        simpl in *; subst; eauto.
      }
      pose proof (IHt2 _ _ _ H2 {|
                st_ev := mt_evc; st_trace := st_trace x; st_pl := st_pl x; st_evid := st_evid x; st_AM_config := st_AM_config x
              |} H); intuition;
      destruct H1; intuition; 
      try (rewrite H4; eauto).
  - destruct s, s, s0; simpl in *; monad_unfold; intuition; eauto.
    * pose proof (IHt1 _ _ _ H2 {|
           st_ev := st_ev st;
           st_trace :=
             (st_trace st ++ Term_Defs.split (st_evid st) (st_pl st) :: nil) ++
             cvm_thread_start 0 (st_pl st) (copland_compile t2) (get_et (st_ev st)) :: nil;
           st_pl := st_pl st;
           st_evid := st_evid st + 1;
           st_AM_config := st_AM_config st
         |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
    * pose proof (IHt1 _ _ _ H2 {|
                 st_ev := st_ev st;
                 st_trace :=
                   app (app (st_trace st) (cons (Term_Defs.split (st_evid st) (st_pl st)) nil))
                     (cons (cvm_thread_start 0 (st_pl st) (lseqc (aspc CLEAR) (copland_compile t2)) (get_et (st_ev st))) nil);
                 st_pl := st_pl st;
                 st_evid := Nat.add (st_evid st) 1;
                 st_AM_config := st_AM_config st
               |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
    * pose proof (IHt1 _ _ _ H2 {|
                  st_ev := mt_evc;
                  st_trace :=
                    app (app (st_trace st) (cons (Term_Defs.split (st_evid st) (st_pl st)) nil))
                      (cons (cvm_thread_start 0 (st_pl st) (copland_compile t2) (get_et (st_ev st))) nil);
                  st_pl := st_pl st;
                  st_evid := Nat.add (st_evid st) 1;
                  st_AM_config := st_AM_config st
                |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
    * pose proof (IHt1 _ _ _ H2 {|
                  st_ev := mt_evc;
                  st_trace :=
                    app (app (st_trace st) (cons (Term_Defs.split (st_evid st) (st_pl st)) nil))
                      (cons (cvm_thread_start 0 (st_pl st) (lseqc (aspc CLEAR) (copland_compile t2)) (get_et (st_ev st))) nil);
                  st_pl := st_pl st;
                  st_evid := Nat.add (st_evid st) 1;
                  st_AM_config := st_AM_config st
                |}); intuition;
      destruct H0; intuition;
      try (rewrite H0; eauto).
Qed.

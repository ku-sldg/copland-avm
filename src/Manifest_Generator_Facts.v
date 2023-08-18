Require Import Maps Term_Defs_Core Manifest Eqb_Evidence
Executable_Facts EqClass
  Manifest_Generator Executable_Defs_Prop.

Require Import Auto.

Require Import StructTactics.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)

Fixpoint place_terms (t:Term) (tp:Plc) (p:Plc) : list Term := 
  if(eqb_plc tp p)
  then [t]
  else (
    match t with 
    | asp a => []
    | att q t' => place_terms t' q p (* if (eqb_plc p q) then ([t'] ++ (place_terms t' q p)) else (place_terms t' q p) *)
    | lseq t1 t2 => (place_terms t1 tp p) ++ (place_terms t2 tp p)
    | bseq _ t1 t2 => (place_terms t1 tp p) ++ (place_terms t2 tp p)
    | bpar _ t1 t2 => (place_terms t1 tp p) ++ (place_terms t2 tp p)
    end).


Definition distributed_executability 
    (t:Term) (tp:Plc) (env_map:EnvironmentM) : Prop := 
    forall p t', 
      In p (places tp t) /\ 
      In t' (place_terms t tp p) ->
      (exists (m:Manifest),
        Maps.map_get env_map p = Some m /\
        executable_local t' m).


Definition manifest_subset (m1:Manifest) (m2:Manifest) : Prop :=
  (forall i, In i (asps m1) -> In i (asps m2)) /\
  (forall p, In p (uuidPlcs m1) -> In p (uuidPlcs m2)) /\
  (forall q, In q (pubKeyPlcs m1) -> In q (pubKeyPlcs m2)) /\
  (forall p, In p (targetPlcs m1) -> In p (targetPlcs m2)).

Definition Environment_subset (e1:EnvironmentM) (e2:EnvironmentM) : Prop := 
  forall m1 p, 
  Maps.map_get e1 p = Some m1 -> 

  (exists m2, 
    Maps.map_get e2 p = Some m2 /\
    manifest_subset m1 m2
  ).

Lemma manifest_subset_refl : forall m,
  manifest_subset m m.
Proof.
  intros.
  unfold manifest_subset; intros.
  split; intros; ff.
Qed.

Lemma manifest_subset_trans : forall m1 m2 m3,
  manifest_subset m1 m2 ->
  manifest_subset m2 m3 ->
  manifest_subset m1 m3.
Proof.
  intros; unfold manifest_subset in *; intuition.
Qed.

Lemma env_subset_refl : forall e, 
  Environment_subset e e.
Proof.
  intros.
  unfold Environment_subset; intros.
  exists m1.
  split; ff.
  
  apply manifest_subset_refl.
Qed.


Lemma env_subset_trans : forall e1 e2 e3,
  Environment_subset e1 e2 ->
  Environment_subset e2 e3 -> 
  Environment_subset e1 e3.
Proof.
  intros.
  unfold Environment_subset in *; intros.
  specialize H with (m1:= m1) (p:=p).
  apply H in H1.
  destruct_conjs.

  specialize H0 with (m1 := H1) (p:= p).
  apply H0 in H2.
  destruct_conjs.
  eexists.
  split; eauto.
  eapply manifest_subset_trans; eauto.
Qed.

Lemma plc_ne{A:Type} `{H : EqClass A} : forall (p1 p2:A),
p1 <> p2 -> 
eqb p1 p2 = false.
Proof.
  intros.
  unfold not in *.
  destruct (eqb p1 p2) eqn:hi.
  ++
  assert False.
  {
    apply H0.
    apply eqb_leibniz.
    eauto.
  }
  solve_by_inversion.
  ++
  eauto.
Qed.

Lemma env_subset_set_man : forall e p m1 m2,
map_get e p = Some m1 ->
manifest_subset m1 m2 ->
Environment_subset e (map_set e p m2).
Proof.
  induction e; simpl in *; intuition; eauto; try congruence;
  ff; repeat (rewrite eqb_leibniz in *); subst.
  - unfold Environment_subset; intuition; simpl in *;
    ff; eauto.
    exists m0; intuition; eauto; eapply manifest_subset_refl.
  - unfold Environment_subset; intuition; simpl in *;
    ff; eauto.
    * exists m0; intuition; eauto; eapply manifest_subset_refl.
    * destruct (eqb p p0) eqn:E.
      ** rewrite eqb_leibniz in *; subst.
          rewrite mapC_get_works; exists m2; intuition; eauto.
          find_rewrite; find_injection; eauto.
      ** 
        assert (p <> p0). intros HC. rewrite <- eqb_leibniz in HC; congruence.
          pose proof (mapC_get_distinct_keys e p p0 m2 m0 H2 H1).
          rewrite H3; eexists; intuition; eauto.
          eapply manifest_subset_refl.
Qed.

Lemma env_subset_set : forall e p m,
map_get e p = Some m ->
Environment_subset e (map_set e p m).
Proof.
  intros.
  apply env_subset_set_man with (m1:=m).
  -
    eassumption.
  -
    apply manifest_subset_refl.
Qed. 

Lemma env_subset_set_none : forall e p m,
map_get e p = None ->
Environment_subset e (map_set e p m).
Proof.
  intros.
  unfold Environment_subset; intros.
  assert (p <> p0).
  {
    unfold not; intros.
    subst.
    find_rewrite.
    solve_by_inversion.
  }
  exists m1.
  split.
  +
    apply mapC_get_distinct_keys; eauto.
  +
    apply manifest_subset_refl.
Qed.

Lemma manifest_generator_cumul : forall t p e1 e2,
    Environment_subset e1 e2 ->
    Environment_subset e1 (manifest_generator' p t e2).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ff.
  - (* asp case *)
    unfold asp_manifest_generator, manifest_update_env, asp_manifest_update, aspid_manifest_update;
    simpl in *; unfold Environment_subset, manifest_subset in *; intuition.
    destruct (H _ _ H0); intuition;
    destruct (eqb p0 p) eqn:E.
    * rewrite eqb_leibniz in *; subst;
      rewrite H2 in *; simpl in *; destruct x; simpl in *.
      rewrite mapC_get_works; eexists; intuition; eauto;
      destruct a; simpl in *; eauto;
      destruct a; simpl in *; eauto.
    * assert (p <> p0). intros HC. rewrite <- eqb_leibniz in HC. 
      rewrite eqb_symm in HC; congruence.
      erewrite (mapC_get_distinct_keys e2 p p0 _ _ H5 H2); eexists; intuition; eauto.

  - (* at case *)
    eapply IHt; clear IHt; unfold Environment_subset in *; intuition.
    unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update; 
    simpl in *;
    destruct (H _ _ H0); intuition; clear H H0; unfold manifest_subset in *; intuition; eauto.
    destruct (eqb p0 p1) eqn:E.
    * rewrite eqb_leibniz in *; subst.
      rewrite H2; destruct x. rewrite mapC_get_works;
      eexists; intuition; eauto; simpl in *; eauto.
    * erewrite mapC_get_distinct_keys; eauto.
      eexists; intuition; simpl in *; eauto.
      intros HC. rewrite <- eqb_leibniz in HC; congruence.

  - (* lseq case *)
    eauto.
  -
    eauto.
  -
    eauto.
Qed.

Lemma manifest_generator_cumul' : forall t p e,
  Environment_subset e (manifest_generator' p t e).
Proof.
  intros.
  apply manifest_generator_cumul.
  apply env_subset_refl.
Qed.

Lemma exec_static_cumul : forall t p e1 e2,
  executable_global t p e1 -> 
  Environment_subset e1 e2 -> 
  executable_global t p e2.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* asp case *)
  destruct a; ff.
  +
    destruct_conjs.
    unfold Environment_subset in *.
    specialize H0 with (m1:=H) (p:=p).
    apply H0 in H1.
    destruct_conjs.
    eauto.
  + destruct_conjs.
  unfold Environment_subset in *.
  specialize H0 with (m1:=H) (p:=p).
  apply H0 in H1.
  destruct_conjs.
  eauto.
  + unfold canRunAsp_Env in *; simpl in *.
    ff.
    ++
    unfold Environment_subset in *; ff.
    specialize H0 with (m1:=m0) (p:=p).
    apply H0 in Heqo0.
    destruct_conjs.
    find_rewrite.
    ff.
    unfold manifest_subset in *; ff.
    unfold canRunAsp_Manifest in *; ff;
      destruct_conjs; ff; subst.
    ++
    unfold Environment_subset in *; ff.
    specialize H0 with (m1:=m) (p:=p).
    apply H0 in Heqo0.
    destruct_conjs.
    find_rewrite.
    solve_by_inversion.
  + (* SIG case *)
  unfold Environment_subset in *; ff.
  unfold canRun_aspid_Env in *; ff.
  unfold canRun_aspid in *; ff.
  specialize H0 with (m1:=m0) (p:=p).
  apply H0 in Heqo0.
  destruct_conjs.
  find_rewrite.
  ff.
  unfold manifest_subset in *; ff.

  unfold Environment_subset in *; ff.
  specialize H0 with (m1:=m) (p:=p).
  apply H0 in Heqo0.
  destruct_conjs.
  find_rewrite.
  solve_by_inversion.
  + (* HSH case *)
  unfold Environment_subset in *; ff.
  unfold canRun_aspid_Env in *; ff.
  unfold canRun_aspid in *; ff.
  specialize H0 with (m1:=m0) (p:=p).
  apply H0 in Heqo0.
  destruct_conjs.
  find_rewrite.
  ff.
  unfold manifest_subset in *; ff.

  unfold Environment_subset in *; ff.
  specialize H0 with (m1:=m) (p:=p).
  apply H0 in Heqo0.
  destruct_conjs.
  find_rewrite.
  solve_by_inversion.
  
  + (* ENC case *)
  unfold Environment_subset in *; ff.
  unfold knowsPub_Env in *; ff.
  specialize H0 with (m1:=m0) (p:=p).
  apply H0 in Heqo0.
  destruct_conjs.
  find_rewrite.
  ff.
  unfold manifest_subset in *; ff.

  destruct_conjs.
  eauto.

  unfold Environment_subset in *; ff.
  specialize H0 with (m1:=m) (p:=p).
  apply H0 in Heqo0.
  destruct_conjs.
  find_rewrite.
  solve_by_inversion. 

- (* at case *)
  destruct_conjs.
  ff.
  destruct_conjs.
  split.
  +
    unfold knowsOf_Env in *; ff.
    ++
      unfold Environment_subset in *; ff.
      specialize H0 with (m1:=m0) (p:=p0).
      apply H0 in Heqo0.
      destruct_conjs.
      find_rewrite.
      ff.
      unfold manifest_subset in H3.
      destruct_conjs.
      apply H4.
      eassumption.
    ++
    unfold Environment_subset in *; ff.
    specialize H0 with (m1:=m) (p:=p0).
    apply H0 in Heqo0.
    destruct_conjs.
    find_rewrite.
    solve_by_inversion.
  +
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


Lemma env_subset_plc_manifest_gen: forall e1 e2 p0 p,
Environment_subset e1 e2 ->
Environment_subset 
  (at_manifest_generator p0 p e1) 
  (at_manifest_generator p0 p e2).
Proof.
  unfold Environment_subset, manifest_subset, at_manifest_generator,
    knowsof_manifest_update, manifest_update_env, empty_Manifest in *; 
  simpl in *; intuition.
  destruct (eqb p0 p1) eqn:E.
  - rewrite eqb_leibniz in *; subst;
    rewrite mapC_get_works in *; ff;
    try (eexists; simpl in *; intuition; simpl in *; eauto; fail);
    destruct (H _ _ Heqo0); simpl in *; intuition; eauto.
    * find_rewrite; find_injection;
      eexists; simpl in *; intuition; simpl in *; eauto.
    * find_rewrite; congruence.
  - ff; subst; simpl in *;
    try (eexists; simpl in *; intuition; simpl in *; eauto; fail);
    assert (p0 <> p1) by (intros HC; rewrite <- eqb_leibniz in HC; congruence);
    assert (map_get e1 p1 = Some m1) by (eapply mapC_get_distinct_keys_from_set; eauto); 
    destruct (H _ _ H2); intuition; eauto;
    erewrite mapC_get_distinct_keys; eauto;
    eexists; simpl in *; intuition; simpl in *; eauto.
Qed.

Local Hint Resolve env_subset_plc_manifest_gen : core.

Lemma empty_manifest_always_sub: forall m,
manifest_subset empty_Manifest m.
Proof.
intros;
unfold empty_Manifest; unfold manifest_subset; intros; 
intuition; try solve_by_inversion.
Qed.

Local Hint Resolve empty_manifest_always_sub : core.

Lemma fafafa : forall t p e1 e2,
    Environment_subset e1 e2 ->
    Environment_subset (manifest_generator' p t e1)
                       (manifest_generator' p t e2).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; eauto.
  - (* asp case *)
    destruct a; ff;
    unfold asp_manifest_generator, manifest_update_env, asp_manifest_update,
      aspid_manifest_update, update_manifest_policy_targ, Environment_subset, 
      empty_Manifest, pubkey_manifest_update in *; ff;
    simpl in *; intuition; eauto;
    try match goal with 
    | H1 : map_get e1 ?p1 = _,
      H2 : map_get (map_set e1 ?p1 _) ?p2 = Some ?m2 |- _ =>
        destruct (eqb p1 p2) eqn:E;
        [
          rewrite eqb_leibniz in *; subst;
          try (destruct (H _ _ H1); intuition; eauto);
          unfold manifest_subset in *; simpl in *;
          rewrite mapC_get_works in *;
          repeat find_rewrite; repeat find_injection; simpl in *; eauto;
          eexists; simpl in *; intuition; simpl in *; eauto; try congruence
        |
        assert (p1 <> p2) by (intros HC; rewrite <- eqb_leibniz in HC; congruence);
        assert (HM : map_get e1 p2 = Some m2) by (eapply mapC_get_distinct_keys_from_set; eauto);
        destruct (H _ _ HM); intuition; eauto;
        erewrite mapC_get_distinct_keys; eauto
        ]; fail
    end.
Qed.

Lemma map_get_mangen : forall t e p p' v,
map_get e p = Some v ->
exists v',
map_get (manifest_generator' p' t e) p = Some v'.
Proof.
  intros.
  assert (Environment_subset e (manifest_generator' p' t e)).
  {
    apply manifest_generator_cumul.
    apply env_subset_refl.
  }

  unfold Environment_subset in H0.
  specialize H0 with (m1:=v) (p:=p).
  apply H0 in H.
  destruct_conjs.
  eexists.
  apply H1.
  Qed.


Lemma afafa : forall e p t p0 m m',
map_get (manifest_generator' p t e) p0 = Some m -> 
e = [(p0, m')] ->
manifest_subset m' m.
Proof.
  intros.
  subst.

  assert (
    Environment_subset 
      [(p0, m')] 
      (manifest_generator' p t [(p0, m')])
  ).
  {
    apply manifest_generator_cumul.
    apply env_subset_refl.
  }

  unfold Environment_subset in H0.
  specialize H0 with (m1:=m') (p:=p0).
  assert (map_get [(p0, m')] p0 = Some m').
  {
    simpl in *; rewrite eqb_refl; eauto.
  }
  apply H0 in H1.
  destruct_conjs.
  rewrite H2 in *.
  ff.
Qed.

Theorem manifest_generator_executability_static :
    forall (t:Term) (p:Plc), 
        executable_global t p (manifest_generator t p).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; eauto.
  - (* asp case *)
    destruct a; 
    try (simpl in *; trivial).
    +
      eexists.
      rewrite eqb_plc_refl.
      eauto. 

    + eexists.
    rewrite eqb_plc_refl.
    eauto. 
    +
      destruct a.
      cbv.
      ff.
      assert (eqb p p = true).
      {
        rewrite eqb_leibniz.
        auto.
      }
      find_rewrite.
      solve_by_inversion.
    +
    cbv.
    ff.
    assert (eqb p p = true).
    {
      rewrite eqb_leibniz.
      auto.
    }
    find_rewrite.
    solve_by_inversion.
    +
    cbv.
    ff.
    assert (eqb p p = true).
    {
      rewrite eqb_leibniz.
      auto.
    }
    find_rewrite.
    solve_by_inversion.
    +
    cbv.
    ff.
    assert (eqb p p = true).
    {
      rewrite eqb_leibniz.
      auto.
    }
    find_rewrite.
    solve_by_inversion.

  - (* at case *)

    unfold manifest_generator in *.
    cbn.
    intros.
    unfold knowsOf_Env in *.
    ff; eauto.
    2: {

    assert (
      exists v,
      
    map_get
    (manifest_generator' p t
       (map_set e_empty p0
          {|
            my_abstract_plc :=
              Manifest_Admits.empty_Manifest_Plc;
            asps := [];
            uuidPlcs := [p];
            pubKeyPlcs := [];
            targetPlcs := [];
            policy := Manifest_Admits.empty_PolicyT
          |})) p0 = Some v).
          {

            assert ( exists v,
              map_get (map_set e_empty p0
               {|
                 my_abstract_plc :=
                   Manifest_Admits.empty_Manifest_Plc;
                 asps := [];
                 uuidPlcs := [p];
                 pubKeyPlcs := [];
                 targetPlcs := [];
                 policy := Manifest_Admits.empty_PolicyT
               |}) p0 = Some v).
               {
                eexists.
                apply mapC_get_works.
               }
               destruct_conjs.

               eapply map_get_mangen.
               eassumption.
          }

          destruct_conjs.
          ff.
          find_rewrite; congruence.
    }

    split.
    +
    ff.
    unfold e_empty in *.
    unfold map_set in *.
    ff.

  assert (manifest_subset 
    {|
                my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
                asps := [];
                uuidPlcs := [p];
                pubKeyPlcs := [];
                targetPlcs := [];
                policy := Manifest_Admits.empty_PolicyT
              |}

              m).
      {

      assert (
      Environment_subset 

      ([(p0,
      {|
        my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
        asps := [];
        uuidPlcs := [p];
        pubKeyPlcs := [];
        targetPlcs := [];
        policy := Manifest_Admits.empty_PolicyT
      |})])

      (manifest_generator' p t
            [(p0,
              {|
                my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
                asps := [];
                uuidPlcs := [p];
                pubKeyPlcs := [];
                targetPlcs := [];
                policy := Manifest_Admits.empty_PolicyT
              |})]) 


      ).
      {
        apply manifest_generator_cumul.
        apply env_subset_refl.
      }

      eapply afafa.
      apply Heqo.
      reflexivity.

      }
      unfold manifest_subset in H; ff.
      destruct_conjs.
      apply H0.
      left; eauto.
    +
    assert (executable_global t p (manifest_generator' p t e_empty)).
    { eauto. }

  eapply exec_static_cumul.
  eassumption.

  apply fafafa.

  unfold Environment_subset; intros.
  exists m1.
  ff.


  - (* lseq case *)
    unfold manifest_generator in *.
    ff.
    split.
    +
    eapply exec_static_cumul.
    apply IHt1.
    apply manifest_generator_cumul.
    apply env_subset_refl.
    +
    eapply exec_static_cumul.
    apply IHt2.
    apply fafafa.
    apply manifest_generator_cumul.
    apply env_subset_refl.


  - (* bseq case *)
    unfold manifest_generator in *.
    ff.
    split.
    +
    eapply exec_static_cumul.
    apply IHt1.
    apply manifest_generator_cumul.
    apply env_subset_refl.
    +
    eapply exec_static_cumul.
    apply IHt2.
    apply fafafa.
    apply manifest_generator_cumul.
    apply env_subset_refl.

  - (* bpar case *)
    unfold manifest_generator in *.
    ff.
    split.
    +
    eapply exec_static_cumul.
    apply IHt1.
    apply manifest_generator_cumul.
    apply env_subset_refl.
    +
    eapply exec_static_cumul.
    apply IHt2.
    apply fafafa.
    apply manifest_generator_cumul.
    apply env_subset_refl.  
Qed.

Lemma man_gen_map_getter' : forall t u preEnv p st postEnv,
  map_get preEnv p = None ->
  exists st', 
    (map_get (manifest_generator' u t (preEnv ++ (p, st) :: postEnv)) p = Some st') /\
    (forall x, In x st.(uuidPlcs) -> In x st'.(uuidPlcs)) /\
    (forall x, In x st.(asps) -> In x st'.(asps)) /\
    (forall x, In x st.(pubKeyPlcs) -> In x st'.(pubKeyPlcs)).
Proof.
  intros.
  pose proof (manifest_generator_cumul' t u (preEnv ++ (p,st) :: postEnv)).
  unfold Environment_subset in *.
  pose proof (H0 st p). clear H0.
  assert (map_get (preEnv ++ (p, st) :: postEnv) p = Some st). {
    clear H1.
    induction preEnv; simpl in *; eauto.
    - rewrite eqb_refl; eauto.
    - repeat break_match; try congruence; eauto.
  }
  intuition; clear H0.
  destruct H2; intuition.
  exists x; intuition; eauto;
  unfold manifest_subset in *; simpl in *; intuition; eauto.
Qed.

Local Hint Resolve man_gen_map_getter' : core.

Lemma man_gen_map_getter : forall t u p st stEnv,
  exists st', 
    (map_get (manifest_generator' u t (map_set stEnv p st)) p = Some st') /\
    (forall x, In x st.(uuidPlcs) -> In x st'.(uuidPlcs)) /\
    (forall x, In x st.(asps) -> In x st'.(asps)) /\
    (forall x, In x st.(pubKeyPlcs) -> In x st'.(pubKeyPlcs)).
Proof.
  intuition;
  destruct (map_set_sandwiched stEnv p st) as [preM [postM H]];
  intuition; find_rewrite; eauto.
Qed.

Lemma man_gen_self_map_getter : forall t u p st backEnv,
  map_get backEnv p = Some st ->
  exists st', 
    (map_get (manifest_generator' u t backEnv) p = Some st') /\
    (forall x, In x st.(uuidPlcs) -> In x st'.(uuidPlcs)) /\
    (forall x, In x st.(asps) -> In x st'.(asps)) /\
    (forall x, In x st.(pubKeyPlcs) -> In x st'.(pubKeyPlcs)).
Proof.
  induction t; simpl in *; intuition; eauto.
  - unfold asp_manifest_generator, manifest_update_env, asp_manifest_update,
      aspid_manifest_update, update_manifest_policy_targ, pubkey_manifest_update in *;
    simpl in *;
    repeat break_match; destruct (eqb u p) eqn:E;
    try rewrite eqb_leibniz in *; subst;
    repeat find_rewrite; repeat find_injection; try congruence; eauto;
    try (rewrite mapC_get_works; eexists; intuition; simpl in *; intuition; eauto; congruence);
    try (match goal with
    | H1 : eqb ?x ?y = false |- _ =>
        assert (x <> y) by (intros HC; rewrite <- eqb_leibniz in *; congruence)
    end); try (erewrite mapC_get_distinct_keys; eauto; fail).
  - unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update in *;
    simpl in *; repeat break_match.
    * destruct (eqb u p0) eqn:E.
      ** rewrite eqb_leibniz in *; subst.
        pose proof (man_gen_map_getter t p p0 {|
            my_abstract_plc := my_abstract_plc;
            asps := asps;
            uuidPlcs := p :: uuidPlcs;
            pubKeyPlcs := pubKeyPlcs;
            targetPlcs := targetPlcs;
            policy := policy
          |} backEnv). simpl in *.
        destruct H0; intuition; eauto.
        repeat find_rewrite; repeat find_injection; simpl in *;
        exists x; intuition; eauto.
      ** subst. eapply IHt; eauto.
          eapply mapC_get_distinct_keys; eauto.
          match goal with
          | H1 : eqb ?x ?y = false |- _ =>
              assert (x <> y) by (intros HC; rewrite <- eqb_leibniz in *; congruence)
          end; eauto.
    * unfold empty_Manifest in *; find_injection.
      destruct (eqb u p0) eqn:E.
      ** rewrite eqb_leibniz in *; subst.
        pose proof (man_gen_map_getter t p p0 {|
            my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
            asps := [];
            uuidPlcs := [p];
            pubKeyPlcs := [];
            targetPlcs := [];
            policy := Manifest_Admits.empty_PolicyT
          |} backEnv). simpl in *.
        destruct H0; intuition; eauto.
        repeat find_rewrite; repeat find_injection; simpl in *;
        exists x; intuition; eauto; try congruence.
      ** subst. eapply IHt; eauto.
          eapply mapC_get_distinct_keys; eauto.
          match goal with
          | H1 : eqb ?x ?y = false |- _ =>
              assert (x <> y) by (intros HC; rewrite <- eqb_leibniz in *; congruence)
          end; eauto.
  - pose proof (IHt1 u _ _ _ H);
    destruct H0; intuition;
    pose proof (IHt2 u _ _ _ H1);
    destruct H3; intuition;
    exists x0; intuition; eauto.
  - pose proof (IHt1 u _ _ _ H);
    destruct H0; intuition;
    pose proof (IHt2 u _ _ _ H1);
    destruct H3; intuition;
    exists x0; intuition; eauto.
  - pose proof (IHt1 u _ _ _ H);
    destruct H0; intuition;
    pose proof (IHt2 u _ _ _ H1);
    destruct H3; intuition;
    exists x0; intuition; eauto.
Qed.

Theorem manifest_generator_executability_static' :
    forall (t:Term) (p:Plc) stEnv, 
        executable_global t p (manifest_generator' p t stEnv).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; simpl in *; intuition; eauto.
  - (* asp case *)
    repeat unfold canRun_aspid_Env, knowsPub_Env, asp_manifest_generator,
      canRunAsp_Env, manifest_update_env, asp_manifest_update,
      aspid_manifest_update, update_manifest_policy_targ, canRunAsp_Manifest,
      canRun_aspid, can_measure_target_prop, pubkey_manifest_update in *;
    simpl in *; repeat rewrite mapC_get_works in *; simpl in *;
    repeat break_match; simpl in *; subst;
    repeat find_injection; try congruence; eauto with *.
  - (* at case *)
    repeat unfold knowsOf_Env, at_manifest_generator, 
      manifest_update_env, knowsof_manifest_update in *;
    simpl in *.
    destruct (man_gen_map_getter t p p0 (let
      '{|
        my_abstract_plc := oldPlc;
        asps := oldasps;
        uuidPlcs := oldKnowsOf;
        pubKeyPlcs := oldContext;
        targetPlcs := oldTargets;
        policy := oldPolicy
      |} := match map_get stEnv p0 with
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
      |}) stEnv); simpl in *; intuition.
    rewrite H0; eapply H;
    break_match; simpl in *; eauto.

  - (* lseq case *)
    eapply exec_static_cumul; eauto;
    eapply manifest_generator_cumul;
    eapply env_subset_refl.

  - (* bseq case *)
    eapply exec_static_cumul; eauto;
    eapply manifest_generator_cumul;
    eapply env_subset_refl.

  - (* bpar case *)
    eapply exec_static_cumul; eauto;
    eapply manifest_generator_cumul;
    eapply env_subset_refl.
Qed.
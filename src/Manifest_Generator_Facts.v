Require Import Maps Term_Defs_Core Manifest Eqb_Evidence
Executable_Facts
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

Lemma plc_ne{A:Type} `{H : EqClass.EqClass A} : forall (p1 p2:A),
p1 <> p2 -> 
EqClass.eqb p1 p2 = false.
Proof.
  intros.
  unfold not in *.
  destruct (EqClass.eqb p1 p2) eqn:hi.
  ++
  assert False.
  {
    apply H0.
    apply EqClass.eqb_leibniz.
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
  intros.
  unfold Environment_subset; intros.
  destruct (eq_plc_dec p0 p).
  +
    ff.
    subst.
    repeat find_rewrite.
    invc H1.
    assert (EqClass.eqb p p = true).
    {
      rewrite EqClass.eqb_leibniz.
      tauto.
    }
    find_rewrite.
    exists m2.
    split; eauto.
  +
    ff.
    assert (EqClass.eqb p0 p = false).
    {
      apply plc_ne; auto.
    }
    find_rewrite.
    exists m0.
    split.
    ++
      eauto.
    ++
      apply manifest_subset_refl.
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
    destruct a; unfold asp_manifest_generator; ff;
    try (unfold asp_manifest_update);
      try (unfold manifest_update_env);
      try (apply env_subset_set; auto; tauto);
      try (apply env_subset_set_none; auto; tauto).
      + (* NULL case *)
        ff.
        ++
        unfold Environment_subset; intros.
        destruct (eq_plc_dec p p0) eqn:hee.
        +++
        subst.
        unfold manifest_update_env.
        unfold asp_manifest_update.

        ff.
        rewrite eqb_plc_refl.
        exists m.
        split; eauto.
        unfold Environment_subset in H.
        specialize H with (m1:= m1) (p:=p0).
        apply H in H0.
        destruct_conjs.
        repeat find_rewrite.
        ff.
          +++
            unfold Environment_subset in H.
            specialize H with (m1:=m1) (p:=p0).
            apply H in H0.
            destruct_conjs.
            repeat find_rewrite.
            ff.
            assert (EqClass.eqb p0 p = false).
            {
              apply plc_ne; auto.
            }
            find_rewrite.
            exists H0.
            split.
            ++++
              eassumption.
            ++++
              eauto.
        ++
        unfold Environment_subset; intros.
        destruct (eq_plc_dec p p0) eqn:hee.
        +++
        subst.

        unfold Environment_subset in H.
        specialize H with (m1:=m1) (p:=p0).
        apply H in H0.
        destruct_conjs.
        repeat find_rewrite.
        solve_by_inversion.
        +++
          ff.
          assert (EqClass.eqb p0 p = false).
          {
            apply plc_ne; auto. 
          }
          find_rewrite.

          unfold Environment_subset in H.
          specialize H with (m1:=m1) (p:=p0).
          apply H in H0.
          destruct_conjs.
          repeat find_rewrite.

          exists H0.
          split.
          ++++
          auto.
          ++++
            eauto.

    + (* CPY case *)

    ff.
    ++
    unfold Environment_subset; intros.
    destruct (eq_plc_dec p p0) eqn:hee.
    +++
    subst.
    unfold manifest_update_env.
    unfold asp_manifest_update.

    ff.
    rewrite eqb_plc_refl.
    exists m.
    split; eauto.
    unfold Environment_subset in H.
    specialize H with (m1:= m1) (p:=p0).
    apply H in H0.
    destruct_conjs.
    repeat find_rewrite.
    ff.
      +++
        unfold Environment_subset in H.
        specialize H with (m1:=m1) (p:=p0).
        apply H in H0.
        destruct_conjs.
        repeat find_rewrite.
        ff.
        assert (EqClass.eqb p0 p = false).
        {
          apply plc_ne; auto. 
        }
        find_rewrite.
        exists H0.
        split.
        ++++
          eassumption.
        ++++
          eauto.
    ++
    unfold Environment_subset; intros.
    destruct (eq_plc_dec p p0) eqn:hee.
    +++
    subst.

    unfold Environment_subset in H.
    specialize H with (m1:=m1) (p:=p0).
    apply H in H0.
    destruct_conjs.
    repeat find_rewrite.
    solve_by_inversion.
    +++
      ff.
      assert (EqClass.eqb p0 p = false).
      {
        apply plc_ne; auto. 
      }
      find_rewrite.

      unfold Environment_subset in H.
      specialize H with (m1:=m1) (p:=p0).
      apply H in H0.
      destruct_conjs.
      repeat find_rewrite.

      exists H0.
      split.
      ++++
      auto.
      ++++
        eauto.

  + (* ASPC case *) 

    ff.
    unfold update_manifest_policy_targ.
    unfold aspid_manifest_update; ff; subst.
    ++
    unfold Environment_subset; intros.
    destruct (eq_plc_dec p p1) eqn:hee.
      +++
      subst.
      unfold manifest_update_env.
      unfold asp_manifest_update.
    
      ff.
      rewrite eqb_plc_refl.
      eexists.
      split; eauto.
      unfold Environment_subset in H.
      specialize H with (m1:= m1) (p:=p1).
      apply H in H0.
      destruct_conjs.
      repeat find_rewrite.
      ff.
      eapply manifest_subset_trans.
      eassumption.
      unfold aspid_manifest_update.
      ff.
      unfold pubkey_manifest_update in *.
      ff.
      unfold manifest_subset; intros.
      split; ff; intros; eauto.

      +++
        unfold Environment_subset in H.
        specialize H with (m1:=m1) (p:=p1).
        apply H in H0.
        destruct_conjs.
        repeat find_rewrite.
        ff.
        assert (EqClass.eqb p1 p = false).
        {
          apply plc_ne; auto. 
        }
        repeat find_rewrite.
        
        exists H0.

        split.
        ++++
          tauto.
        ++++
          eauto.
    ++
    unfold Environment_subset; intros.
    destruct (eq_plc_dec p p1) eqn:hee.
    +++
    subst.
  
    unfold Environment_subset in H.
    specialize H with (m1:=m1) (p:=p1).
    apply H in H0.
    destruct_conjs.
    repeat find_rewrite.
    solve_by_inversion.
      +++
        ff.
        assert (EqClass.eqb p1 p = false).
        {
          apply plc_ne; auto. 
        }
        find_rewrite.
    
        unfold Environment_subset in H.
        specialize H with (m1:=m1) (p:=p1).
        apply H in H0.
        destruct_conjs.
        repeat find_rewrite.
    
    
        exists H0.
        split.
        ++++
        auto.
        ++++
          eauto.

  + (* SIG case *) 
  ff.
    ++
    unfold Environment_subset; intros.
    destruct (eq_plc_dec p p0) eqn:hee.
      +++
      subst.
      unfold manifest_update_env.
      unfold asp_manifest_update.

      ff.
      rewrite eqb_plc_refl.
      eexists.
      split; eauto.
      unfold Environment_subset in H.
      specialize H with (m1:= m1) (p:=p0).
      apply H in H0.
      destruct_conjs.
      repeat find_rewrite.
      ff.
      eapply manifest_subset_trans.
      eassumption.
      unfold aspid_manifest_update.
      ff.
      unfold manifest_subset; intros.
      split; ff; intros; eauto.
      +++
        unfold Environment_subset in H.
        specialize H with (m1:=m1) (p:=p0).
        apply H in H0.
        destruct_conjs.
        repeat find_rewrite.
        ff.
        assert (EqClass.eqb p0 p = false).
        {
          apply plc_ne; auto.  
        }
        find_rewrite.
        exists H0.
        split.
        ++++
          eassumption.
        ++++
          eauto.
  ++
  unfold Environment_subset; intros.
  destruct (eq_plc_dec p p0) eqn:hee.
    +++
    subst.

    unfold Environment_subset in H.
    specialize H with (m1:=m1) (p:=p0).
    apply H in H0.
    destruct_conjs.
    repeat find_rewrite.
    solve_by_inversion.
    +++
      ff.
      assert (EqClass.eqb p0 p = false).
      {
        apply plc_ne; auto. 
      }
      find_rewrite.

      unfold Environment_subset in H.
      specialize H with (m1:=m1) (p:=p0).
      apply H in H0.
      destruct_conjs.
      repeat find_rewrite.


      exists H0.
      split.
      ++++
      auto.
      ++++
        eauto.
  + (* HSH case *) 

  ff.
  ++

  unfold Environment_subset; intros.
  destruct (eq_plc_dec p p0) eqn:hee.
    +++
    subst.
    unfold manifest_update_env.
    unfold asp_manifest_update.

    ff.
    rewrite eqb_plc_refl.
    eexists.
    split; eauto.
    unfold Environment_subset in H.
    specialize H with (m1:= m1) (p:=p0).
    apply H in H0.
    destruct_conjs.
    repeat find_rewrite.
    ff.
    eapply manifest_subset_trans.
    eassumption.
    unfold aspid_manifest_update.
    ff.
    unfold manifest_subset; intros.
    split; ff; intros; eauto.
    +++
      unfold Environment_subset in H.
      specialize H with (m1:=m1) (p:=p0).
      apply H in H0.
      destruct_conjs.
      repeat find_rewrite.
      ff.
      assert (EqClass.eqb p0 p = false).
      {
        apply plc_ne; auto. 
      }
      find_rewrite.
      exists H0.
      split.
      ++++
        eassumption.
      ++++
        eauto.
  ++
  unfold Environment_subset; intros.
  destruct (eq_plc_dec p p0) eqn:hee.
  +++
  subst.

  unfold Environment_subset in H.
  specialize H with (m1:=m1) (p:=p0).
  apply H in H0.
  destruct_conjs.
  repeat find_rewrite.
  solve_by_inversion.
    +++
      ff.
      assert (EqClass.eqb p0 p = false).
      {
        apply plc_ne; auto. 
      }
      find_rewrite.

      unfold Environment_subset in H.
      specialize H with (m1:=m1) (p:=p0).
      apply H in H0.
      destruct_conjs.
      repeat find_rewrite.


      exists H0.
      split.
      ++++
      auto.
      ++++
        eauto.


  + (* ENC case *) 

    ff.
    ++
    unfold Environment_subset; intros.
    destruct (eq_plc_dec p p1) eqn:hee.
      +++
      subst.
      unfold manifest_update_env.
      unfold asp_manifest_update.
    
      ff.
      rewrite eqb_plc_refl.
      eexists.
      split; eauto.
      unfold Environment_subset in H.
      specialize H with (m1:= m1) (p:=p1).
      apply H in H0.
      destruct_conjs.
      repeat find_rewrite.
      ff.
      eapply manifest_subset_trans.
      eassumption.
      unfold aspid_manifest_update.
      ff.
      unfold pubkey_manifest_update in *.
      ff.
      unfold manifest_subset; intros.
      split; ff; intros; eauto.

        +++
          unfold Environment_subset in H.
          specialize H with (m1:=m1) (p:=p1).
          apply H in H0.
          destruct_conjs.
          repeat find_rewrite.
          ff.
          assert (EqClass.eqb p1 p = false).
          {
            apply plc_ne; auto. 
          }
          repeat find_rewrite.
          
          exists H0.

          split.
          ++++
            tauto.
          ++++
            eauto.
    ++
    unfold Environment_subset; intros.
    destruct (eq_plc_dec p p1) eqn:hee.
      +++
      subst.
    
      unfold Environment_subset in H.
      specialize H with (m1:=m1) (p:=p1).
      apply H in H0.
      destruct_conjs.
      repeat find_rewrite.
      solve_by_inversion.
      +++
        ff.
        assert (EqClass.eqb p1 p = false).
        {
          apply plc_ne; auto. 
        }
        find_rewrite.
    
        unfold Environment_subset in H.
        specialize H with (m1:=m1) (p:=p1).
        apply H in H0.
        destruct_conjs.
        repeat find_rewrite.

        exists H0.
        split.
        ++++
        auto.
        ++++
          eauto.

  - (* at case *)

  unfold at_manifest_generator.
  unfold manifest_update_env.
  ff.
    +
      unfold knowsof_manifest_update; 
        ff; subst.

      apply IHt.
      eapply env_subset_trans.
      eassumption.
      unfold Environment_subset; intros.

      destruct (eq_plc_dec p0 p1).
      ++
        subst.
        find_rewrite.
        ff.
        assert (EqClass.eqb p1 p1 = true).
        {
          rewrite EqClass.eqb_leibniz.
          tauto.
        }
        find_rewrite.
        eexists.
        split.
        reflexivity.
        unfold manifest_subset; intros; ff.
        split; eauto.
      ++
        exists m1.
        split.
        apply mapC_get_distinct_keys; eauto.
        apply manifest_subset_refl.
    +
    unfold knowsof_manifest_update; 
    ff; subst.

    apply IHt.
    eapply env_subset_trans.
    eassumption.
    unfold Environment_subset; intros.

    destruct (eq_plc_dec p0 p1).
      ++
      subst.
      find_rewrite.
      ff.
      ++
      exists m1.
      split.
      apply mapC_get_distinct_keys; eauto.
      apply manifest_subset_refl.

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
  intros.
  unfold at_manifest_generator; ff.
  -
    unfold knowsof_manifest_update; ff; subst; ff.
    unfold Environment_subset; intros; ff.

    destruct (eq_plc_dec p1 p0).
    +
      subst.
      assert (EqClass.eqb p0 p0 = true).
      {
        rewrite EqClass.eqb_leibniz.
        tauto.
      }
      repeat find_rewrite; ff.


      unfold Environment_subset in H; ff.
      specialize H with (m1:= {|
        my_abstract_plc := my_abstract_plc;
        asps := asps;
        uuidPlcs := uuidPlcs;
        pubKeyPlcs := pubKeyPlcs;
        targetPlcs := targetPlcs;
        policy := policy
      |}) (p:=p0).

      apply H in Heqo0.
      clear H.
      destruct_conjs.

      unfold manifest_subset in H0; ff.
      destruct_conjs.

      repeat find_rewrite; ff.

      eexists.
      split.
      ++
        reflexivity.
      ++
        unfold manifest_subset; ff; intros.
        split; intros; eauto.

        split; intros; eauto.

        door.
        +++
          eauto.
        +++
          eauto.
      ++
        unfold empty_Manifest in *.
        ff.
        eexists.
        split; try reflexivity.
        unfold manifest_subset; ff; intros.
        split; intros; eauto; try solve_by_inversion.
        split; intros; eauto; intuition.

      ++
        unfold Environment_subset in H; 
        apply H in Heqo0;
        destruct_conjs;
        repeat find_rewrite;
        ff.
      ++
        unfold empty_Manifest in *; ff.
        eexists.
        split; eauto.
        apply manifest_subset_refl.

    +
    assert (EqClass.eqb p1 p0 = false).
    {
      apply plc_ne; auto.
    }
    repeat find_rewrite; ff.
Qed.

Lemma empty_manifest_always_sub: forall m,
manifest_subset empty_Manifest m.
Proof.
intros;
unfold empty_Manifest; unfold manifest_subset; intros; 
intuition; try solve_by_inversion.
Qed.

Lemma fafafa : forall t p e1 e2,
    Environment_subset e1 e2 ->
    Environment_subset (manifest_generator' p t e1)
                       (manifest_generator' p t e2).
  Proof.
    intros.
    generalizeEverythingElse t.
    induction t; intros.
    - (* asp case *)
      destruct a; ff.
        + (* NULL *)
          unfold asp_manifest_generator;
          unfold manifest_update_env; 
          unfold asp_manifest_update; ff.
          ++
            unfold Environment_subset in *; ff; intros.
            destruct (eq_plc_dec p p0).
            +++
              subst.
              assert (EqClass.eqb p0 p0 = true).
              {
                rewrite EqClass.eqb_leibniz.
                tauto.
              }
              repeat find_rewrite; ff.
            +++
            assert (EqClass.eqb p0 p = false).
              {
                apply plc_ne; auto. 
              }

              repeat find_rewrite; ff.
          ++
            unfold Environment_subset in *; ff; intros.
            destruct (eq_plc_dec p p0).
            +++
              subst.
              assert (EqClass.eqb p0 p0 = true).
              {
                rewrite EqClass.eqb_leibniz.
                tauto.
              }
              repeat find_rewrite; ff.

              specialize H with (m1:=m1) (p:= p0).
              apply H in Heqo.
              destruct_conjs.
              repeat find_rewrite; ff.

            +++
            assert (EqClass.eqb p0 p = false).
              {
                apply plc_ne; auto.
              }

              repeat find_rewrite; ff.
          ++
              unfold Environment_subset in *; ff; intros.
              destruct (eq_plc_dec p p0).
              +++
                subst.
                assert (EqClass.eqb p0 p0 = true).
                {
                  rewrite EqClass.eqb_leibniz.
                  tauto.
                }
                repeat find_rewrite; ff.

                exists m.
                split; try eauto.

                apply empty_manifest_always_sub.
  
              +++
              assert (EqClass.eqb p0 p = false).
                {
                  apply plc_ne; auto.
                }
  
                repeat find_rewrite; ff.

        ++
        unfold Environment_subset in *; ff; intros.
        destruct (eq_plc_dec p p0).
        +++
          subst.
          assert (EqClass.eqb p0 p0 = true).
          {
            rewrite EqClass.eqb_leibniz.
            tauto.
          }
          repeat find_rewrite; ff.

          exists empty_Manifest.
          split; try eauto.

          apply empty_manifest_always_sub.

        +++
        assert (EqClass.eqb p0 p = false).
          {
            apply plc_ne; auto.
          }

          repeat find_rewrite; ff.
  + (* CPY case *)
  unfold asp_manifest_generator;
  unfold manifest_update_env; 
  unfold asp_manifest_update; ff.
  ++
    unfold Environment_subset in *; ff; intros.
    destruct (eq_plc_dec p p0).
    +++
      subst.
      assert (EqClass.eqb p0 p0 = true).
      {
        rewrite EqClass.eqb_leibniz.
        tauto. 
      }
      repeat find_rewrite; ff.
    +++
    assert (EqClass.eqb p0 p = false).
      {
        apply plc_ne; auto.
      }

      repeat find_rewrite; ff.
  ++
    unfold Environment_subset in *; ff; intros.
    destruct (eq_plc_dec p p0).
    +++
      subst.
      assert (EqClass.eqb p0 p0 = true).
      {
        rewrite EqClass.eqb_leibniz.
          tauto. 
      }
      repeat find_rewrite; ff.

      specialize H with (m1:=m1) (p:= p0).
      apply H in Heqo.
      destruct_conjs.
      repeat find_rewrite; ff.

    +++
    assert (EqClass.eqb p0 p = false).
      {
        apply plc_ne; auto. 
      }

      repeat find_rewrite; ff.
  ++
      unfold Environment_subset in *; ff; intros.
      destruct (eq_plc_dec p p0).
      +++
        subst.
        assert (EqClass.eqb p0 p0 = true).
        {
          rewrite EqClass.eqb_leibniz.
          tauto.
        }
        repeat find_rewrite; ff.

        exists m.
        split; try eauto.

        apply empty_manifest_always_sub.

      +++
      assert (EqClass.eqb p0 p = false).
        {
          apply plc_ne; auto.
        }

        repeat find_rewrite; ff.

  ++
    unfold Environment_subset in *; ff; intros.
    destruct (eq_plc_dec p p0).
      +++
        subst.
        assert (EqClass.eqb p0 p0 = true).
        {
          rewrite EqClass.eqb_leibniz.
          tauto.
        }
        repeat find_rewrite; ff.

        exists empty_Manifest.
        split; try eauto.

        apply empty_manifest_always_sub.

      +++
        assert (EqClass.eqb p0 p = false).
        {
          apply plc_ne; auto. 
        }

        repeat find_rewrite; ff.

  + (* ASPC case *)
    unfold asp_manifest_generator; 
    unfold asp_manifest_generator;
    unfold manifest_update_env; 
    unfold asp_manifest_update; 
      ff; subst; unfold aspid_manifest_update; ff; subst.
    ++
      unfold Environment_subset in *; intros; ff.




      destruct (eq_plc_dec p1 p).
      +++
        subst.

        assert (EqClass.eqb p p = true).
        {
          rewrite EqClass.eqb_leibniz.
          tauto.
        }
        repeat find_rewrite; ff.

        unfold update_manifest_policy_targ in *; 
        subst.

        apply H in Heqo.
        destruct_conjs.
        rewrite H0 in *.
        inversion Heqo0; clear Heqo0.
        subst.
        clear H.

        eexists.
        split; eauto;
        unfold manifest_subset in *; intros; 
        intuition; 
        destruct m0, m; simpl in *; 
        inv Heqm0; inv Heqm1;
        destruct_conjs; simpl in *; intuition; eauto.
    +++
      assert (EqClass.eqb p1 p = false).
      {
        apply plc_ne; auto.
      }
      repeat find_rewrite; ff.
  ++
    unfold Environment_subset in H; ff.
    unfold update_manifest_policy_targ in *; subst.
    apply H in Heqo.
    destruct_conjs.
    repeat find_rewrite.
    solve_by_inversion.
  ++
  unfold Environment_subset in *; intros; ff.

  destruct (eq_plc_dec p1 p).
  +++
    subst.

    assert (EqClass.eqb p p = true).
    {
      rewrite EqClass.eqb_leibniz.
          tauto.
    }
    repeat find_rewrite; ff.

    eexists.
    split.
      reflexivity.
      unfold manifest_subset; intros; intuition; ff;
      destruct H0; subst; intuition; eauto.
      * unfold update_manifest_policy_targ in *; 
        destruct m; simpl in *; inv Heqm0; eauto with *.
  +++
  assert (EqClass.eqb p1 p = false).
  {
    apply plc_ne; auto. 
  }
  repeat find_rewrite; ff.

++

unfold Environment_subset in *; intros; ff.

destruct (eq_plc_dec p1 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
          tauto.
  }
  repeat find_rewrite; ff.

  eexists.
  split.
    reflexivity.
    unfold manifest_subset; intros; ff.

+++
assert (EqClass.eqb p1 p = false).
{
  apply plc_ne; auto. 
}
repeat find_rewrite; ff.


+ (* SIG case *)

(*
  unfold asp_manifest_generator; ff;
  ff; subst; unfold aspid_manifest_update; ff; subst.
  *)

  unfold asp_manifest_generator; 
  unfold asp_manifest_generator;
  unfold manifest_update_env; 
  unfold asp_manifest_update; 
    ff; subst; unfold aspid_manifest_update; ff; subst.
++
unfold Environment_subset in *; intros; ff.

destruct (eq_plc_dec p0 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
          tauto.
  }
  repeat find_rewrite; ff.

  apply H in Heqo.
  destruct_conjs.
  rewrite H0 in *.
  inversion Heqo0; clear Heqo0.
  subst.
  clear H.



  eexists.
  split.
  ++++
    reflexivity.
  ++++
  unfold manifest_subset in *; intros; ff.
  destruct_conjs.
  
  split; intros; eauto.
  door.
  +++++
    eauto.
  +++++
  right.
  eauto.
+++
assert (EqClass.eqb p0 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.

++

unfold Environment_subset in H; ff.

apply H in Heqo.
destruct_conjs.
repeat find_rewrite.
solve_by_inversion.


++

unfold Environment_subset in *; intros; ff.

destruct (eq_plc_dec p0 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
    tauto.
  }
  repeat find_rewrite; ff.

  eexists.
  split.
    reflexivity.
      unfold manifest_subset; intros; intuition; ff;
      destruct H0; subst; intuition; eauto.
+++
assert (EqClass.eqb p0 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.


++
unfold Environment_subset in *; intros; ff.

destruct (eq_plc_dec p0 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
    tauto.
  }
  repeat find_rewrite; ff.

  eexists.
  split.
    reflexivity.
    unfold manifest_subset; intros; ff.

+++
assert (EqClass.eqb p0 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.

+ (* HSH case *)

(*
  unfold asp_manifest_generator; ff;
  ff; subst; unfold aspid_manifest_update; ff; subst.
  *)
  unfold asp_manifest_generator; 
  unfold asp_manifest_generator;
  unfold manifest_update_env; 
  unfold asp_manifest_update; 
    ff; subst; unfold aspid_manifest_update; ff; subst.
++
unfold Environment_subset in *; intros; ff.

destruct (eq_plc_dec p0 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
          tauto.
  }
  repeat find_rewrite; ff.

  apply H in Heqo.
  destruct_conjs.
  find_rewrite.
  ff.

  eexists.
  split; eauto.

  unfold manifest_subset; subst; ff; intros.
  split; ff; eauto; intros.
  door; ff.

+++
assert (EqClass.eqb p0 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.

++

unfold Environment_subset in H; ff.

apply H in Heqo.
destruct_conjs.
repeat find_rewrite.
solve_by_inversion.

++
unfold Environment_subset in *; intros; ff.

destruct (eq_plc_dec p0 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
    tauto.
  }
  repeat find_rewrite; ff.

  eexists.
  split.
    reflexivity.
    unfold manifest_subset; intros; intuition; ff;
    destruct H0; subst; intuition; eauto.
+++
assert (EqClass.eqb p0 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.


++
unfold Environment_subset in *; intros; ff.

destruct (eq_plc_dec p0 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
    tauto.
  }
  repeat find_rewrite; ff.

  eexists.
  split.
    reflexivity.
    unfold manifest_subset; intros; ff.

+++
assert (EqClass.eqb p0 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.

+ (* ENC case *)

(*
  unfold asp_manifest_generator; ff;
  ff; subst; unfold aspid_manifest_update; ff; subst;
  unfold pubkey_manifest_update in *; ff; subst.
  *)
  unfold asp_manifest_generator; 
  unfold asp_manifest_generator;
  unfold manifest_update_env; 
  unfold asp_manifest_update; 
  unfold pubkey_manifest_update in *;
    ff; subst; unfold aspid_manifest_update; ff; subst.
++
unfold Environment_subset in *; intros; ff.

destruct (eq_plc_dec p1 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
          tauto.
  }
  repeat find_rewrite; ff.

apply H in Heqo0.
destruct_conjs.
repeat find_rewrite.
ff.

eexists.
split; eauto.

unfold manifest_subset in *; intros; intuition; ff; 
intuition; eauto with *.
+++
assert (EqClass.eqb p1 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.

++

unfold Environment_subset in *; intros; ff.

destruct (eq_plc_dec p1 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
    tauto.
  }
  repeat find_rewrite; ff.
  unfold empty_Manifest in *; ff.

  eexists.
  split.
  reflexivity.
  unfold manifest_subset; intros; intuition; ff;
  destruct H0; subst; intuition; eauto.
+++
assert (EqClass.eqb p1 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.

++
unfold Environment_subset in H.

apply H in Heqo0.
destruct_conjs.
repeat find_rewrite.
solve_by_inversion.

++
  unfold empty_Manifest in *; ff.

  unfold Environment_subset; intros; ff.


destruct (eq_plc_dec p1 p).
+++
  subst.

  assert (EqClass.eqb p p = true).
  {
    rewrite EqClass.eqb_leibniz.
    tauto.
  }
  repeat find_rewrite; ff.
  unfold empty_Manifest in *; ff.

  eexists.
  split.
    reflexivity.
    unfold manifest_subset; intros; ff.

+++
assert (EqClass.eqb p1 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.

- (* at case *)
  ff.
  apply IHt.
  apply env_subset_plc_manifest_gen; auto.

  - (* lseq case *)
    eauto.
  - (* bseq case *)
    eauto.
  - (* bpar case *)
    eauto.
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
    apply mapC_get_works.
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
  induction t; intros.
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
          unfold at_manifest_generator in Heqo.
          unfold manifest_update_env in *.
          unfold knowsof_manifest_update in Heqo.
          break_let.
          ff.
          unfold empty_Manifest in *.
          ff.
          find_rewrite.

          solve_by_inversion.
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

Lemma knows_of_helper : forall stEnv p p' t,
  knowsOf_Env p' (manifest_generator' p t (at_manifest_generator p' p stEnv)) p.
Proof.
  unfold at_manifest_generator, knowsOf_Env, manifest_update_env, map_set, 
    knowsof_manifest_update; simpl in *. intros.
  destruct (map_get stEnv p') eqn:E; simpl in *; eauto.
  - destruct m.
    pose proof (manifest_generator_cumul t p ((p',
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) :: stEnv) ((p',
         {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |}) :: stEnv)); simpl in *;
    pose proof (env_subset_refl ((p',
        {|
          my_abstract_plc := my_abstract_plc;
          asps := asps;
          uuidPlcs := p :: uuidPlcs;
          pubKeyPlcs := pubKeyPlcs;
          targetPlcs := targetPlcs;
          policy := policy
        |}) :: stEnv)); intuition; clear H0;
    unfold Environment_subset, manifest_subset in *; simpl in *;
    pose proof (H1 {|
           my_abstract_plc := my_abstract_plc;
           asps := asps;
           uuidPlcs := p :: uuidPlcs;
           pubKeyPlcs := pubKeyPlcs;
           targetPlcs := targetPlcs;
           policy := policy
         |} p'); rewrite EqClass.eqb_refl in *; intuition.
    destruct H0; clear H1; intuition; simpl in *;
    rewrite H0; eauto.
  - pose proof (manifest_generator_cumul t p ((p',
         {|
           my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
           asps := [];
           uuidPlcs := [p];
           pubKeyPlcs := [];
           targetPlcs := [];
           policy := Manifest_Admits.empty_PolicyT
         |}) :: stEnv) ((p',
         {|
           my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
           asps := [];
           uuidPlcs := [p];
           pubKeyPlcs := [];
           targetPlcs := [];
           policy := Manifest_Admits.empty_PolicyT
         |}) :: stEnv)); simpl in *; 
    pose proof (env_subset_refl ((p',
         {|
           my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
           asps := [];
           uuidPlcs := [p];
           pubKeyPlcs := [];
           targetPlcs := [];
           policy := Manifest_Admits.empty_PolicyT
         |}) :: stEnv)); intuition; clear H0;
    unfold Environment_subset, manifest_subset in *; simpl in *.
    pose proof (H1 {|
           my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
           asps := [];
           uuidPlcs := [p];
           pubKeyPlcs := [];
           targetPlcs := [];
           policy := Manifest_Admits.empty_PolicyT
         |} p'). rewrite EqClass.eqb_refl in *; intuition;
    destruct H0; clear H1; intuition; simpl in *;
    rewrite H0; eauto.
Qed.

Theorem manifest_generator_executability_static' :
    forall (t:Term) (p:Plc) stEnv, 
        executable_global t p (manifest_generator' p t stEnv).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
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
      unfold canRunAsp_Env, asp_manifest_generator, manifest_update_env, 
        asp_manifest_update, update_manifest_policy_targ, aspid_manifest_update, canRunAsp_Manifest, 
        can_measure_target_prop, map_set; simpl in *;
      repeat break_let; repeat break_match; repeat find_injection; simpl in *;
      intuition; eauto; try congruence;
      exfalso; pose proof (EqClass.eqb_leibniz p p); intuition; eauto;
      find_rewrite; congruence.
    +
    cbv.
    ff; intuition; eauto; try congruence;
    exfalso; pose proof (eqb_leibniz p p); intuition; eauto;
      find_rewrite; try congruence.
    +
    cbv.
    ff; intuition; eauto; try congruence;
    exfalso; pose proof (eqb_leibniz p p); intuition; eauto;
      find_rewrite; try congruence.
    +
    cbv.
    ff; intuition; eauto; try congruence;
    exfalso; pose proof (eqb_leibniz p p); intuition; eauto;
      find_rewrite; try congruence.

  - (* at case *)
    simpl in *; intuition; eauto.
    eapply knows_of_helper.
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
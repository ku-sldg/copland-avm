Require Import Maps Term_Defs_Core Manifest Eqb_Evidence
Executable_Facts
  Manifest_Generator Executable_Defs_Prop.

Require Import Auto.

Require Import StructTactics.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.


Definition manifest_subset (m1:Manifest) (m2:Manifest) : Prop :=
  (forall i, In i (asps m1) -> In i (asps m2)) /\
  (forall p, In p (uuidPlcs m1) -> In p (uuidPlcs m2)) /\
  (forall q, In q (pubKeyPlcs m1) -> In q (pubKeyPlcs m2)).

Check Maps.map_get.

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
  intros.
  unfold manifest_subset in *; ff.
  split; intros; destruct_conjs; eauto.
  split; intros; destruct_conjs; eauto.
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
      try (apply env_subset_set; auto; tauto);
      try (apply env_subset_set_none; auto; tauto).
      +
        unfold Environment_subset; intros.
        destruct (eq_plc_dec p p0).
        ++
        subst.
        exists m.
        split.
        apply mapC_get_works.
        unfold Environment_subset in H.
        specialize H with (m1:= m1) (p:= p0).
        apply H in H0.
        destruct_conjs.
        repeat find_rewrite.
        ff.
        ++
        
        unfold Environment_subset in H.
        specialize H with (m1:= m1) (p:=p0).
        apply H in H0.
        destruct_conjs.
        exists H0.
        split.
        +++
        apply mapC_get_distinct_keys; eauto.
        +++
        eassumption.

      +
        unfold Environment_subset; intros.
        unfold Environment_subset in H.
        specialize H with (m1:=m1) (p:=p0).
        apply H in H0.
        destruct_conjs.
        exists H0.
        split.
        ++
          assert (p <> p0).
          {
            unfold not; intros; subst.
            find_rewrite.
            ff.
          }

          apply mapC_get_distinct_keys.
          eassumption.
          eassumption.
        ++
        eassumption.
      +
      unfold Environment_subset; intros.
      unfold Environment_subset in H.
      specialize H with (m1:=m1) (p:=p0).
      apply H in H0.
      destruct_conjs.
      exists H0.
      split.
      ++

        destruct (eq_plc_dec p p0).
        +++
        subst.
        find_rewrite.
        ff.
        assert (EqClass.eqb p0 p0 = true).
        {
          rewrite EqClass.eqb_leibniz.
          tauto.
        }
        rewrite H1.
        tauto.
        +++
          apply mapC_get_distinct_keys;
            eassumption.

      (*
        assert (p <> p0).
        {
          unfold not; intros; subst.
          find_rewrite.
          ff.
        }

        apply mapC_get_distinct_keys.
        eassumption.
        eassumption.
        *)
      ++
      eassumption.



    +
    unfold Environment_subset; intros.
    unfold Environment_subset in H.
    specialize H with (m1:=m1) (p:=p0).
    apply H in H0.
    destruct_conjs.
    exists H0.
    split.
    ++
      assert (p <> p0).
      {
        unfold not; intros; subst.
        find_rewrite.
        ff. 
      }

      apply mapC_get_distinct_keys.
      eassumption.
      eassumption.
    ++
    eassumption.



    + 
      unfold aspid_manifest_update; ff.
      subst.
      eapply env_subset_trans.
      eassumption.
      eapply env_subset_set_man.
      eassumption.
      unfold manifest_subset; intros; ff.
      split; eauto.
    +
      subst.
      
      eapply env_subset_trans.
      eassumption.
      eapply env_subset_set_none.
      eassumption. 
    +

    unfold Environment_subset; intros.
    unfold Environment_subset in H.
    specialize H with (m1:=m1) (p:=p0).
    apply H in H0.
    destruct_conjs.

    destruct (eq_plc_dec p p0).
    +++
      subst.
      find_rewrite.
      ff.
      assert (EqClass.eqb p0 p0 = true).
      {
        rewrite EqClass.eqb_leibniz.
        tauto.
      }
      rewrite H1; clear H1.
      unfold aspid_manifest_update; ff.

      eexists.
      split.
      reflexivity.

      eapply manifest_subset_trans.
      eassumption.
      
      unfold manifest_subset; intros; ff.
      split; eauto.

      +++
      
    exists H0.
    split.
    ++++
    apply mapC_get_distinct_keys; eauto.
    ++++
    eassumption.

  +
    
    unfold Environment_subset; intros.
    unfold Environment_subset in H.
    specialize H with (m1:=m1) (p:=p0).
    apply H in H0.
    destruct_conjs.
    exists H0.
    split.
    ++
      assert (p <> p0).
      {
        unfold not; intros; subst.
        find_rewrite.
        ff. 
      }

      apply mapC_get_distinct_keys.
      eassumption.
      eassumption.
    ++
    eassumption.


    +

    unfold Environment_subset; intros.
    unfold Environment_subset in H.
    specialize H with (m1:=m1) (p:=p0).
    apply H in H0.
    destruct_conjs.

    destruct (eq_plc_dec p p0).
    +++
      subst.
      find_rewrite.
      ff.
      assert (EqClass.eqb p0 p0 = true).
      {
        rewrite EqClass.eqb_leibniz.
        tauto.
      }
      rewrite H1; clear H1.
      unfold aspid_manifest_update; ff.

      eexists.
      split.
      reflexivity.
      eassumption.
(*
      eapply manifest_subset_trans.
      eassumption.
      
      unfold manifest_subset; intros; ff.
      split; eauto.
      *)

      +++
      
    exists H0.
    split.
    ++++
    apply mapC_get_distinct_keys; eauto.
    ++++
    eassumption.

(*
    +
    
    unfold Environment_subset; intros.
    unfold Environment_subset in H.
    specialize H with (m1:=m1) (p:=p0).
    apply H in H0.
    destruct_conjs.
    exists H0.
    split.
    ++
      assert (p <> p0).
      {
        unfold not; intros; subst.
        find_rewrite.
        ff. 
      }

      apply mapC_get_distinct_keys.
      eassumption.
      eassumption.
    ++
    eassumption.

    *)

  +
  unfold Environment_subset; intros.
  unfold Environment_subset in H.
  specialize H with (m1:=m1) (p:=p0).
  apply H in H0.
  destruct_conjs.
  exists H0.
  split.
  ++
    assert (p <> p0).
    {
      unfold not; intros; subst.
        find_rewrite.
        ff. 
    }

    apply mapC_get_distinct_keys.
    eassumption.
    eassumption.
  ++
  eassumption.


  +

  unfold Environment_subset; intros.
  unfold Environment_subset in H.
  specialize H with (m1:=m1) (p:=p1).
  apply H in H0.
  destruct_conjs.

  destruct (eq_plc_dec p p1).
  +++
    subst.
    find_rewrite.
    ff.
    assert (EqClass.eqb p1 p1 = true).
    {
      rewrite EqClass.eqb_leibniz.
      tauto.
    }
    rewrite H1; clear H1.
    unfold aspid_manifest_update; ff.

    eexists.
    split.
    reflexivity.

    eapply manifest_subset_trans.
    eassumption.
    apply manifest_subset_refl.

    +++

  exists H0.
  split.
  ++++
  apply mapC_get_distinct_keys; eauto.
  ++++
  eassumption.

  +
  unfold Environment_subset; intros.
  unfold Environment_subset in H.
  specialize H with (m1:=m1) (p:=p1).
  apply H in H0.
  destruct_conjs.
  exists H0.
  split.
  ++
    assert (p <> p1).
    {
      unfold not; intros; subst.
        find_rewrite.
        ff. 
    }

    apply mapC_get_distinct_keys.
    eassumption.
    eassumption.
  ++
  eassumption.

  - (* at case *)

  (*
  assert (Environment_subset e 
  (manifest_generator' p t e)) by eauto.
  clear IHt.
  *)

  unfold plc_manifest_generator.
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

    (*
    assert (EqClass.eqb p1 p1 = true).
    {
      admit. 
    }
    find_rewrite.
    eexists.
    split.
    reflexivity.
    unfold manifest_subset; intros; ff.
    split; eauto. *)
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




(*


  intros.
  generalizeEverythingElse t.
  induction t; intros; ff.
  - (* asp case *)
    destruct a; unfold asp_manifest_generator; ff;
      try (apply env_subset_set; auto; tauto);
      try (apply env_subset_set_none; auto; tauto).
      +
        subst.
        unfold aspid_manifest_update.
        ff.
        unfold Environment_subset; intros.
        ff.
        subst.
        destruct (eq_plc_dec p1 p).
        ++
          subst.
          rewrite H in *.
          inversion Heqo; clear Heqo.
          subst.
          assert (EqClass.eqb p p = true).
          {
            admit. 
          }
          find_rewrite.
          eexists.
          split.
          reflexivity.

          unfold manifest_subset; intros.
          ff.
          split.
          +++
            intros.
            right; eauto.
          +++
            split.
            ++++
              intros.
              eassumption.
            ++++
              intros.
              eassumption.
        ++
          assert (EqClass.eqb p1 p = false).
          {
            admit. 
          }
          find_rewrite.
          exists m1.
          split.
          eassumption.
          apply manifest_subset_refl.
      +
      subst.
      unfold aspid_manifest_update.
      ff.
      unfold Environment_subset; intros.
      ff.
      subst.
      destruct (eq_plc_dec p0 p).
      ++
        subst.
        rewrite H in *.
        inversion Heqo; clear Heqo.
        subst.
        assert (EqClass.eqb p p = true).
        {
          admit. 
        }
        find_rewrite.
        eexists.
        split.
        reflexivity.

        unfold manifest_subset; intros.
        ff.
        split.
        +++
          intros.
          right; eauto.
        +++
          split.
          ++++
            intros.
            eassumption.
          ++++
            intros.
            eassumption.
      ++
        assert (EqClass.eqb p0 p = false).
        {
          admit. 
        }
        find_rewrite.
        exists m1.
        split.
        eassumption.
        apply manifest_subset_refl.
  - (* at case *)
        assert (Environment_subset e 
                  (manifest_generator' p t e)) by eauto.
        clear IHt.

        unfold plc_manifest_generator.
        ff.
        +
          unfold knowsof_manifest_update; 
            ff; subst.

          


          assert (
          Environment_subset e 
          

          (map_set e p0
          (
        {|
          my_abstract_plc := my_abstract_plc;
          asps := asps;
          uuidPlcs := p :: uuidPlcs;
          pubKeyPlcs := pubKeyPlcs;
          policy := policy
        |}))

          
          ).

          {

          eapply env_subset_set_man.
          ++
          eassumption.
          ++
          unfold manifest_subset; intros; ff.
          split; try auto.

          }
          

          
          
          eapply env_subset_trans with (e2:= e).
          eassumption.







        unfold Environment_subset in *; intros.
        unfold plc_manifest_generator; ff.
        +
          destruct (eq_plc_dec p0 p).
            ++
              subst.
              exists m1.
              split.
              +++
                unfold knowsof_manifest_update; ff.
                subst.



              destruct (eq_plc_dec p p1).
                +++
                  subst.
                  find_rewrite.
                  ff.
              subst.

        apply H.


          unfold knowsof_manifest_update; ff.
          subst.
          destruct (eq_plc_dec p0 p).
          ++
            subst.
            rewrite H0 in *.
            ff.
            apply H.
            specialize H with (m1:= )
            exists 
            
            split.







              



Admitted.

Lemma manifest_generator_cumul : forall t p e1 e2,
    Environment_subset e1 e2 ->
    Environment_subset e1 (manifest_generator' p t e2).
Proof.
    intros.
    assert (Environment_subset e2 (manifest_generator' p t e2)).
    {
      apply manifest_generator_cumul'.
    }
    eapply env_subset_trans; eassumption.
Qed.
*)

  Lemma exec_static_cumul : forall t p e1 e2,
    executable_static t p e1 -> 
    Environment_subset e1 e2 -> 
    executable_static t p e2.
  Proof.
    intros.
    generalizeEverythingElse t.
    induction t; intros.
    - (* asp case *)
    destruct a; ff.
    +
      subst.
      unfold canRunAsp_Env in *.
      ff.
      ++
      unfold Environment_subset in *; ff.
      specialize H0 with (m1:=m0) (p:=p).
      apply H0 in Heqo0.
      destruct_conjs.
      find_rewrite.
      ff.
      unfold manifest_subset in *; ff.
      ++
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
  (plc_manifest_generator p0 p e1) 
  (plc_manifest_generator p0 p e2).
Proof.
  intros.
  unfold plc_manifest_generator; ff.
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
        policy := policy
      |}) (p:=p0).

      apply H in Heqo.
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
    +
    assert (EqClass.eqb p1 p0 = false).
    {
      apply plc_ne; auto.
    }
    repeat find_rewrite; ff.
-
  unfold Environment_subset in H.
  specialize H with (m1:= m) (p:=p0).
  apply H in Heqo.
  destruct_conjs.
  repeat find_rewrite; ff.

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

  eexists.
  split.
  ++
    reflexivity.
  ++
    unfold manifest_subset; intros; ff.
    split; intros; eauto.
    solve_by_inversion.
    split; intros; eauto.
    door.
      eauto.
      solve_by_inversion.
      solve_by_inversion.
+
assert (EqClass.eqb p1 p0 = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.


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

  eexists.
  split.
  ++
    reflexivity.
  ++
    unfold manifest_subset; intros; ff.
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
intros.
unfold empty_Manifest.
unfold manifest_subset; intros; ff.
split; intros; try solve_by_inversion.
split; intros; try solve_by_inversion.
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
          unfold asp_manifest_generator; ff.
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
  unfold asp_manifest_generator; ff.
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


        specialize H with (m1:= {|
          my_abstract_plc := my_abstract_plc;
          asps := asps;
          uuidPlcs := uuidPlcs;
          pubKeyPlcs := pubKeyPlcs;
          policy := policy
        |}) (p:=p).
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
      assert (EqClass.eqb p1 p = false).
      {
        apply plc_ne; auto.
      }
      repeat find_rewrite; ff.
  ++
    unfold Environment_subset in H; ff.
    specialize H with (m1:={|
      my_abstract_plc := my_abstract_plc;
      asps := asps;
      uuidPlcs := uuidPlcs;
      pubKeyPlcs := pubKeyPlcs;
      policy := policy
    |}) (p:=p).

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
      unfold manifest_subset; intros; ff.
      split; intros.
      ++++
      door.
        +++++
          left; eauto.
        +++++
          solve_by_inversion.
      ++++
        split; intros; solve_by_inversion.
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

  unfold asp_manifest_generator; ff;
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


  specialize H with (m1:= {|
    my_abstract_plc := my_abstract_plc;
    asps := asps;
    uuidPlcs := uuidPlcs;
    pubKeyPlcs := pubKeyPlcs;
    policy := policy
  |}) (p:=p).
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
specialize H with (m1:={|
  my_abstract_plc := my_abstract_plc;
  asps := asps;
  uuidPlcs := uuidPlcs;
  pubKeyPlcs := pubKeyPlcs;
  policy := policy
|}) (p:=p).

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
    unfold manifest_subset; intros; ff.
    split; intros.
    ++++
    door.
      +++++
        left; eauto.
      +++++
        solve_by_inversion.
    ++++
      split; intros; solve_by_inversion.
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

  unfold asp_manifest_generator; ff;
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


  (*


  specialize H with (m1:= {|
    my_abstract_plc := my_abstract_plc;
    asps := asps;
    uuidPlcs := uuidPlcs;
    pubKeyPlcs := pubKeyPlcs;
    policy := policy
  |}) (p:=p).
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

  *)


+++
assert (EqClass.eqb p0 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.

++

unfold Environment_subset in H; ff.

specialize H with (m1:=m) (p:=p).


(*
specialize H with (m1:={|
  my_abstract_plc := my_abstract_plc;
  asps := asps;
  uuidPlcs := uuidPlcs;
  pubKeyPlcs := pubKeyPlcs;
  policy := policy
|}) (p:=p). *)

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
    unfold manifest_subset; intros; ff.
    split; intros.
    ++++
      solve_by_inversion.
      (*
    door.
      +++++
        left; eauto.
      +++++
        solve_by_inversion. *)
    ++++
      split; intros; solve_by_inversion.
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

  unfold asp_manifest_generator; ff;
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


  (*


  specialize H with (m1:= {|
    my_abstract_plc := my_abstract_plc;
    asps := asps;
    uuidPlcs := uuidPlcs;
    pubKeyPlcs := pubKeyPlcs;
    policy := policy
  |}) (p:=p).
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

  *)


+++
assert (EqClass.eqb p1 p = false).
{
  apply plc_ne; auto.
}
repeat find_rewrite; ff.

++

unfold Environment_subset in H; ff.

specialize H with (m1:=m) (p:=p).


(*
specialize H with (m1:={|
  my_abstract_plc := my_abstract_plc;
  asps := asps;
  uuidPlcs := uuidPlcs;
  pubKeyPlcs := pubKeyPlcs;
  policy := policy
|}) (p:=p). *)

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
    unfold manifest_subset; intros; ff.
    split; intros.
    ++++
      solve_by_inversion.
      (*
    door.
      +++++
        left; eauto.
      +++++
        solve_by_inversion. *)
    ++++
      split; intros; solve_by_inversion.
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


Lemma afafa : forall e p t p0 m m',
Environment_subset e (manifest_generator' p t e) -> 
map_get (manifest_generator' p t e) p0 = Some m -> 
e = [(p0, m')] ->
manifest_subset m' m.
Proof.
  intros.
  subst.
  asdf.
Admitted.

Theorem manifest_generator_executability_static :
    forall (t:Term) (p:Plc), 
        executable_static t p (manifest_generator t p).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* asp case *)
    destruct a; 
    try (simpl in *; trivial).
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
  - (* at case *)

    unfold manifest_generator in *.
    cbn.
    intros.
    unfold knowsOf_Env in *.
    ff.
    Focus 2.
    admit.
    split.
    +
    ff.
    unfold e_empty in *.
    unfold map_set in *.
    ff.

    (*

Lemma manifest_generator_cumul' : forall t p e,
  Environment_subset e (manifest_generator' p t e).
  *)

  assert (manifest_subset 
    {|
                my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
                asps := [];
                uuidPlcs := [p];
                pubKeyPlcs := [];
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
        policy := Manifest_Admits.empty_PolicyT
      |})])

      (manifest_generator' p t
            [(p0,
              {|
                my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
                asps := [];
                uuidPlcs := [p];
                pubKeyPlcs := [];
                policy := Manifest_Admits.empty_PolicyT
              |})]) 


      ).
      {
        apply manifest_generator_cumul.
        apply env_subset_refl.
      }

      eapply afafa.
      apply H.
      apply Heqo.
      reflexivity.

      }


      unfold manifest_subset in H; ff.
      destruct_conjs.
      apply H0.
      left; eauto.


(*

    assert (m = {|
      my_abstract_plc := Manifest_Admits.empty_Manifest_Plc;
      asps := [];
      uuidPlcs := [p];
      pubKeyPlcs := [];
      policy := Manifest_Admits.empty_PolicyT
    |}).
    admit.
    subst.
    simpl.
    left. eauto.
    *)
    +
    assert (executable_static t p (manifest_generator' p t e_empty)).
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

Abort.




(*
Theorem manifest_generator_executability :
    forall (t t':Term) (top_plc p:Plc) (t_places : list Plc) 
           (env_map : EnvironmentM) (m:Manifest), 
    env_map = (manifest_generator t top_plc) ->
    t_places = (places top_plc t) ->
    In p t_places -> 
    In t' (place_terms t top_plc p) ->
    Maps.map_get env_map p = Some m ->
    executable t' m.
*)
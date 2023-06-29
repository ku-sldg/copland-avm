Require Import Maps Term_Defs_Core Manifest Eqb_Evidence
Executable_Facts
  Manifest_Generator Executable_Defs_Prop.

Require Import Auto.

Require Import StructTactics.

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

Lemma env_subset_refl : forall e, 
  Environment_subset e e.
Proof.
  intros.
  unfold Environment_subset; intros.
  exists m1.
  split; ff.
  
  apply manifest_subset_refl.
Qed.

  (*
  Lemma env_subset_trans : forall e1 e2 e3,
  Environment_subset e1 e2 ->
  Environment_subset e2 e3 -> 
  Environment_subset e1 e3.
  Proof.
  Admitted.
  *)

Lemma manifest_generator_cumul : forall t p e1 e2,
    Environment_subset e1 e2 ->
    Environment_subset e1 (manifest_generator' p t e2).
  Proof.
  Admitted.

  Lemma exec_static_cumul : forall t p e1 e2,
    executable_static t p e1 -> 
    Environment_subset e1 e2 -> 
    executable_static t p e2.
  Proof.
  Admitted.

  Lemma fafafa : forall t p e1 e2,
    Environment_subset e1 e2 ->
    Environment_subset (manifest_generator' p t e1)
                       (manifest_generator' p t e2).
  Proof.
    intros.
    apply manifest_generator_cumul.

    generalizeEverythingElse t.
    induction t; intros; ff.
    -
    destruct a; ff;
    unfold asp_manifest_generator; ff.
    +
      unfold Environment_subset in *; intros.
      apply H.
      Check eqb_plc.
      destruct (eqb_plc p p0) eqn:hi.
      ++
      assert (m = m1). admit.
      subst.
      rewrite eqb_eq_plc in *.
      subst.
      eassumption.
      ++
      admit.
    +
      unfold Environment_subset in *; intros.
      apply H.
      destruct (eqb_plc p p0) eqn:hi.
      ++
      
      rewrite eqb_eq_plc in *.
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
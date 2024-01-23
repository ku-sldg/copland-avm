(* Core properties about the Manifest Generator output.
    Also included:  manifest and environment subset definitions and associated properties. 
    TODO: consider renaming some of these lemmas (e.g. fafafa, afafafa, ...) *)

Require Import Maps Term_Defs_Core Manifest Eqb_Evidence EqClass Manifest_Generator.

Require Import Auto StructTactics.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)


Definition manifest_subset (m1:Manifest) (m2:Manifest) : Prop :=
  (forall i, In_set i (asps m1) -> In_set i (asps m2)) /\
  (forall pr, In_set pr (appraisal_asps m1) -> In_set pr (appraisal_asps m2)) /\
  (forall p, In_set p (uuidPlcs m1) -> In_set p (uuidPlcs m2)) /\
  (forall q, In_set q (pubKeyPlcs m1) -> In_set q (pubKeyPlcs m2)) /\
  (forall p, In_set p (targetPlcs m1) -> In_set p (targetPlcs m2)).

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

      simpl in *; eauto;
      try ( find_apply_hyp_hyp;
      try eapply in_set_add; eauto; tauto);
      ff; simpl in *; eauto;

      try (
        find_apply_hyp_hyp;
        try eapply in_set_add; eauto
      ).
  
    * assert (p <> p0). intros HC. rewrite <- eqb_leibniz in HC. 
      rewrite eqb_symm in HC; congruence.
      erewrite (mapC_get_distinct_keys e2 p p0 _ _ H6 H2); eexists; intuition; eauto.

  - (* at case *)
    eapply IHt; clear IHt; unfold Environment_subset in *; intuition.
    unfold at_manifest_generator, manifest_update_env, knowsof_manifest_update; 
    simpl in *;
    destruct (H _ _ H0); intuition; clear H H0; unfold manifest_subset in *; intuition; eauto.
    destruct (eqb p0 p1) eqn:E.
    * rewrite eqb_leibniz in *; subst.
      rewrite H2; destruct x. rewrite mapC_get_works;
      eexists; intuition; eauto; simpl in *; eauto.
      
      find_apply_hyp_hyp;
      eapply in_set_add; eauto.
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

Lemma env_subset_plc_manifest_gen: forall e1 e2 p0 p,
Environment_subset e1 e2 ->
Environment_subset 
  (at_manifest_generator p0 p e1) 
  (at_manifest_generator p0 p e2).
Proof.
Admitted.

(*
  unfold Environment_subset, manifest_subset, at_manifest_generator,
    knowsof_manifest_update, manifest_update_env, empty_Manifest in *; 
  simpl in *; intuition.
  destruct (eqb p0 p1) eqn:E.
  - rewrite eqb_leibniz in *; subst;
    rewrite mapC_get_works in *; ff;
    try (eexists; simpl in *; intuition; simpl in *; eauto; fail);
    simpl in *; intuition; eauto; 
    try
    destruct (H _ _ Heqo0); simpl in *; intuition; eauto.
    * find_rewrite; find_injection;
      eexists; simpl in *; intuition; simpl in *; eauto.

    * find_injection.
    eexists; simpl in *; intuition; simpl in *; eauto.

      * find_rewrite; congruence.
      * find_rewrite; find_injection.
        eexists; simpl in *; intuition; simpl in *; eauto.


(*

    * find_rewrite; congruence.










unfold Environment_subset, manifest_subset, at_manifest_generator,
knowsof_manifest_update, manifest_update_env, empty_Manifest in *; 
simpl in *; intuition.
destruct (eqb p0 p1) eqn:E.
- rewrite eqb_leibniz in *; subst;
rewrite mapC_get_works in *; ff;
try (eexists; simpl in *; intuition; simpl in *; eauto; fail);
try destruct (H _ _ Heqo0); simpl in *; intuition; eauto.
* find_rewrite; find_injection;
  eexists; simpl in *; intuition; simpl in *; eauto.
* 
  Print find_injection.


find_injection.

admit. 
* find_rewrite; congruence.
* find_rewrite.
  find_rewrite.
  invc Heqm.
  invc Heqm0.
  eexists; simpl in *; intuition; simpl in *; eauto.


  Locate find_injection.
  
  find_injection.
  find_rewrite.
  ff.


find_rewrite; find_injection;
  eexists; simpl in *; intuition; simpl in *; eauto.
* find_rewrite; congruence.



  unfold Environment_subset, manifest_subset, at_manifest_generator,
    knowsof_manifest_update, manifest_update_env, empty_Manifest in *; 
  simpl in *; intuition.
  destruct (eqb p0 p1) eqn:E.
  - rewrite eqb_leibniz in *; subst;
    rewrite mapC_get_works in *; ff;
    try (eexists; simpl in *; intuition; simpl in *; eauto; fail).

    * destruct (H _ _ Heqo0); simpl in *; intuition; eauto.
      eexists.
      split; try reflexivity.
      split; intros; simpl; try eauto.
      ff.
      find_rewrite.
      ff.
      find_rewrite.
      ff.
      split;
      eauto.
      split; eauto.
      intros.
      door; eauto.


    * invc Heqm0.
      eexists.
      split; try reflexivity.
      split; simpl;  try intuition.

    * destruct (H _ _ Heqo0); simpl in *; intuition; eauto.
      eexists.
      split; try reflexivity.
      split; intros; simpl; try eauto.
      ff.
      find_rewrite.
      ff.
      find_rewrite.
      ff.

      * invc Heqm0.
      eexists.
      split; try reflexivity.
      split; simpl;  try intuition.

*)




  - ff; subst; simpl in *;
    try (eexists; simpl in *; intuition; simpl in *; eauto; fail);
    assert (p0 <> p1) by (intros HC; rewrite <- eqb_leibniz in HC; congruence);
    assert (map_get e1 p1 = Some m1) by (eapply mapC_get_distinct_keys_from_set; eauto); 
    destruct (H _ _ H2); intuition; eauto;
    erewrite mapC_get_distinct_keys; eauto;
    eexists; simpl in *; intuition; simpl in *; eauto.
Qed.
*)



Local Hint Resolve env_subset_plc_manifest_gen : core.


Lemma empty_manifest_always_sub: forall m,
manifest_subset empty_Manifest m.
Proof.
intros;
unfold empty_Manifest; unfold manifest_subset; intros; 
intuition; try solve_by_inversion;
ff;

eapply In_set_empty_contra; eauto.
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
          (* try (destruct (H _ _ H1); intuition; eauto). *)
          unfold manifest_subset in *; simpl in *;
          rewrite mapC_get_works in *;
          repeat find_rewrite; repeat find_injection; simpl in *; eauto;
          eexists; simpl in *; intuition; simpl in *; eauto; try congruence;
          try find_apply_hyp_hyp;
          destruct_conjs; ff;
          try find_rewrite; repeat find_injection; ff;



          try match goal with 
          | H1 : In_set _ (manset_add _ _) |- _ => 
            apply manadd_In_set in H1;
          door; subst;
          try (find_apply_hyp_hyp);
            try (eapply manadd_In_add);
            try (eapply in_set_add);
          eauto
          end;

          try (apply manadd_In_add); try (subst; apply manadd_In_add)
      

          | 
          assert (p1 <> p2) by (intros HC; rewrite <- eqb_leibniz in HC; congruence);
          assert (HM : map_get e1 p2 = Some m2) by (eapply mapC_get_distinct_keys_from_set; eauto);
          destruct (H _ _ HM); intuition; eauto;
          erewrite mapC_get_distinct_keys; eauto



        ]
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
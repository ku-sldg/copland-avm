(* Core properties about the Manifest Generator output.
    Also included:  manifest and environment subset definitions and associated properties. 
    TODO: consider renaming some of these lemmas (e.g. fafafa, afafafa, ...) *)

Require Import Maps Manifest EqClass Manifest_Generator Manifest_Union.

Require Import Auto StructTactics.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)


Definition manifest_subset (m1:Manifest) (m2:Manifest) : Prop :=
  (forall i, In_set i (asps m1) -> In_set i (asps m2)).

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
  intros; 
  unfold manifest_subset; eauto.
Qed.

Lemma manifest_subset_trans : forall m1 m2 m3,
  manifest_subset m1 m2 ->
  manifest_subset m2 m3 ->
  manifest_subset m1 m3.
Proof.
  intros; unfold manifest_subset in *; intuition.
Qed.

Global Hint Resolve manifest_subset_trans : core.

Lemma manifest_subset_union_l : forall m1 m2,
  manifest_subset m1 (manifest_union_asps m1 m2).
Proof.
  induction m1; destruct m2; simpl in *; intuition; eauto;
  unfold manifest_subset; simpl in *; intuition; eauto;
  try eapply union_inclusion_l; eauto.
Qed.
Global Hint Resolve manifest_subset_union_l : core.

Lemma manifest_subset_union_r : forall m1 m2,
  manifest_subset m2 (manifest_union_asps m1 m2).
Proof.
  induction m1; destruct m2; simpl in *; intuition; eauto;
  unfold manifest_subset; simpl in *; intuition; eauto;
  try eapply union_inclusion_r; eauto.
Qed.
Global Hint Resolve manifest_subset_union_r : core.


Lemma env_subset_refl : forall e, 
  Environment_subset e e.
Proof.
  intros.
  unfold Environment_subset; intros; 
  exists m1; intuition; eauto;
  eapply manifest_subset_refl.
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
Qed.

Lemma env_subset_set_man : forall e p m1 m2,
  map_get e p = Some m1 ->
  manifest_subset m1 m2 ->
  Environment_subset e (map_set e p m2).
Proof.
  induction e; simpl in *; intuition; eauto; try congruence;
  ff; repeat (rewrite eqb_eq in *); subst.
  - unfold Environment_subset; intuition; simpl in *;
    ff; eauto.
    exists m0; intuition; eauto; eapply manifest_subset_refl.
  - unfold Environment_subset; intuition; simpl in *;
    ff; eauto.
    * exists m0; intuition; eauto; eapply manifest_subset_refl.
    * destruct (eqb p p0) eqn:E.
      ** rewrite eqb_eq in *; subst.
          rewrite mapC_get_works; exists m2; intuition; eauto.
          find_rewrite; find_injection; eauto.
      ** 
        assert (p <> p0). intros HC. rewrite <- eqb_eq in HC; congruence.
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

(* Lemma map_get_man_gen_cons : forall t tp e p m p' x,
  map_get e tp = None ->
  map_get (manifest_generator' p t e) p' = Some x ->
  manifest_subset m x ->
  forall anyM,
  exists m',
    map_get (manifest_generator' p t ((tp, anyM) :: e)) p' = Some m' /\
    manifest_subset m m'.
Proof.
  induction t; simpl in *; intuition; eauto.
Admitted.

Lemma get_man_gen_env : forall t tp e p m,
  map_get e p = Some m ->
  exists m',
    map_get (manifest_generator' tp t e) p = Some m' /\
    manifest_subset m m'.
Proof.
  induction t; simpl in *; intuition; eauto.
  - unfold manifest_update_env, asp_manifest_update,
      aspid_manifest_update;
    ff; subst; destEq p tp;
    try rewrite mapC_get_works; eauto;
    try rewrite map_distinct_key_rw; eauto;
    repeat find_rewrite; repeat find_injection;
    eauto using manifest_subset_refl; try congruence;
    eexists; intuition; eauto;
    unfold manifest_subset; simpl in *; intuition; 
    pose proof @in_set_add;
    eauto.
  - break_match; eauto. 
    eapply (IHt p) in H; break_exists; intuition.
    clear IHt.
    eapply map_get_man_gen_cons; eauto.
    induction t; simpl in *; intuition; eauto.
    * unfold manifest_update_env, asp_manifest_update,
        aspid_manifest_update in *; 
      simpl in *; repeat ff; repeat find_rewrite;
      try rewrite String.eqb_eq in *;
      try rewrite String.eqb_neq in *;
      subst; repeat find_rewrite; try congruence;
      try rewrite mapC_get_works in *; 
      repeat find_injection; eauto; subst.
      try match goal with
      | H : ?p <> ?p0 
        H1 : map_get (map_set _ ?p _) ?p0 = _
        |- _ =>
          erewrite map_distinct_key_rw in H1
      end.
      erewrite Heqb0 in *.
      try rewrite map_distinct_key_rw in *; 
      repeat find_rewrite; repeat find_injection;
      eauto; try congruence.
      Search (String.eqb _ _ = false).
      ff; eauto. 
  - eapply IHt1 in H; break_exists; intuition;
    eapply IHt2 in H0; break_exists; intuition; eauto.
  - eapply IHt1 in H; break_exists; intuition;
    eapply IHt2 in H0; break_exists; intuition; eauto.
  - eapply IHt1 in H; break_exists; intuition;
    eapply IHt2 in H0; break_exists; intuition; eauto.
Qed. *)

Lemma manifest_union_asps_empty_r : forall m,
  manifest_union_asps m empty_Manifest = m.
Proof.
  destruct m; reflexivity.
Qed.

Lemma env_subset_cons_none : forall e2 e1 p m,
  map_get e2 p = None ->
  Environment_subset e1 e2 ->
  Environment_subset e1 ((p, m) :: e2).
Proof.
  intros.
  unfold Environment_subset in *.
  intuition.
  eapply H0 in H1; break_exists; intuition.
  simpl in *; ff; eauto;
  rewrite String.eqb_eq in *; congruence.
Qed.

Lemma manifest_generator_cumul : forall t p e1 e2,
    Environment_subset e1 e2 ->
    Environment_subset e1 (manifest_generator' p t e2).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; try (ff; eauto; fail).
  - (* asp case *)
    ff; eauto;
    unfold Environment_subset in *;
    intuition.
    unfold manifest_update_env, asp_manifest_update, 
      aspid_manifest_update; try congruence.
    ff; subst; find_apply_hyp_hyp; break_exists;
    intuition; destEq p0 p;
    repeat find_rewrite; repeat find_injection;
    try rewrite mapC_get_works; eauto; try congruence;
    try match goal with
    | E : ?p0 <> ?p ,
      H1 : map_get ?e ?p0 = ?r1,
      H2 : map_get ?e ?p = ?r2 |- 
      context [map_get (map_set ?e ?p ?m) ?p0] =>
      erewrite map_distinct_key_rw; eauto
    end;
    eexists; intuition; eauto;
    unfold manifest_subset in *; intuition; simpl in *;
    find_apply_hyp_hyp; eauto;
    eapply in_set_add; eauto.
  - simpl in *; ff.
    eapply IHt;
    eapply env_subset_cons_none; eauto.
Qed.

Lemma manifest_generator_cumul' : forall t p e,
  Environment_subset e (manifest_generator' p t e).
Proof.
  intros.
  apply manifest_generator_cumul.
  apply env_subset_refl.
Qed.

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

Lemma env_subset_l_cons : forall e1 e2 p m m',
  map_get e2 p = Some m ->
  Environment_subset e1 e2 ->
  manifest_subset m' m ->
  Environment_subset ((p, m') :: e1) e2.
Proof.
  intuition;
  unfold Environment_subset, manifest_subset in *;
  simpl in *; intuition; ff; eauto;
  rewrite String.eqb_eq in *; subst; eauto.
Qed.

Lemma env_subset_both_cons : forall e1 e2 p m,
  Environment_subset e1 e2 ->
  Environment_subset ((p, m) :: e1) ((p, m) :: e2).
Proof.
  intuition;
  unfold Environment_subset, manifest_subset in *;
  simpl in *; intuition; ff; eauto;
  rewrite String.eqb_eq in *; subst; eauto.
Qed.

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
    unfold manifest_update_env, asp_manifest_update,
      aspid_manifest_update, Environment_subset, 
      empty_Manifest in *; ff;
    simpl in *; intuition; eauto;


    try match goal with 
    | H1 : map_get e1 ?p1 = _,
      H2 : map_get (map_set e1 ?p1 _) ?p2 = Some ?m2 |- _ =>
        destruct (eqb p1 p2) eqn:E;

        [
          rewrite eqb_eq in *; subst;
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
          assert (p1 <> p2) by (intros HC; rewrite <- eqb_eq in HC; congruence);
          assert (HM : map_get e1 p2 = Some m2) by (eapply mapC_get_distinct_keys_from_set; eauto);
          destruct (H _ _ HM); intuition; eauto;
          erewrite mapC_get_distinct_keys; eauto



        ]
      end. 
  - simpl in *; ff; eapply IHt; eauto. 
    * unfold Environment_subset in *; intuition.
      eapply H in Heqo; break_exists; find_rewrite; 
      intuition; congruence.
    * eapply env_subset_l_cons; eauto.
    * eapply env_subset_both_cons; eauto. 
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
    simpl in *; rewrite String.eqb_refl; eauto.
  }
  apply H0 in H1.
  destruct_conjs.
  rewrite H2 in *.
  ff.
Qed.
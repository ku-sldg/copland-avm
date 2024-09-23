(* Core properties about the Manifest Generator output.
    Also included:  manifest and environment subset definitions and associated properties. *)

Require Import Maps Manifest EqClass Manifest_Generator Manifest_Union.
Require Import Coq.Program.Tactics.

Require Import StructTactics.

Require Import List.
Import ListNotations.

Definition manifest_subset (m1:Manifest) (m2:Manifest) : Prop :=
  (forall i, In_set i (asps m1) -> In_set i (asps m2)).

Definition Environment_subset (e1:EnvironmentM) (e2:EnvironmentM) : Prop := 
  forall m1 p, 
  Maps.map_get p e1 = Some m1 -> 

  (exists m2, 
    Maps.map_get p e2 = Some m2 /\
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
  map_get p e = Some m1 ->
  manifest_subset m1 m2 ->
  Environment_subset e (map_set p m2 e).
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
  map_get p e = Some m ->
  Environment_subset e (map_set p m e).
Proof.
  intros.
  apply env_subset_set_man with (m1:=m); eauto;
  apply manifest_subset_refl.
Qed. 

Lemma env_subset_set_none : forall e p m,
  map_get p e = None ->
  Environment_subset e (map_set p m e).
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
  map_get p e2 = None ->
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

Require Import Term_Defs_Core.

Lemma appr_manifest_update_cumul : forall G et m m',
  appr_manifest_update G et m = resultC m' ->
  manifest_subset m m'.
Proof.
  induction et using EvidenceT_double_ind; simpl in *; intuition; ff;
  unfold aspid_manifest_update; 
  unfold manifest_subset; intuition; 
  simpl in *; ff; try eapply in_set_add; eauto;
  ffa using result_monad_unfold.
Qed.

Lemma manifest_generator_cumul : forall G t et p e1 e2 e',
    Environment_subset e1 e2 ->
    manifest_generator' G p et t e2 = resultC e' ->
    Environment_subset e1 e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; try (ffa using result_monad_unfold; eauto; fail).
  - (* asp case *)
    ff; eauto;
    unfold Environment_subset in *;
    intuition.
    unfold manifest_update_env_res, asp_manifest_update, 
      aspid_manifest_update in *; try congruence;
    ff; subst; find_apply_hyp_hyp; break_exists;
    intuition; destEq p0 p;
    repeat find_rewrite; repeat find_injection;
    try rewrite mapC_get_works; eauto; try congruence;
    try match goal with
    | E : ?p0 <> ?p ,
      H1 : map_get ?p0 ?e = ?r1,
      H2 : map_get ?p ?e = ?r2 |- 
      context [map_get ?p0 (map_set ?p ?m ?e)] =>
      erewrite map_distinct_key_rw; eauto
    end;
    eexists; intuition; eauto;
    unfold manifest_subset in *; intuition; simpl in *;
    find_apply_hyp_hyp; eauto;
    try (eapply in_set_add; eauto);
    find_apply_lem_hyp appr_manifest_update_cumul; eauto.
  - simpl in *; ffa;
    eapply IHt;
    [ eapply env_subset_cons_none; eauto | eauto ].
Qed.

Lemma manifest_generator_cumul' : forall G t et p e e',
  manifest_generator' G p et t e = resultC e' ->
  Environment_subset e e'.
Proof.
  intros.
  eapply manifest_generator_cumul; eauto;
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
  map_get p e2 = Some m ->
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

Lemma map_get_mangen : forall G t et e e' p p' v,
  map_get p e = Some v ->
  manifest_generator' G p' et t e = resultC e' ->
  exists v',
  map_get p e' = Some v'.
Proof.
  intros;
  find_apply_lem_hyp manifest_generator_cumul';
  unfold Environment_subset in *;
  find_apply_hyp_hyp;
  break_exists; intuition; ff.
Qed.

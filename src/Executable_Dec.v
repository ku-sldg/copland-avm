Require Import Executable_Defs_Prop Executable_Defs_Bool
               Manifest Eqb_Evidence Term_Defs_Core.

Require Import Example_Phrases_Admits Example_Phrases Params_Admits.

Require Import AbstractedTypes Utilities EqClass Maps.


Require Import StructTactics.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.


(*
Set Nested Proofs Allowed.
*)



(* Helper lemma for proving equivalence of propositional vs boolean list membership.  
       TODO:  consider moving this somewhwere else? *)
Lemma existsb_eq_iff_In: forall `{H : EqClass ID_Type} l a,
    existsb (eqb a) l = true <-> In a l.
Proof.
  intros.
  split.
  -
    generalizeEverythingElse l.
    induction l; intros; simpl in *.
    +
      solve_by_inversion.
    +
      find_apply_lem_hyp Bool.orb_prop.
      destruct H0.
      ++
        left.
        symmetry.
        apply eqb_leibniz.
        eassumption.
      ++
        right.
        eauto.
  -
    generalizeEverythingElse l.
    induction l; intros; simpl in *.
    +
      solve_by_inversion.
    +
      destruct H0.
      ++
        subst.
        assert (eqb a0 a0 = true).
        {
          apply eqb_leibniz.
          auto.
        }
        find_rewrite.
        eauto.
      ++
        assert (existsb (eqb a0) l = true) by eauto.
        find_rewrite.
        simpl.
 
        apply Bool.orb_true_r.
Qed.

Lemma canRunAsp_Manifest_prop_iff_bool : forall e a,
    canRunAsp_ManifestB e a = true <-> canRunAsp_Manifest e a.
Proof.
  intros.
  split.
  - (* -> case *)
    unfold canRunAsp_Manifest.
    unfold canRunAsp_ManifestB.
    destruct e.
    destruct a.
    intros.
    find_apply_lem_hyp andb_prop.
    destruct_conjs.
    split.
    + 
      eapply existsb_eq_iff_In.
      eassumption.
    + unfold can_measure_target_prop, can_measure_target in *; simpl in *; 
      eapply existsb_eq_iff_In; eauto.

  - (* <- case *)
    unfold canRunAsp_Manifest.
    unfold canRunAsp_ManifestB.
    destruct e.
    destruct a.
    intros.
    destruct_conjs.
    unfold can_measure_target, can_measure_target_prop in *.
    rewrite <- existsb_eq_iff_In in *; simpl in *.
    eauto with *.
Qed.

Lemma knowsOf_Manifest_prop_iff_bool: forall e a,
    knowsOf_ManifestB e a = true <-> knowsOf_Manifest e a.
Proof.
  intros.
  split;
    unfold knowsOf_Manifest in * ;
    unfold knowsOf_ManifestB in * ;
    apply existsb_eq_iff_In; auto.
Qed.

Lemma knowsPub_Manifest_prop_iff_bool: forall e a,
    knowsPub_ManifestB e a = true <-> knowsPub_Manifest e a.
Proof.
  intros.
  split;
    unfold knowsOf_Manifest in * ;
    unfold knowsOf_ManifestB in * ;
    apply existsb_eq_iff_In; auto.
Qed.

Lemma canRun_aspid_prop_iff_bool : forall m i,
canRun_aspid m i <-> canRun_aspidB m i = true.
Proof.
  intros.
  split;
    unfold canRun_aspid in *;
    unfold canRun_aspidB in *;
    apply existsb_eq_iff_In; auto.
Qed.

Lemma executable_prop_iff_bool : forall t e,
    executableB t e = true <-> executable_local t e.
Proof.
  intros.
  split.
  - (* -> case *)
  generalizeEverythingElse t.
  induction t; intros;

    (* lseq, bseq, bpar cases... *)
    try (
        simpl in *;
        specialize IHt1 with (e:=e);
        specialize IHt2 with (e:=e);
        split;
          try (apply IHt1);
          try (apply IHt2);
          find_apply_lem_hyp andb_prop;
          destruct_conjs;
          eassumption).

  + (* asp case *)
    destruct a; simpl in *; try tauto.
    ++
      rewrite <- canRunAsp_Manifest_prop_iff_bool.
      eauto.
    ++ 
      rewrite canRun_aspid_prop_iff_bool.
      eauto.
    ++
    rewrite canRun_aspid_prop_iff_bool.
    eauto.
    ++
      rewrite <- knowsPub_Manifest_prop_iff_bool.
      eauto.
  + (* at case *)
    simpl in *.
    rewrite <- knowsOf_Manifest_prop_iff_bool.
    eauto.

  - (* <- case *)
    generalizeEverythingElse t.
    induction t; intros;

      (* lseq, bseq, bpar cases... *) 
      try (
          simpl in *;
          specialize IHt1 with (e:=e);
          specialize IHt2 with (e:=e);
          destruct H;
          repeat find_apply_hyp_hyp;
          repeat find_rewrite;
          tauto).

    + (* asp case *)
      destruct a; simpl in *; try tauto.
      ++
        rewrite canRunAsp_Manifest_prop_iff_bool.
        eauto.
      ++
        rewrite <- canRun_aspid_prop_iff_bool.
        eauto.
      ++
        rewrite <- canRun_aspid_prop_iff_bool.
        eauto.
      ++
        rewrite knowsPub_Manifest_prop_iff_bool.
        eauto.
    + (* at case *)
      simpl in *.
      rewrite knowsOf_Manifest_prop_iff_bool.
      eauto.
Qed.


Theorem executable_dec : forall t e, {executable_local t e} + {~ executable_local t e}.
Proof.
  intros.
  destruct (executableB t e) eqn:H.
  -
    left.
    rewrite <- executable_prop_iff_bool.
    eassumption.
  -
    right.
    rewrite <- executable_prop_iff_bool.
    rewrite H.
    auto.
Qed.
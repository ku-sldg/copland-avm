Require Import Term_Defs.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Bool.Bool.
Require Import PeanoNat.


Definition eq_evidence_dec:
  forall x y: Evidence, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality.
Defined.
Hint Resolve eq_evidence_dec : core.

Scheme Equality for list.

Lemma eqb_eq_list {A:Type}:
  forall x y f,
    list_beq A f x y = true <-> x = y.
Admitted.

Fixpoint eqb_evidence (e:Evidence) (e':Evidence): bool :=
  match (e,e') with
  | (mt,mt) => true
  | (uu i args p tid e1, uu i' args' p' tid' e2) =>
    (Nat.eqb i i') && (list_beq nat Nat.eqb args args') && (Nat.eqb p p')
    && (Nat.eqb tid tid') && (eqb_evidence e1 e2)
  | (gg p e1, gg p' e2) =>
    (Nat.eqb p p') && (eqb_evidence e1 e2)
  | (hh p e1, hh p' e2) =>
    (Nat.eqb p p') && (eqb_evidence e1 e2)
  | (nn i, nn i') =>
    (Nat.eqb i i') (*&& (eqb_evidence e1 e2) *)
  | (ss e1 e2, ss e1' e2') =>
    (eqb_evidence e1 e1') && (eqb_evidence e2 e2')
  | (pp e1 e2, pp e1' e2') =>
    (eqb_evidence e1 e1') && (eqb_evidence e2 e2')
  | _ => false
  end.

Lemma eqb_eq_evidence: forall e1 e2,
    eqb_evidence e1 e2 = true <-> e1 = e2.
Proof.
  intros.
  split.
  -
    generalizeEverythingElse e1.
    induction e1; destruct e2; intros;
      try (cbn in *; try solve_by_inversion; eauto; tauto).
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      rewrite eqb_eq_list in H3.

      apply EqNat.beq_nat_true in H1.
      apply EqNat.beq_nat_true in H2.
      apply EqNat.beq_nat_true in H.
      subst.
      specialize IHe1 with e2.
      concludes.
      congruence.
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      apply EqNat.beq_nat_true in H.
      specialize IHe1 with e2.
      concludes.
      congruence.
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      apply EqNat.beq_nat_true in H.
      specialize IHe1 with e2.
      concludes.
      congruence.
    +
      cbn in *.
      (*rewrite Bool.andb_true_iff in H. *)
      destruct_conjs.
      apply EqNat.beq_nat_true in H.
      (*specialize IHe1 with e2.  
      concludes. *)
      congruence.
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      
      specialize IHe1_1 with e2_1.
      specialize IHe1_2 with e2_2.
      concludes.
      concludes.
      congruence.
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      
      specialize IHe1_1 with e2_1.
      specialize IHe1_2 with e2_2.
      concludes.
      concludes.
      congruence.
  -
    generalizeEverythingElse e1.
    induction e1; destruct e2; intros;
      try (cbn in * ; try solve_by_inversion; eauto; tauto).
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split.
      split.
      split.
      split.
      apply Nat.eqb_refl.

      rewrite eqb_eq_list.
      auto.
      apply Nat.eqb_refl.
      apply Nat.eqb_refl.
      eauto.
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split.
      apply Nat.eqb_refl.
      eauto.
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split.
      apply Nat.eqb_refl.
      eauto.
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      (*split. *)
      apply Nat.eqb_refl.
      (*
      eauto. *)
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split;
        eauto.
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split;
      eauto. 
Defined.

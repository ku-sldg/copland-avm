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

Lemma list_beq_refl {A:Type}: forall f y,
    (forall a b, f a b = true <-> a = b) ->
    list_beq A f y y = true.
 Proof.
   intros.
   generalizeEverythingElse y.
   induction y; intros.
   -
     cbn.
     tauto.
   -
     cbn.
     eapply andb_true_intro.
     split.
     +
       eapply H; eauto.
     +
       eauto.
 Defined.

Lemma eqb_eq_list {A:Type}:
  forall x y f,
    (forall a b, f a b = true <-> a = b) ->
    list_beq A f x y = true <-> x = y.
Proof.
  intros.
  generalizeEverythingElse x.
  induction x; destruct y; intros.
  -
    cbn in *.
    split; tauto.
  -
    cbn in *.
    split;
      intros;
      solve_by_inversion.
  -
    cbn in *.
    split; intros;
      solve_by_inversion.
  -
    cbn in *.
    split; intros.
    +
      assert (f a a0 = true /\ list_beq A f x y = true).
      {
        eapply andb_true_iff.
        eassumption.
      }
      destruct_conjs.
      
      edestruct IHx with (y:= y).
      assert (x = y).
      {
        eapply IHx.
        split; intros.
        eapply H.
        eassumption.
        specialize H with (a:=a1) (b:=b).
        inversion H.
        eapply H5. eassumption.
        eassumption.
      }
      intros.
      split; intros.
      specialize H with (a:=a1) (b:=b).
      invc H.
      eapply H5; eauto.
      subst.
      specialize H with (a:=b) (b:=b).
      invc H.
      eapply H4; eauto.
      

      assert (a = a0).
      {
        
      
        concludes.
        eapply H.
        eassumption.
      }
      subst.
      assert (x = y).
      {
        eapply IHx.
        eassumption.
        eassumption.
      }
      congruence.
    +
      invc H0.
      eapply andb_true_intro.
      split.
      eapply H.
      reflexivity.
      eapply list_beq_refl; eauto.
Defined.

Fixpoint eqb_evidence (e:Evidence) (e':Evidence): bool :=
  match (e,e') with
  | (mt,mt) => true
  | (uu (asp_paramsC i args p tid) q e1, uu (asp_paramsC i' args' p' tid') q' e2) =>
    (Nat.eqb i i') && (list_beq nat Nat.eqb args args') && (Nat.eqb p p') && (Nat.eqb q q')
    && (Nat.eqb tid tid') && (eqb_evidence e1 e2)
  | (gg p e1, gg p' e2) =>
    (Nat.eqb p p') && (eqb_evidence e1 e2)
  | (hh p e1, hh p' e2) =>
    (Nat.eqb p p') && (eqb_evidence e1 e2)
  | (nn i, nn i') => (Nat.eqb i i')
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
      try (cbn in *; repeat break_match; try solve_by_inversion; eauto).
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      rewrite eqb_eq_list in H4.

      apply EqNat.beq_nat_true in H1.
      apply EqNat.beq_nat_true in H2.
      apply EqNat.beq_nat_true in H3.
      apply EqNat.beq_nat_true in H.
      subst.
      specialize IHe1 with e2.
      concludes.
      congruence.
     
      (*
EqNat.beq_nat_refl: forall n : nat, true = (n =? n)
Nat.eqb_refl: forall x : nat, (x =? x) = true
       *)
      simpl.
      intros.
      split; intros.
      eapply Nat.eqb_eq; eauto.
      subst.
      (*
      Search ((_ =? _) = true).
       *)
      
      (*
Nat.eqb_refl: forall x : nat, (x =? x) = true
EqNat.beq_nat_true: forall n m : nat, (n =? m) = true -> n = m
Nat.eqb_eq: forall n m : nat, (n =? m) = true <-> n = m
       *)
      
      eapply Nat.eqb_refl.
      
      
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
      try (cbn in * ; repeat break_match; try solve_by_inversion; eauto).
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split.
      split.
      split.
      split.
      split.
      apply Nat.eqb_refl.

      rewrite eqb_eq_list.
      auto.
      eapply Nat.eqb_eq.
      apply Nat.eqb_refl.
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

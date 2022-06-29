Require Import Term_Defs.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Bool.Bool.
Require Import PeanoNat.

(*
Set Nested Proofs Allowed.
 *)


Definition eqb_aspid: ASP_ID -> ASP_ID -> bool.
Admitted.

Lemma eqb_eq_aspid: forall i1 i2,
    eqb_aspid i1 i2 = true <-> i1 = i2.
Admitted.


(* eqb Copland phrase terms *)

Definition eqb_asp_params: ASP_PARAMS -> ASP_PARAMS -> bool.
Admitted.

Definition eq_asp_params_dec:
  forall x y: ASP_PARAMS, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; repeat (decide equality).
Defined.

Lemma eqb_asp_params_true_iff: forall a a0,
    eqb_asp_params a a0 = true <->
    a = a0.
Proof.
Admitted.

(*
(* Duplicate below *)
Definition eq_evidence_dec:
  forall x y: Evidence, {x = y} + {x <> y}.
Proof.
Admitted.
*)

Definition eq_ev_dec:
  forall x y: Ev, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality;
    try (apply eq_arg_dec).
Defined.
Hint Resolve eq_ev_dec : core.







(* eqb Copland evidence terms *)
Definition eq_evidence_dec:
  forall x y: Evidence, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality;
  apply eq_arg_dec.
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

Print Evidence.

Fixpoint eqb_evidence (e:Evidence) (e':Evidence): bool :=
  match (e,e') with
  | (mt,mt) => true
                (*
  | (uu (*i args tpl tid tet*) params q e1,
     uu (*i' args' tpl' tid' tet'*) params' q' e2) =>
    (eqb_asp_params params params') && 
    (Nat.eqb q q') &&
    (eqb_evidence e1 e2)
*)
  | (gg p params e1, gg p' params' e2) =>
    (Nat.eqb p p') && (eqb_asp_params params params') && (eqb_evidence e1 e2)
  | (hh p params e1, hh p' params' e2) =>
    (Nat.eqb p p') && (eqb_asp_params params params') && (eqb_evidence e1 e2)
  | (nn i, nn i') => (Nat.eqb i i')
  | (ss e1 e2, ss e1' e2') =>
    (eqb_evidence e1 e1') && (eqb_evidence e2 e2')
                               (*
  | (pp e1 e2, pp e1' e2') =>
    (eqb_evidence e1 e1') && (eqb_evidence e2 e2') *)
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
      
      apply EqNat.beq_nat_true in H.
      eauto.





    
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      (*
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H. *)
      destruct_conjs.
      (*
      rewrite eqb_eq_list in H4. *)

      apply EqNat.beq_nat_true in H.
      (*
      apply EqNat.beq_nat_true in H2.
      apply EqNat.beq_nat_true in H3.
      apply EqNat.beq_nat_true in H. *)
      subst.
      specialize IHe1 with e2.
      concludes.
      assert (a = a0).
      {
        erewrite <- eqb_asp_params_true_iff.
        eassumption.
      }
            
      congruence.

      (*
     
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
       *)
      
      
      
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      apply EqNat.beq_nat_true in H.
      specialize IHe1 with e2.
      concludes.
      rewrite eqb_asp_params_true_iff in H1.
      congruence.

      (*
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
      congruence. *)
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      
      specialize IHe1_1 with e2_1.
      specialize IHe1_2 with e2_2.
      concludes.
      concludes.
      congruence.

      (*
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      
      specialize IHe1_1 with e2_1.
      specialize IHe1_2 with e2_2.
      concludes.
      concludes.
      congruence. *)
  -
    generalizeEverythingElse e1.
    induction e1; destruct e2; intros;
      try (cbn in * ; repeat break_match; try solve_by_inversion; eauto).
    +
      invc H.
      apply Nat.eqb_refl.
    
      



(*
    
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split.
      split.
      (*
      split.
      split.
      split. *)

      erewrite eqb_asp_params_true_iff.
      tauto.
      
      apply Nat.eqb_refl.
      (*

      rewrite eqb_eq_list.
      auto.
      eapply Nat.eqb_eq.
      apply Nat.eqb_refl.
      apply Nat.eqb_refl.
      apply Nat.eqb_refl. *)
      eauto.

 *)
      
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split. split.
      apply Nat.eqb_refl.
      erewrite eqb_asp_params_true_iff. tauto.
      
      eauto.
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split. split.
      apply Nat.eqb_refl.
      erewrite eqb_asp_params_true_iff. tauto.
      eauto.
      (*
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      (*split. *)
      apply Nat.eqb_refl.
      (*
      eauto. *)
       *)
      
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split;
        eauto.

      (*
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split;
      eauto.  *)
Defined.

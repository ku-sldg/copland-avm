Require Import Term_Defs.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Bool.Bool.
Require Import PeanoNat.

(*
Set Nested Proofs Allowed.
 *)


Definition eqb_aspid (a1 a2 : ASP_ID) : bool :=
  String.eqb a1 a2.

(** Admitted Lemmas relating boolean to propositional equality for 
   ASP ID and PARAMS *)
Lemma eqb_eq_aspid: forall i1 i2,
    eqb_aspid i1 i2 = true <-> i1 = i2.
Proof.
  intros.
  destruct (eqb_aspid i1 i2) eqn:E.
  - split; auto. intros. unfold eqb_aspid in E.
    rewrite String.eqb_eq in E. auto.
  - split; try congruence. intros.
    unfold eqb_aspid in E. rewrite String.eqb_neq in E.
    congruence.
Qed.

Open Scope list.

Fixpoint eqb_list_args (a1 a2 : list Arg) : bool :=
  match a1, a2 with
  | h1 :: t1, h2 :: t2 => andb (String.eqb h1 h2) (eqb_list_args t1 t2)
  | nil, nil => true
  | _, _ => false
  end.

Close Scope list.


Lemma eqb_list_args_true_iff : forall a1 a2,
    eqb_list_args a1 a2 = true <->
    a1 = a2.
Proof.
  split; intros.
  - generalize dependent a2.
    induction a1; simpl; intros.
    * destruct a2; auto; try congruence.
    * destruct a2; auto; try congruence.
      rewrite andb_true_iff in H. destruct_conjs.
      rewrite String.eqb_eq in H. subst. 
      apply IHa1 in H0. subst. auto.
  - subst. induction a2; auto. 
    simpl; rewrite IHa2. rewrite String.eqb_refl. auto.
Qed.

Definition eqb_asp_params (ap1 ap2 : ASP_PARAMS) : bool :=
  match ap1, ap2 with
  | (asp_paramsC a1 la1 p1 t1), (asp_paramsC a2 la2 p2 t2) =>
      andb (eqb_aspid a1 a2) 
        (andb (eqb_list_args la1 la2)
          (andb (Nat.eqb p1 p2) 
                (String.eqb t1 t2)))
  end.

(** Decidable equality proofs for various Copland datatypes *)
Definition eq_asp_params_dec:
  forall x y: ASP_PARAMS, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; repeat (decide equality).
Defined.

Lemma eqb_eq_asp_params: forall a a0,
    eqb_asp_params a a0 = true <->
    a = a0.
Proof.
  split; intros; pose proof (eq_asp_params_dec a a0) as HD.
  - destruct HD; auto. 
    unfold eqb_asp_params in H.
    destruct a, a0. 
    repeat rewrite andb_true_iff in H.
    destruct_conjs.
    rewrite String.eqb_eq in *. subst.
    rewrite Nat.eqb_eq in *. subst.
    rewrite eqb_list_args_true_iff in *. subst.
    reflexivity.
  - subst. unfold eqb_asp_params.
    destruct a0. 
    repeat rewrite andb_true_iff.
    repeat split.
    * unfold eqb_aspid. rewrite String.eqb_eq. auto.
    * apply eqb_list_args_true_iff. auto.
    * rewrite Nat.eqb_eq. auto.
    * rewrite String.eqb_eq. auto.
Qed.


Definition eq_ev_dec:
  forall x y: Ev, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality;
    try (apply eq_arg_dec).
Defined.
#[local] Hint Resolve eq_ev_dec : core.

Definition eq_evidence_dec:
  forall x y: Evidence, {x = y} + {x <> y}.
Proof.
  intros;
    repeat decide equality;
  apply eq_arg_dec.
Defined.
#[local] Hint Resolve eq_evidence_dec : core.


(** list equality Lemmas *)
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

Definition eqb_fwd (fwd1 fwd2 : FWD) : bool.
Admitted.

Lemma eqb_eq_fwd: forall f1 f2,
    eqb_fwd f1 f2 = true <->
    f1 = f2.
Proof.
Admitted.

(** Boolean equality for Evidence Types *)
Fixpoint eqb_evidence (e:Evidence) (e':Evidence): bool :=
  match (e,e') with
  | (mt,mt) => true
                (*
  | (gg p params e1, gg p' params' e2) =>
    (Nat.eqb p p') && (eqb_asp_params params params') && (eqb_evidence e1 e2)
  | (hh p params e1, hh p' params' e2) =>
    (Nat.eqb p p') && (eqb_asp_params params params') && (eqb_evidence e1 e2)
                 *)
  | (uu p fwd params e1, uu p' fwd' params' e2) =>
    (Nat.eqb p p') && (eqb_fwd fwd fwd') && (eqb_asp_params params params') && (eqb_evidence e1 e2)
  | (nn i, nn i') => (Nat.eqb i i')
  | (ss e1 e2, ss e1' e2') =>
    (eqb_evidence e1 e1') && (eqb_evidence e2 e2')
  | _ => false
  end.


(**  Lemma relating boolean to propositional equality for Evidence Types *)
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
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      apply EqNat.beq_nat_true in H.
      specialize IHe1 with e2.
      concludes.
      rewrite eqb_eq_asp_params in H1.
      rewrite eqb_eq_fwd in H2.
      congruence.


(*
      
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      apply EqNat.beq_nat_true in H.
      subst.
      specialize IHe1 with e2.
      concludes.
      assert (a = a0).
      {
        erewrite <- eqb_eq_asp_params.
        eassumption.
      }       
      congruence.  
      
    +
      cbn in *.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      apply EqNat.beq_nat_true in H.
      specialize IHe1 with e2.
      concludes.
      rewrite eqb_eq_asp_params in H1.
      congruence.
*)


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
      apply Nat.eqb_refl.
      
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split. split. split.
      apply Nat.eqb_refl.
      rewrite eqb_eq_fwd. tauto.
      erewrite eqb_eq_asp_params. tauto.
      eauto.
      (*
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split. split.
      apply Nat.eqb_refl.
      erewrite eqb_eq_asp_params. tauto.
      eauto. *)
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split;
        eauto.
Defined.

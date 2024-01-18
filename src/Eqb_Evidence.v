(* Boolean and Propositional equality definitions and lemmas for core Copland 
    datatypes, manily Evidence.  Includes decidability of equality lemmas.
*) 

Require Import AbstractedTypes EqClass Term_Defs.

Require Import StructTactics.

Require Import Coq.Program.Tactics.
Require Import PeanoNat.

(*
Set Nested Proofs Allowed.
 *)


Definition eqb_aspid `{H : EqClass ID_Type} (a1 a2 : ASP_ID)  : bool :=
  eqb a1 a2.

(** Admitted Lemmas relating boolean to propositional equality for 
   ASP ID and PARAMS *)
Lemma eqb_eq_aspid: forall `{H : EqClass ID_Type} i1 i2,
    eqb_aspid i1 i2 = true -> i1 = i2.
Proof.
  unfold eqb_aspid.
  destruct H. eapply eqb_leibniz.
Qed.

Definition eqb_plc `{H : EqClass ID_Type} (a1 a2 : Plc)  : bool :=
  eqb a1 a2.

(** Admitted Lemmas relating boolean to propositional equality for 
   ASP ID and PARAMS *)
Lemma eqb_eq_plc: forall `{H : EqClass ID_Type} i1 i2,
    eqb_plc i1 i2 = true <-> i1 = i2.
Proof.
  intros.
  split; eapply eqb_leibniz.
Qed.

Definition eqb_asp_params `{H : EqClass ID_Type} `{H : EqClass (list ID_Type)} (ap1 ap2 : ASP_PARAMS) : bool :=
  match ap1, ap2 with
  | (asp_paramsC a1 la1 p1 t1), (asp_paramsC a2 la2 p2 t2) =>
      andb (eqb_aspid a1 a2) 
        (andb (eqb la1 la2)
          (andb (eqb p1 p2) 
                (eqb t1 t2)))
  end.

(** Decidable equality proofs for various Copland datatypes *)

Definition eq_plc_dec `{H : EqClass ID_Type} :
  forall x y: Plc, {x = y} + {x <> y}.
Proof.
  intros.
  (* try decide equality; subst; *)
  eapply EqClass_impl_DecEq; eauto.
Defined.

Definition eq_aspid_dec `{H : EqClass ID_Type} :
  forall x y: ASP_ID, {x = y} + {x <> y}.
Proof.
  intros.
  (* try decide equality; subst; *)
  eapply EqClass_impl_DecEq; eauto.
Defined.



Definition eq_asp_params_dec `{H : EqClass ID_Type} :
  forall x y: ASP_PARAMS, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; subst;
  eapply EqClass_impl_DecEq; eauto.
  eapply EqClass_extends_to_list; eauto.
Defined.

Lemma eqb_eq_asp_params: forall `{H : EqClass ID_Type} a a0 ,
    eqb_asp_params a a0 = true <->
    a = a0.
Proof.
  induction a; destruct a0; simpl;
  repeat (rewrite Bool.andb_true_iff);
  repeat split; eauto; try inv H0;
  try rewrite eqb_leibniz; eauto;
  try (eapply EqClass_extends_to_list; eauto).
  - intros; destruct_conjs; subst.
    repeat (rewrite eqb_leibniz in *); subst.
    eapply general_list_eqb_leibniz in H1; subst; eauto.
  - eapply eqb_leibniz; eauto.
Qed.

Global Instance EqClassASP_PARAMS `{H : EqClass ID_Type} : EqClass ASP_PARAMS := {
  eqb := eqb_asp_params ;
  eqb_leibniz := eqb_eq_asp_params
}.

Definition eq_evidence_dec : forall `{H : EqClass ID_Type},
  forall x y : Evidence, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; subst;
  try (try eapply EqClass_impl_DecEq; eauto;
  try eapply nat_EqClass; eauto; fail).
  - eapply eq_asp_params_dec.
  - destruct f, f0; eauto; right; intros HC; congruence.
Qed.

Definition eq_term_dec : forall `{H : EqClass ID_Type},
  forall x y : Term, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; subst;
  try (try eapply EqClass_impl_DecEq; eauto;
  try eapply nat_EqClass; eauto; fail).
  - destruct a, a0; eauto; try (right; intros HC; congruence).
    * destruct (eq_asp_params_dec a a0); subst; eauto;
      destruct s, s0, f, f0; eauto; try (right; intros HC; congruence).
    * destruct (@EqClass_impl_DecEq Plc H p p0); subst; eauto.
      right; intros HC; congruence.
  - destruct s, s0, s, s1, s0, s2; eauto; try (right; intros HC; congruence).
  - destruct s, s0, s, s1, s0, s2; eauto; try (right; intros HC; congruence).
Qed.

Definition eq_core_term_dec : forall `{H : EqClass ID_Type},
  forall x y : Core_Term, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; subst;
  try (try eapply EqClass_impl_DecEq; eauto;
  try eapply nat_EqClass; eauto; fail).
  - destruct a, a0; eauto; try (right; intros HC; congruence).
    * destruct (eq_asp_params_dec a a0); subst; eauto;
      destruct f, f0; eauto; try (right; intros HC; congruence).
  - eapply eq_term_dec.
Qed.

Definition eq_ev_dec: forall `{H : EqClass ID_Type},
  forall x y: Ev, {x = y} + {x <> y}.
Proof.
  intros;
  decide equality; subst;
  try (try eapply EqClass_impl_DecEq; eauto;
  try eapply nat_EqClass; 
  try eapply EqClassASP_Params; eauto; fail).
  repeat decide equality; subst;
  try (try eapply EqClass_impl_DecEq; eauto;
  try eapply nat_EqClass; eauto; fail).
  - eapply eq_asp_params_dec.
  - eapply eq_evidence_dec.
  - eapply eq_term_dec.
  - eapply eq_evidence_dec.
  - eapply eq_evidence_dec.
  - eapply eq_core_term_dec.
Qed.
#[local] Hint Resolve eq_ev_dec : core.

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
        eapply Bool.andb_true_iff.
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
Fixpoint eqb_evidence `{H : EqClass ID_Type} (e:Evidence) (e':Evidence): bool :=
  match (e,e') with
  | (mt,mt) => true
  | (uu p fwd params e1, uu p' fwd' params' e2) =>
    (eqb_plc p p') && (eqb_fwd fwd fwd') && (eqb_asp_params params params') && (eqb_evidence e1 e2)
  | (nn i, nn i') => (eqb i i')
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
    + rewrite Nat.eqb_eq in H; eauto.
    + cbn in *.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      rewrite Bool.andb_true_iff in H.
      destruct_conjs.
      rewrite eqb_eq_plc in H.
      (* rewrite eqb_leibniz in H. *)
      
      specialize IHe1 with e2.
      concludes.
      rewrite eqb_eq_asp_params in H1.
      rewrite eqb_eq_fwd in H2.
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
    + invc H. rewrite Nat.eqb_eq; eauto.
    + invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split. split. split. 
      * eapply eqb_eq_plc; auto.
        (* eapply eqb_leibniz; eauto. *)
      * rewrite eqb_eq_fwd. tauto.
      * erewrite eqb_eq_asp_params. tauto.
      * eauto.
    +
      invc H.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split;
        eauto.
Defined.


Lemma eqb_plc_refl : forall p0, Eqb_Evidence.eqb_plc p0 p0 = true.
Proof.
  intros. apply eqb_eq_plc. auto.
Qed.  
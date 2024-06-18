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

(*
(* Assumed equality for identifiers.  TODO:  complete this impl. *)
Global Instance Eq_Class_Resource_ID_Arg_Type : EqClass Resource_ID_Arg. Admitted.
*)

Definition eqb_asp_params `{H : EqClass ID_Type} (ap1 ap2 : ASP_PARAMS) : bool :=
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
  eapply pair_EqClass.
Defined.

Lemma eqb_eq_asp_params `{H : EqClass ID_Type} : forall  a a0 ,
    eqb_asp_params a a0 = true <->
    a = a0.
Proof.
  intuition; subst; eauto;
  unfold eqb_asp_params in *;
  repeat match goal with
  | a : ASP_PARAMS |- _ => destruct a
  end;
  repeat rewrite Bool.andb_true_iff in *;
  intuition; repeat rewrite eqb_leibniz in *;
  subst; eauto;
  eapply eqb_leibniz; eauto.
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
  - destruct f, f0; eauto; try (right; intros HC; congruence).
    destEq n n0; eauto; try (right; intros HC; congruence).
Qed.

Definition eqb_evidence `{H : EqClass ID_Type} (x y : Evidence): bool :=
  if @eq_evidence_dec H x y then true else false.

Lemma eqb_leibniz_evidence `{H : EqClass ID_Type} : forall x y,
  eqb_evidence x y = true <-> x = y.
Proof.
  unfold eqb_evidence; intuition; 
  destruct eq_evidence_dec; eauto; congruence.
Qed.

Global Instance EqClass_Evidence `{H : EqClass ID_Type} : EqClass Evidence := {
  eqb := eqb_evidence ;
  eqb_leibniz := eqb_leibniz_evidence
}.

Definition eq_term_dec : forall `{H : EqClass ID_Type},
  forall x y : Term, {x = y} + {x <> y}.
Proof.
  intros.
  decide equality; subst;
  try (try eapply EqClass_impl_DecEq; eauto;
  try eapply nat_EqClass; eauto; fail).
  - destruct a, a0; eauto; try (right; intros HC; congruence).
    * destruct (eq_asp_params_dec a a0); subst; eauto;
      destruct s, s0, f, f0; eauto; try (right; intros HC; congruence);
      destEq n n0; eauto; try (right; intros HC; congruence).
    * destruct (@EqClass_impl_DecEq Plc H p p0); subst; eauto.
      right; intros HC; congruence.
  - destruct s, s0, s, s1, s0, s2; eauto; try (right; intros HC; congruence).
  - destruct s, s0, s, s1, s0, s2; eauto; try (right; intros HC; congruence).
Qed.

Definition eqb_term `{H : EqClass ID_Type} (x y : Term): bool :=
  if @eq_term_dec H x y then true else false.

Lemma eqb_leibniz_term `{H : EqClass ID_Type} : forall x y,
  eqb_term x y = true <-> x = y.
Proof.
  unfold eqb_term; intuition;
  destruct eq_term_dec; eauto; congruence.
Qed.

Global Instance EqClass_Term `{H : EqClass ID_Type} : EqClass Term := {
  eqb := eqb_term ;
  eqb_leibniz := eqb_leibniz_term
}.

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
      destEq n n0; eauto; try (right; intros HC; congruence).
  - eapply eq_term_dec.
Qed.

Definition eqb_core_term `{H : EqClass ID_Type} (x y : Core_Term): bool :=
  if @eq_core_term_dec H x y then true else false.

Lemma eqb_leibniz_core_term `{H : EqClass ID_Type} : forall x y,
  eqb_core_term x y = true <-> x = y.
Proof.
  unfold eqb_core_term; intuition;
  destruct eq_core_term_dec; eauto; congruence.
Qed.

Global Instance EqClass_Core_Term `{H : EqClass ID_Type} : EqClass Core_Term := {
  eqb := eqb_core_term ;
  eqb_leibniz := eqb_leibniz_core_term
}.

Definition eq_ev_dec: forall `{H : EqClass ID_Type},
  forall x y: Ev, {x = y} + {x <> y}.
Proof.
  intuition; subst; eauto;
  repeat match goal with
  | a : Ev |- _ => destruct a
  end; try (right; intros HC; congruence);
  repeat (break_eqs; [ eauto | right; intros ?; congruence]).
  - destEq n n0; destEq p1 p; destEq p2 p0; 
    try (right; intros ?; congruence); eauto.
  - destEq n n0; destEq p1 p; destEq p2 p0; 
    try (right; intros ?; congruence); eauto.
Qed.
Local Hint Resolve eq_ev_dec : core.

Local Hint Resolve eq_evidence_dec : core.


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

Definition eqb_fwd (fwd1 fwd2 : FWD) : bool :=
  match fwd1, fwd2 with
  | COMP, COMP => true
  | ENCR, ENCR => true
  | (EXTD n), (EXTD n') => eqb n n'
  | KILL, KILL => true
  | KEEP, KEEP => true
  | _ , _ => false
  end.

Lemma eqb_eq_fwd: forall f1 f2,
    eqb_fwd f1 f2 = true <->
    f1 = f2.
Proof.
  unfold eqb_fwd; intuition;
  destruct f1, f2; eauto; try congruence.
  - rewrite Nat.eqb_eq in H; eauto. 
  - find_injection; rewrite eqb_leibniz; eauto.
Qed.

(* NOTE: Better impl above 
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
Lemma eqb_eq_evidence `{H: EqClass Arg} `{H1: EqClass (list Arg)} `{H2 : EqClass Resource_ID_Arg}: forall e1 e2,
    eqb_evidence e1 e2 = true <-> e1 = e2.
Proof.
  
  intros.
  split.
  -
    generalizeEverythingElse e1.
    induction e1; destruct e2; intros;
      try (cbn in *; repeat break_match; try solve_by_inversion; eauto).
    + rewrite Nat.eqb_eq in H0; eauto.
    + cbn in *.
      rewrite Bool.andb_true_iff in H0.
      rewrite Bool.andb_true_iff in H0.
      rewrite Bool.andb_true_iff in H0.
      destruct_conjs.
      rewrite eqb_eq_plc in H0.
      rewrite eqb_eq_fwd in H5.
      rewrite eqb_eq_asp_params in H4.
      (* rewrite eqb_leibniz in H. *)
      
      specialize IHe1 with H H2 e2.
      concludes.
      eapply IHe1 in H3.
      congruence.

    +
      cbn in *.
      rewrite Bool.andb_true_iff in H0.
      destruct_conjs.
      specialize IHe1_1 with H H2 e2_1.
      specialize IHe1_2 with H H2 e2_2.
      repeat concludes; try congruence.

  -
    generalizeEverythingElse e1.
    induction e1; destruct e2; intros;
      try (cbn in * ; repeat break_match; try solve_by_inversion; eauto).
    + invc H0. rewrite Nat.eqb_eq; eauto.
    + invc H0.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split. split. split. 
      * eapply eqb_eq_plc; auto.
        (* eapply eqb_leibniz; eauto. *)
      * rewrite eqb_eq_fwd. tauto.
      * erewrite eqb_eq_asp_params. tauto.
      * eauto.
    +
      invc H0.
      cbn in *.
      repeat rewrite Bool.andb_true_iff.
      split;
        eauto.
Defined.
*)

Lemma eqb_plc_refl : forall p0, Eqb_Evidence.eqb_plc p0 p0 = true.
Proof.
  intros; apply eqb_eq_plc; auto.
Qed.  
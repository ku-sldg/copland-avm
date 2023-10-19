Require Import AbstractedTypes Term_Defs_Core Maps String
  Term_Defs Manifest_Admits EqClass ErrorStMonad_Coq.

Require Import Example_Phrases_Admits.

Require Import List.
Import ListNotations.

Definition manifest_set (A : Type) := list A.

Definition manifest_set_empty {A : Type} : manifest_set A := nil.

Fixpoint manset_add {A : Type} `{HA : EqClass A} (a : A) (s : manifest_set A) : manifest_set A :=
  match s with
  | nil => a :: nil
  | h :: t =>
    if eqb a h
    then h :: t
    else h :: manset_add a t
  end.

Fixpoint list_to_manset {A : Type} `{HA : EqClass A} (l : list A) : manifest_set A :=
  match l with
  | nil => nil
  | h :: t => manset_add h (list_to_manset t)
  end.

Definition filter_manset {A : Type} (f : A -> bool) (s : manifest_set A) : manifest_set A :=
  filter f s.

Definition is_empty_manset {A : Type} (s:manifest_set A) : bool :=
  match s with
  | nil => true
  | _ => false
  end.

Lemma manempty_is_empty {A : Type} : is_empty_manset (@manifest_set_empty A) = true.
Proof. auto. Qed.

Definition In_set {A : Type} (a : A) (s : manifest_set A) : Prop :=
  In a s.

Definition in_dec_set {A : Type} `{HA : EqClass A} (a : A) (s : manifest_set A) : {In_set a s} + {~ In_set a s} :=
  in_dec (EqClass_impl_DecEq A) a s.

Lemma In_set_empty_contra {A : Type} : forall (a : A) (P : Prop),
  In_set a manifest_set_empty -> P.
Proof.
  intros a P Contra. inversion Contra.
Qed.

Lemma manadd_In_set {A : Type} `{HA : EqClass A}: forall (s : manifest_set A) i j,
  In_set i (manset_add j s) ->
  i = j \/ In_set i s.
Proof.
  intros s i j H. generalize dependent j. generalize dependent i. induction s;
  intros; simpl in H; intuition.
  - destruct (eqb j a).
    + intuition.
    + simpl in *. destruct H.
      * subst. simpl. eauto.
      * simpl. apply IHs in H. destruct H; eauto.
Qed.

Lemma manadd_In_add {A : Type} `{HA : EqClass A} : forall (s : manifest_set A) i,
  In_set i (manset_add i s).
Proof.
  intros. induction s.
  - simpl; auto.
  - simpl.
    destruct (eqb i a) eqn:Eia.
    + rewrite eqb_leibniz in Eia. subst; simpl; auto.
    + simpl; auto.
Qed.

Lemma in_set_add {A : Type} `{HA : EqClass A} : forall (s : manifest_set A) i j,
  In_set i s ->
  In_set i (manset_add j s).
Proof.
  intros s i j H. induction s.
  - simpl; auto.
  - simpl. destruct (eqb j a).
    + subst; simpl; auto.
    + simpl; simpl in H. destruct H; auto.
Qed.

Definition existsb_set {A:Type} (f : A -> bool) (s: manifest_set A) : bool :=
  existsb f s.

Definition existsb_eq_iff_In_set: forall (s : manifest_set ID_Type) (a : ID_Type),
  existsb_set (eqb a) s = true <-> In_set a s.
Proof.
  split; intros H.
  - induction s.
    + inversion H.
    + simpl in H. simpl. destruct (eqb a a0) eqn:Eaa0.
      * rewrite eqb_leibniz in Eaa0; auto.
      * right. apply IHs. simpl in H; auto.
  - induction s.
    + inversion H.
    + simpl in *. destruct (eqb a a0) eqn:Eaa0; auto.
      * simpl. apply IHs. destruct H; auto.
        -- subst. rewrite eqb_refl in Eaa0. congruence.
Qed.

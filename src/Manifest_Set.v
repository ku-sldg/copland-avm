Require Import AbstractedTypes Term_Defs_Core Maps String
  Term_Defs Manifest_Admits (* EqClass *) ErrorStMonad_Coq.

(* Require Import Example_Phrases_Admits. *)

Require Import List.
Import ListNotations.

Definition manifest_set (A : Type) := list A.

Definition manifest_set_empty {A : Type} : manifest_set A := nil.

Fixpoint manset_add (* {A : Type} `{HA : EqClass A} *) (a : nat) (s : manifest_set nat) : manifest_set nat :=
  match s with
  | nil => a :: nil
  | h :: t =>
    if Nat.eqb a h
    then s
    else h :: manset_add a t
  end.

Fixpoint manset_add_plcAsp (* {A : Type} `{HA : EqClass A} *) (a : (Plc * ASP_ID)) (s : manifest_set (Plc * ASP_ID)) : manifest_set (Plc * ASP_ID) :=
  match s with
  | nil => a :: nil
  | h :: t =>
    if plcAsp_pair_beq a h
    then s
    else h :: manset_add_plcAsp a t
  end.

Lemma manset_add_not_nil (* {A : Type} `{HA : EqClass A} *) (a : nat) (s : manifest_set nat) :
  manset_add a s <> nil.
Proof.
  intro. induction s.
  - simpl in *; congruence.
  - simpl in *. destruct (Nat.eqb a a0) eqn:E; congruence.
Qed.

Fixpoint list_to_manset' (* {A : Type} `{HA : EqClass A} *) (l : list nat) : manifest_set nat :=
  match l with
  | nil => nil
  | h :: t => manset_add h (list_to_manset' t)
  end.

Definition list_to_manset (* {A : Type} `{HA : EqClass A} *) (l : list nat) : manifest_set nat :=
  rev (list_to_manset' l).

Definition filter_manset (* {A : Type} *) (f : nat -> bool) (s : manifest_set nat) : manifest_set nat :=
  filter f s.

Definition is_empty_manset (* {A : Type} *) (s:manifest_set nat) : bool :=
  match s with
  | nil => true
  | _ => false
  end.

Lemma manempty_is_empty (*{A : Type} *) : is_empty_manset (@manifest_set_empty nat) = true.
Proof. auto. Qed.

Definition In_set_nat (* {A : Type} *) (a : nat) (s : manifest_set nat) : Prop :=
  In a s.


Definition In_set_plcAsp (* {A : Type} *) (a : (Plc*ASP_ID)) (s : manifest_set (Plc*ASP_ID)) : Prop :=
    In a s.


Lemma in_dec_set_nat (* {A : Type} `{HA : EqClass A} *) (a : nat) (s : manifest_set nat) : {In_set_nat a s} + {~ In_set_nat a s}.
Admitted.
(* in_dec (EqClass_impl_DecEq nat) a s. *)

Definition in_dec_set_nat_bool (* {A : Type} `{HA : EqClass A} *) (a : nat) (s : manifest_set nat) : bool := true.

Lemma in_dec_set_plc_asp_pair (* {A : Type} `{HA : EqClass A} *) (a : (Plc*ASP_ID)) (s : manifest_set (Plc*ASP_ID)) : {In_set_plcAsp a s} + {~ In_set_plcAsp a s}.
Admitted.

Definition in_dec_set_plc_asp_pair_bool (* {A : Type} `{HA : EqClass A} *) (a : (Plc*ASP_ID)) (s : manifest_set (Plc*ASP_ID)) : bool := true.

Lemma In_set_empty_contra (* {A : Type} *) : forall (a : nat) (P : Prop),
  In_set_nat a manifest_set_empty -> P.
Proof.
  intros a P Contra. inversion Contra.
Qed.

Lemma manadd_In_set (* {A : Type} `{HA : EqClass A} *) : forall (s : manifest_set nat) i j,
  In_set_nat i (manset_add j s) ->
  i = j \/ In_set_nat i s.
Proof.
  intros s i j H. generalize dependent j. generalize dependent i. induction s;
  intros; simpl in H; intuition.
  - destruct (Nat.eqb j a).
    + intuition.
    + simpl in *. destruct H.
      * subst. simpl. eauto.
      * simpl. apply IHs in H. destruct H; eauto.
Qed.

Lemma manadd_In_add (* {A : Type} `{HA : EqClass A} *) : forall (s : manifest_set nat) i,
  In_set_nat i (manset_add i s).
Proof.
Admitted.
(*
  intros. induction s.
  - simpl; auto.
  - simpl.
    destruct (Nat.eqb i a) eqn:Eia.
    + rewrite eqb_leibniz in Eia. subst; simpl; auto.
    + simpl; auto.
Qed.
*)

Lemma in_set_add (* {A : Type} `{HA : EqClass A} *) : forall (s : manifest_set nat) i j,
  In_set_nat i s ->
  In_set_nat i (manset_add j s).
Proof.
  intros s i j H. induction s.
  - simpl; auto.
  - simpl. destruct (Nat.eqb j a).
    + subst; simpl; auto.
    + simpl; simpl in H. destruct H; auto.
Qed.

Lemma in_list_to_set (* {A : Type} `{HA : EqClass A} *) : forall (a: nat) (l : list nat),
  In a l <-> In_set_nat a (list_to_manset l).
Proof.
  split; intros H; induction l; auto.
  - simpl in *. destruct H as [H | H].
    + subst. apply -> in_rev. apply manadd_In_add.
    + apply -> in_rev. simpl. apply in_set_add. apply in_rev. intuition.
  - simpl in *. apply <- in_rev in H. simpl in H.
    apply manadd_In_set in H. destruct H as [H | H]; auto.
    apply -> in_rev in H. auto.
Qed.

Definition existsb_set (* {A:Type} *) (f : nat -> bool) (s: manifest_set nat) : bool :=
  existsb f s.

Lemma existsb_eq_iff_In_set: forall (s : manifest_set ID_Type) (a : ID_Type),
  existsb_set (Nat.eqb a) s = true <-> In_set_nat a s.
Proof.
Admitted.
(*
  split; intros H.
  - induction s.
    + inversion H.
    + simpl in H. simpl. destruct (Nat.eqb a a0) eqn:Eaa0.
      * rewrite eqb_leibniz in Eaa0; auto.
      * right. apply IHs. simpl in H; auto.
  - induction s.
    + inversion H.
    + simpl in *. destruct (Nat.eqb a a0) eqn:Eaa0; auto.
      * simpl. apply IHs. destruct H; auto.
        -- subst. rewrite eqb_refl in Eaa0. congruence.
Qed.
*)

Lemma nodup_manset_add (* {A : Type} `{HA : EqClass A} *) (a : nat) (s : manifest_set nat) :
  NoDup s ->
  NoDup (manset_add a s).
Proof.
Admitted.
(*
  intro H. induction s; simpl.
  - constructor. auto. constructor.
  - destruct (Nat.eqb a a0) eqn:Eaa0; eauto.
    + constructor.
      * intro H0. inversion H. subst.
        assert (a <> a0) by (intro HC; apply eqb_leibniz in HC; congruence).
        apply manadd_In_set in H0. intuition.
      * inversion H; auto.
Qed.
*)

Lemma nodup_list_to_manset (* {A : Type} `{HA : EqClass A} *) (l : list nat) :
  NoDup (list_to_manset l).
Proof.
  induction l; simpl.
  - constructor.
  - apply NoDup_rev. simpl. apply nodup_manset_add.
    apply NoDup_rev in IHl. unfold list_to_manset in IHl. rewrite rev_involutive in IHl.
    auto.
Qed.

Lemma manset_add_result (* {A : Type} `{HA : EqClass A} *) (a : nat) (s : manifest_set nat) :
  manset_add a s = s \/ manset_add a s = app s (a :: nil).
Proof.
Admitted.
(*
  generalize dependent a. induction s.
  - right. simpl. auto.
  - intros. destruct (IHs a0) as [H | H];
      destruct (Nat.eqb a a0) eqn:E;
        simpl; rewrite eqb_symm in E; rewrite E; try rewrite H; auto.
Qed. 
*)

Lemma manset_add_same_dup (* {A : Type} `{HA : EqClass A} *) (a : nat) (s : manifest_set nat) :
  manset_add a s = s -> In_set_nat a s /\ ~NoDup (a::s).
Proof.
Admitted.
(*
  split.
  - generalize dependent a. induction s; intros a0 H.
    + inversion H.
    + simpl in H. destruct (eqb a0 a) eqn:E.
      * apply eqb_leibniz in E. simpl. auto.
      * simpl. injection H. intros H0. apply IHs in H0. right. auto.
  - generalize dependent a. induction s; intros a0 H.
    + inversion H.
    + simpl in H. destruct (eqb a0 a) eqn:E.
      * apply eqb_leibniz in E. subst. intro H0. inversion H0.
        simpl in H3. intuition.
      * injection H. intro H0. pose proof (IHs a0 H0) as H1. intro H2. apply H1.
        inversion H2 as [H2' | x l H3 H4]. subst. intuition.
        assert (G: (a0 :: a :: s = app (a0 :: nil) (a :: s))) by reflexivity.
        rewrite G in H2. apply NoDup_remove_1 in H2. simpl in H2. auto.
Qed.
*)

Lemma nodup_preserves_manset (* {A : Type} `{HA : EqClass A} *) (l : list nat) :
  NoDup l -> list_to_manset l = l.
Proof.
  intros. induction l; auto.
  - inversion H; subst; intuition.
    unfold list_to_manset.
    assert (list_to_manset' l = rev l).
    {
       unfold list_to_manset in H0. rewrite <- H0. rewrite rev_involutive. rewrite H0. auto.
    }
    simpl. rewrite H1.
    destruct (manset_add_result a (rev l)).
    + apply manset_add_same_dup in H4. intuition. apply in_rev in H5. congruence.
    + replace (a :: l) with (rev (rev (a :: l))) by (rewrite rev_involutive; eauto).
      f_equal. simpl. auto.
Qed.

Fixpoint manset_union (* {A : Type} `{HA : EqClass A} *) (a b : manifest_set nat) : manifest_set nat :=
  match b with
  | nil => a
  | h :: t => (*manset_union t (manset_add h b)*)
              manset_union (manset_add h a) t
  end.

Fixpoint manset_union_plcAsp (* {A : Type} `{HA : EqClass A} *) (a b : manifest_set (Plc * ASP_ID)) : manifest_set (Plc * ASP_ID) :=
  match b with
  | nil => a
  | h :: t => (*manset_union t (manset_add h b)*)
              manset_union_plcAsp (manset_add_plcAsp h a) t
  end.

Lemma manset_add_not_in (* {A : Type} `{HA : EqClass A} *) (a : nat) (s : manifest_set nat) :
  ~In_set_nat a s -> manset_add a s = s ++ [a].
Proof.
Admitted.
(*
  intros. induction s; auto.
  - simpl. simpl in H. intuition.
    destruct (eqb a a0) eqn:E.
    + apply eqb_leibniz in E. symmetry in E. intuition.
    + rewrite H. auto.
Qed.
*)

Lemma NoDup_app_single (* {A : Type} *) (a : nat) (a0 : list nat) :
  NoDup (a0 ++ [a]) <-> NoDup (a :: a0).
Proof.
  split.
  - induction a0; auto.
    intros. rewrite <- app_comm_cons in H.
    inversion H; subst; intuition.
    constructor.
    + intro. simpl in H1. destruct H1.
      * subst. auto with *.
      * inversion H0; subst; intuition.  
    + constructor.
      * intro. auto with *.
      * inversion H0; auto.
  - induction a0; auto.
    intros. simpl. constructor.
    + intro. inversion H; subst; auto.
      apply in_app_or in H0; destruct H0.
      * inversion H4; subst; auto.
      * simpl in H0. destruct H0; auto. subst. simpl in H3. intuition.
    + apply IHa0. apply NoDup_cons_iff. inversion H; subst; auto.
      inversion H3; subst; auto. simpl in H2; subst; auto.
Qed.


Theorem exclusive_set_unification (* {A : Type} `{HA : EqClass A} *) (a b : manifest_set nat) :
  NoDup a -> NoDup b ->
  (forall x, In_set_nat x a -> ~In_set_nat x b) -> (forall y, In_set_nat y b -> ~In_set_nat y a) ->
  manset_union a b = a ++ b.
Proof.
  intros. generalize dependent a. induction b; intros.
  - induction a; auto. simpl. rewrite app_nil_r. auto.
  - simpl. pose proof (H2 a). rewrite manset_add_not_in by (apply H3; simpl; auto).
    assert (a :: b = [a] ++ b) by auto.
    rewrite H4. rewrite app_assoc.
    apply IHb.
    + inversion H0; auto.
    + simpl in H3; intuition. apply NoDup_app_single. constructor; auto.
    + intuition. apply in_app_or in H5; intuition.
      * unfold In_set_nat in *. pose proof (H2 x); auto with *.
      * simpl in H7. destruct H7; subst; auto. inversion H0; subst; auto.
    + intuition. apply in_app_or in H6; intuition.
      * unfold In_set_nat in *. pose proof (H1 y); auto with *.
      * simpl in H7. destruct H7; subst; auto; inversion H0; subst; auto.
Qed.

Lemma manset_union_nil_r (* {A : Type} `{HA : EqClass A} *) (s : manifest_set nat) :
  NoDup s ->
  manset_union [] s = s.
Proof.
  intros. apply exclusive_set_unification; auto. constructor.
Qed.

Lemma manset_union_nil_l (* {A : Type} `{HA : EqClass A} *) (s : manifest_set nat) :
  manset_union s [] = s.
Proof.
  auto.
Qed.

Theorem nodup_manset_union (* {A : Type} `{HA : EqClass A} *) (a b : manifest_set nat) :
  NoDup a ->
  NoDup (manset_union a b).
Proof.
  generalize dependent a. induction b; intros; auto.
  - simpl. auto using nodup_manset_add.
Qed.

Theorem union_inclusion_l (* {A : Type} `{HA : EqClass A} *) (a b : manifest_set nat) :
  forall x, In_set_nat x a -> In_set_nat x (manset_union a b).
Proof.
  generalize dependent a. induction b; intros; auto.
  - simpl. apply (in_set_add _ _ a) in H. auto.
Qed.

Theorem union_inclusion_r (* {A : Type} `{HA : EqClass A} *) (a b : manifest_set nat) :
  forall y, In_set_nat y b -> In_set_nat y (manset_union a b).
Proof.
  generalize dependent a. induction b; intros; auto.
  - inversion H.
  - simpl. apply in_inv in H. destruct H; subst; auto.
    + apply union_inclusion_l. apply manadd_In_add.
Qed.

Lemma union_inclusion (* {A : Type} `{HA : EqClass A} *) (a b : manifest_set nat) :
  forall z, In_set_nat z a \/ In_set_nat z b <-> In_set_nat z (manset_union a b).
Proof.
Admitted.
(*
  split; intros.
  - intuition; auto using union_inclusion_l, union_inclusion_r.
  - generalize dependent a. induction b; intros; auto.
    simpl in H; apply IHb in H; destruct H; auto with *.
    + apply manadd_In_set in H; destruct H; subst; auto with *.       
Qed.
*)
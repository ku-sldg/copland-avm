(* Definition of the manifest_set datatype, its operations, and related properties.  
    This datatype is used for "collection" manifest fields, and should act like a 
    traditional mathematical set (e.g. cumulative, non-duplicating, ...) *)
Require Import List.

Require Import ID_Type 
  JSON.

Import ListNotations.

Definition manifest_set (A : Type) := list A.

Definition manifest_set_empty {A : Type} : manifest_set A := nil.

Fixpoint manset_add {A : Type} `{HA : EqClass A} (a : A) (s : manifest_set A) : manifest_set A :=
  match s with
  | nil => a :: nil
  | h :: t =>
    if eqb a h
    then s
    else h :: manset_add a t
  end.

Lemma manset_add_not_nil {A : Type} `{HA : EqClass A} (a : A) (s : manifest_set A) :
  manset_add a s <> nil.
Proof.
  intuition; induction s; simpl in *; try congruence; eauto;
  break_eqs; congruence.
Qed.

Fixpoint list_to_manset' {A : Type} `{HA : EqClass A} (l : list A) : manifest_set A :=
  match l with
  | nil => nil
  | h :: t => manset_add h (list_to_manset' t)
  end.

Definition list_to_manset {A : Type} `{HA : EqClass A} (l : list A) : manifest_set A :=
  rev (list_to_manset' l).

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
  intuition; invc H.
Qed.

Lemma manadd_In_set {A : Type} `{HA : EqClass A}: forall (s : manifest_set A) i j,
  In_set i (manset_add j s) ->
  i = j \/ In_set i s.
Proof.
  induction s; simpl in *; intuition; eauto;
  break_eqs; eauto; simpl in *; intuition; eauto;
  find_eapply_hyp_hyp; intuition; eauto.
Qed.

Lemma manadd_In_add {A : Type} `{HA : EqClass A} : forall (s : manifest_set A) i,
  In_set i (manset_add i s).
Proof.
  induction s; simpl in *; intuition; eauto;
  break_eqs; simpl in *; intuition.
Qed.

Lemma in_set_add {A : Type} `{HA : EqClass A} : forall (s : manifest_set A) i j,
  In_set i s ->
  In_set i (manset_add j s).
Proof.
  induction s; simpl in *; intuition; eauto;
  break_eqs; simpl in *; intuition; eauto.
Qed.

Lemma in_list_to_set {A : Type} `{HA : EqClass A} : forall (a: A) (l : list A),
  In a l <-> In_set a (list_to_manset l).
Proof.
  split; intros H; induction l; auto.
  - simpl in *. destruct H as [H | H].
    + subst. apply -> in_rev. apply manadd_In_add.
    + apply -> in_rev. simpl. apply in_set_add. apply in_rev. intuition.
  - simpl in *. apply <- in_rev in H. simpl in H.
    apply manadd_In_set in H. destruct H as [H | H]; auto.
    apply -> in_rev in H. auto.
Qed.

Definition existsb_set {A:Type} (f : A -> bool) (s: manifest_set A) : bool :=
  existsb f s.

Definition existsb_eq_iff_In_set: forall (s : manifest_set ID_Type) (a : ID_Type),
  existsb_set (eqb a) s = true <-> In_set a s.
Proof.
  intuition; simpl in *; unfold existsb_set, In_set in *; simpl in *;
  rewrite existsb_exists in *;
  [destruct H | exists a]; intuition; 
  rewrite String.eqb_eq in *; subst; eauto.
Qed.

Lemma nodup_manset_add {A : Type} `{HA : EqClass A} (a : A) (s : manifest_set A) :
  NoDup s ->
  NoDup (manset_add a s).
Proof.
  intro H. induction s; simpl.
  - constructor. auto. constructor.
  - destruct (eqb a a0) eqn:Eaa0; eauto.
    + constructor.
      * intro H0. inversion H. subst.
        assert (a <> a0) by (intro HC; apply eqb_eq in HC; congruence).
        apply manadd_In_set in H0. intuition.
      * inversion H; auto.
Qed.

Lemma nodup_list_to_manset {A : Type} `{HA : EqClass A} (l : list A) :
  NoDup (list_to_manset l).
Proof.
  induction l; simpl.
  - constructor.
  - apply NoDup_rev. simpl. apply nodup_manset_add.
    apply NoDup_rev in IHl. unfold list_to_manset in IHl. rewrite rev_involutive in IHl.
    auto.
Qed.

Lemma manset_add_result {A : Type} `{HA : EqClass A} (a : A) (s : manifest_set A) :
  manset_add a s = s \/ manset_add a s = app s (a :: nil).
Proof.
  generalize dependent a. induction s.
  - right. simpl. auto.
  - intros. destruct (IHs a0) as [H | H];
      destruct (eqb a a0) eqn:E;
        simpl; rewrite eqb_symm in E; rewrite E; try rewrite H; auto.
Qed. 

Lemma manset_add_same_dup {A : Type} `{HA : EqClass A} (a : A) (s : manifest_set A) :
  manset_add a s = s -> In_set a s /\ ~NoDup (a::s).
Proof.
  split.
  - generalize dependent a. induction s; intros a0 H.
    + inversion H.
    + simpl in H. destruct (eqb a0 a) eqn:E.
      * apply eqb_eq in E. simpl. auto.
      * simpl. injection H. intros H0. apply IHs in H0. right. auto.
  - generalize dependent a. induction s; intros a0 H.
    + inversion H.
    + simpl in H. destruct (eqb a0 a) eqn:E.
      * apply eqb_eq in E. subst. intro H0. inversion H0.
        simpl in H3. intuition.
      * injection H. intro H0. pose proof (IHs a0 H0) as H1. intro H2. apply H1.
        inversion H2 as [H2' | x l H3 H4]. subst. intuition.
        assert (G: (a0 :: a :: s = app (a0 :: nil) (a :: s))) by reflexivity.
        rewrite G in H2. apply NoDup_remove_1 in H2. simpl in H2. auto.
Qed.

Lemma nodup_preserves_manset {A : Type} `{HA : EqClass A} (l : list A) :
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

Fixpoint manset_union {A : Type} `{HA : EqClass A} (a b : manifest_set A) : manifest_set A :=
  match b with
  | nil => a
  | h :: t => (*manset_union t (manset_add h b)*)
              manset_union (manset_add h a) t
  end.

Lemma manset_add_not_in {A : Type} `{HA : EqClass A} (a : A) (s : manifest_set A) :
  ~In_set a s -> manset_add a s = s ++ [a].
Proof.
  intros. induction s; auto.
  - simpl. simpl in H. intuition.
    destruct (eqb a a0) eqn:E.
    + apply eqb_eq in E. symmetry in E. intuition.
    + rewrite H. auto.
Qed.

Lemma NoDup_app_single {A : Type} (a : A) (a0 : list A) :
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


Theorem exclusive_set_unification {A : Type} `{HA : EqClass A} (a b : manifest_set A) :
  NoDup a -> NoDup b ->
  (forall x, In_set x a -> ~In_set x b) -> (forall y, In_set y b -> ~In_set y a) ->
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
      * unfold In_set in *. pose proof (H2 x); auto with *.
      * simpl in H7. destruct H7; subst; auto. inversion H0; subst; auto.
    + intuition. apply in_app_or in H6; intuition.
      * unfold In_set in *. pose proof (H1 y); auto with *.
      * simpl in H7. destruct H7; subst; auto; inversion H0; subst; auto.
Qed.

Lemma manset_union_nil_r {A : Type} `{HA : EqClass A} (s : manifest_set A) :
  NoDup s ->
  manset_union [] s = s.
Proof.
  intros. apply exclusive_set_unification; auto. constructor.
Qed.

Lemma manset_union_nil_l {A : Type} `{HA : EqClass A} (s : manifest_set A) :
  manset_union s [] = s.
Proof.
  auto.
Qed.

Theorem nodup_manset_union {A : Type} `{HA : EqClass A} (a b : manifest_set A) :
  NoDup a ->
  NoDup (manset_union a b).
Proof.
  generalize dependent a. induction b; intros; auto.
  - simpl. auto using nodup_manset_add.
Qed.

Theorem union_inclusion_l {A : Type} `{HA : EqClass A} (a b : manifest_set A) :
  forall x, In_set x a -> In_set x (manset_union a b).
Proof.
  generalize dependent a. induction b; intros; auto.
  - simpl. apply (in_set_add _ _ a) in H. auto.
Qed.

Theorem union_inclusion_r {A : Type} `{HA : EqClass A} (a b : manifest_set A) :
  forall y, In_set y b -> In_set y (manset_union a b).
Proof.
  generalize dependent a. induction b; intros; auto.
  - inversion H.
  - simpl. apply in_inv in H. destruct H; subst; auto.
    + apply union_inclusion_l. apply manadd_In_add.
Qed.

Lemma union_inclusion {A : Type} `{HA : EqClass A} (a b : manifest_set A) :
  forall z, In_set z a \/ In_set z b <-> In_set z (manset_union a b).
Proof.
  split; intros.
  - intuition; auto using union_inclusion_l, union_inclusion_r.
  - generalize dependent a. induction b; intros; auto.
    simpl in H; apply IHb in H; destruct H; auto with *.
    + apply manadd_In_set in H; destruct H; subst; auto with *.       
Qed.

Fixpoint manifest_set_to_list_JSON {A :Type} `{Stringifiable A} 
    `{EqClass A} (m : manifest_set A) : list JSON :=
  match m with
  | nil => []
  | h :: t => 
    (JSON_String (to_string h)) :: (manifest_set_to_list_JSON t)
  end.

Fixpoint list_JSON_to_manifest_set {A :Type} `{Stringifiable A} `{EqClass A}
    (l : list JSON) : ResultT (manifest_set A) string :=
  match l with
  | nil => resultC []
  | h :: t => 
    match h with
    | JSON_String s =>
      match (list_JSON_to_manifest_set t) with
      | resultC t' => 
          match (from_string s) with
          (* TODO: This should really use a safer add, but man sets arent guarded inductively so in proofs the fact is lost for resolution *)
          | resultC h' => resultC (h' :: t')
          | errC e => errC e
          end
      | errC e => errC e
      end
    | _ => errC "list_JSON_to_manifest_set: Invalid JSON type in manifest set, only can handle strings."%string
    end
  end.

Lemma canonical_list_injson_to_manset {A : Type} `{Stringifiable A} `{EqClass A} (m : manifest_set A) :
  list_JSON_to_manifest_set (manifest_set_to_list_JSON m) = resultC m.
Proof.
  induction m; simpl in *; intuition; eauto;
  find_rewrite; rewrite canonical_stringification in *; simpl in *; eauto.
Qed.

Fixpoint manifest_set_pairs_to_list_JSON {A B : Type} `{Stringifiable A} 
    `{Stringifiable B} (m : manifest_set (A * B)) : list JSON :=
  match m with
  | [] => []
  | h :: t => (to_JSON h) :: (manifest_set_pairs_to_list_JSON t)
  end.

Fixpoint list_JSON_to_manifest_set_pairs {A B :Type} `{Stringifiable A} 
    `{Stringifiable B} `{EqClass A} `{EqClass B}
    (l : list JSON) : ResultT (manifest_set (A * B)) string :=
  match l with
  | nil => resultC []
  | h :: t => 
    match (from_JSON h) with
    | resultC h' =>
      match (list_JSON_to_manifest_set_pairs t) with
      (* TODO: Same here as above, we would like to use add but it doesnt have all we need *)
      | resultC t' => resultC (h' :: t')
      | errC e => errC e
      end
    | errC e => errC e
    end
  end.

Lemma canonical_list_injson_to_manset_pairs {A B : Type} `{Stringifiable A, Stringifiable B} `{EqClass A, EqClass B} (m : manifest_set (A * B)) :
  list_JSON_to_manifest_set_pairs (manifest_set_pairs_to_list_JSON m) = resultC m.
Proof.
  induction m; simpl in *; intuition; eauto;
  find_rewrite; repeat rewrite canonical_stringification in *; simpl in *; eauto.
Qed.
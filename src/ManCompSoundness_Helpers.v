(*  Helper Lemmas in support of Manifest Compiler Soundness proofs.  *)

Require Import Term_Defs_Core Manifest_Generator_Helpers.
Require Import EqClass.

Require Import StructTactics.

Require Import List.
Import ListNotations.


Lemma places'_cumul : forall t p ls,
    In p ls ->
    In p (places' t ls).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; 
  try (destruct a);
    ff; eauto.
Qed.


Lemma In_dec_tplc : forall (p:Plc) ls,
    In p ls \/ ~ In p ls.
Proof.
  intros.
  assert ({In p ls} + {~ In p ls}) by (apply (In_dec (EqClass_impl_DecEq _))).
  destruct H; eauto.
Qed. 

Lemma places_app_cumul : forall p t ls ls',
  In p (places' t ls) -> 
  ~ In p ls ->
  In p (places' t ls').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; ffa using intuition.
  all: 
  destruct (In_dec_tplc p (places' t1 ls)); ffa;
  eapply places'_cumul; eauto.
Qed.

Lemma top_plc_refl: forall {H : EqClass Plc} t' p1,  In t' (place_terms t' p1 p1).
Proof.
  induction t'; simpl; intuition;
  try erewrite eqb_refl in *; simpl; eauto.
Qed.

Lemma app_not_empty : forall A (l1 l2:list A),
  l1 ++ l2 <> [] -> 
  l1 <> [] \/ l2 <> [].
Proof.
  intros.
  destruct l1; 
  destruct l2; ff.
  - left; intuition; ff.
  - left; intuition; ff.
Qed.


Lemma places'_cumul' : forall t p ls,
    In p (places' t []) ->
    In p (places' t ls).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; 
  try (destruct a);
  try (ff; try (exfalso; eauto; fail); ff; congruence).

  - (* lseq case *)
    ff.
    
    assert (In p (places' t2 []) \/ In p (places' t1 [])).
    {
      assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
      { 
          apply In_dec_tplc.
      }
      ff.
      +             
        assert (In p (places' t2 [])).
        {
          eapply places_app_cumul.
          apply H.
          eassumption.
        }
        eauto.
    }
    ff.
    +
      assert (In p (places' t1 ls)) by eauto.
      apply places'_cumul.
      eauto.

  - (* bseq case *)
    ff.
    
    assert (In p (places' t2 []) \/ In p (places' t1 [])).
    {
      assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
      { 
          apply In_dec_tplc.
      }
      ff.
      + pose proof places_app_cumul.            
        ff.
    }
    ff.
    pose proof places'_cumul.
    ff.

  - (* bpar case *)
    ff.
    
    assert (In p (places' t2 []) \/ In p (places' t1 [])).
    {
      assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
      { 
          apply In_dec_tplc.
      }
      ff.
      + pose proof places_app_cumul.            
        ff.
    }
    ff.
    pose proof places'_cumul.
    ff.
Qed.


Lemma in_plc_term : forall {HP : EqClass Plc} p p0 t,
  place_terms t p p0 <> [] ->
  In p0 (places p t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; repeat ff; rewrite eqb_eq in *; eauto; try congruence.
  - (* at case *)
    repeat ff; eauto; rewrite eqb_eq in *; eauto.
  - (* lseq case *)
    repeat ff; eauto; repeat rewrite eqb_eq in *; subst; eauto;
    rewrite eqb_neq in *.
      right.

      assert (place_terms t1 p p0 <> [] \/ 
              place_terms t2 p p0 <> []).
              {
                apply app_not_empty.
                eassumption.
              }
      ff; break_or_hyp.
      ++
        apply IHt1 in H1.
        assert (In p0 (places' t1 [])).
        {
          assert (p <> p0).
          {
            eauto.
          }
          ff.
        }

        apply places'_cumul.
        eassumption.
    ++
      apply IHt2 in H1.
      assert (In p0 (places' t2 [])).
      {
        assert (p <> p0) by eauto.
        ff.
      }
      apply places'_cumul'.
      eauto.

  - (* bseq case *)
  repeat ff; eauto; simpl in *;
  repeat rewrite eqb_eq in *; subst; eauto;
  repeat rewrite eqb_neq in *; subst; eauto; ff.
  right.
    assert (place_terms t1 p p0 <> [] \/ 
            place_terms t2 p p0 <> []).
            {
              apply app_not_empty.
              eassumption.
            }
    ff; break_or_hyp.
    ++
      apply IHt1 in H1.
      assert (In p0 (places' t1 [])).
      {
        assert (p <> p0) by eauto.
        ff.
        }
  
        apply places'_cumul.
        eassumption.
    ++
      apply IHt2 in H1.
      assert (In p0 (places' t2 [])).
      {
        assert (p <> p0) by eauto.
        ff.
        }
  
      
            apply places'_cumul'.
            eauto.

  - (* bpar case *)
  repeat ff; eauto; simpl in *;
  repeat rewrite eqb_eq in *; subst; eauto;
  repeat rewrite eqb_neq in *; subst; eauto; ff.
    right.
  
    assert (place_terms t1 p p0 <> [] \/ 
            place_terms t2 p p0 <> []).
            {
              apply app_not_empty.
              eassumption.
            }
    ff; break_or_hyp.
    ++
      apply IHt1 in H1.
      assert (In p0 (places' t1 [])).
      {
        assert (p <> p0) by eauto.
        ff.
        }
  
        apply places'_cumul.
        eassumption.
    ++
      apply IHt2 in H1.
      assert (In p0 (places' t2 [])).
      {
        assert (p <> p0) by eauto.
        ff.
        }
        apply places'_cumul'.
        eauto.
Qed.


Lemma in_not_nil : forall A x (ls:list A),
  In x ls -> 
  ls <> [].
Proof.
  intros; destruct ls; ff.
Qed.
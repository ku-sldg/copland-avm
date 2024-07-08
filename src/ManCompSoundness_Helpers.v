(*  Helper Lemmas in support of Manifest Compiler Soundness proofs.  *)

Require Import Term_Defs_Core Manifest Manifest_Generator Manifest_Generator_Helpers EqClass Manifest_Generator_Facts Manifest_Admits Eqb_Evidence.

Require Import Params_Admits.

Require Import StructTactics Auto.

Require Import Coq.Program.Tactics.

Require Import Coq.Program.Equality.

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
      assert ({In p ls} + {~ In p ls}).
      { 
        apply In_dec.
        intros.
        destruct (eq_plc_dec x y); eauto.
      }
      destruct H; eauto.
Qed. 


Lemma places_app_cumul : forall p t ls ls',
      In p (places' t ls) -> 
      ~ In p ls ->
      In p (places' t ls').
Proof.
      intros.
      generalizeEverythingElse t.
      induction t; intros; ff.
      - (* asp case *)
      congruence.
      - (* at case *)
        door; 
          eauto.
      - (* lseq case *)
        destruct (In_dec_tplc p (places' t1 ls)).
        +
          assert (In p (places' t1 ls')) by eauto.
          apply places'_cumul.
          eassumption.
        +
          assert (In p (places' t2 ls)) by eauto.
          eapply IHt2.
          eassumption.
          eassumption.
    - (* bseq case *)

    destruct (In_dec_tplc p (places' t1 ls)).
    +
      assert (In p (places' t1 ls')) by eauto.
      apply places'_cumul.
      eassumption.
    +
    assert (In p (places' t2 ls)) by eauto.
    eapply IHt2.
    eassumption.
    eassumption.
  - (* bpar case *)

    destruct (In_dec_tplc p (places' t1 ls)).
    +
      assert (In p (places' t1 ls')) by eauto.
      apply places'_cumul.
      eassumption.
    +
      assert (In p (places' t2 ls)) by eauto.
      eapply IHt2.
      eassumption.
      eassumption.
Qed.

Lemma top_plc_refl: forall t' p1,  In t' (place_terms t' p1 p1).
Proof.
  intros.
  unfold place_terms.
  destruct t'; ff; 
    try auto;
    try (rewrite eqb_plc_refl in *; solve_by_inversion).
Qed.

Lemma app_not_empty : forall A (l1 l2:list A),
l1 ++ l2 <> [] -> 
l1 <> [] \/ l2 <> [].
Proof.
  intros.
  destruct l1; 
  destruct l2.
  -
    ff.
    congruence.
  -
  ff.
  -
  ff.
  left.
  unfold not.
  intros.
  congruence.
  -
    ff.
    left.
    congruence.
Qed.


Lemma places'_cumul' : forall t p ls,
    In p (places' t []) ->
    In p (places' t ls).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; 
  try (destruct a);
    try (ff; eauto; ff; congruence).

  - (* lseq case *)
    ff.
    
    assert (In p (places' t2 []) \/ In p (places' t1 [])).
    {
      assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
      { 
          apply In_dec_tplc.
      }
      door.
      +
        eauto.
      +             
        assert (In p (places' t2 [])).
        {
          eapply places_app_cumul.
          apply H.
          eassumption.
        }
        eauto.
    }

    door.
    +
      eauto.
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
      door.
      +
        eauto.
      +             
        assert (In p (places' t2 [])).
        {
          eapply places_app_cumul.
          apply H.
          eassumption.
        }
        eauto.
    }

    door.
    +
      eauto.
    +
      assert (In p (places' t1 ls)) by eauto.
      apply places'_cumul.
      eauto.

  - (* bpar case *)
    ff.
    
    assert (In p (places' t2 []) \/ In p (places' t1 [])).
    {
      assert (In p (places' t1 []) \/ (~ In p (places' t1 []))).
      { 
          apply In_dec_tplc.
      }
      door.
      +
        eauto.
      +             
        assert (In p (places' t2 [])).
        {
          eapply places_app_cumul.
          apply H.
          eassumption.
        }
        eauto.
    }

    door.
    +
      eauto.
    +
      assert (In p (places' t1 ls)) by eauto.
      apply places'_cumul.
      eauto.
Qed.


Lemma in_plc_term : forall p p0 t,
place_terms t p p0 <> [] ->
In p0 (places p t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; repeat ff;
    rewrite String.eqb_eq in *; eauto.
- (* at case *)
  repeat ff; eauto;
  rewrite String.eqb_eq in *; eauto.
- (* lseq case *)
repeat ff.
+
  left.
  rewrite String.eqb_eq in *; eauto.
+
  right.

  assert (place_terms t1 p p0 <> [] \/ 
          place_terms t2 p p0 <> []).
          {
            apply app_not_empty.
            eassumption.
          }
  door.
  ++
    apply IHt1 in H0.
    assert (In p0 (places' t1 [])).
    {
      assert (p <> p0).
      {
        unfold not.
        intros.
        subst.
        rewrite eqb_plc_refl in *.
        solve_by_inversion.
      }
      door; ff.
      congruence. 
      }

      apply places'_cumul.
      eassumption.
  ++
    apply IHt2 in H0.
    assert (In p0 (places' t2 [])).
    {
      assert (p <> p0).
      {
        unfold not.
        intros.
        subst.
        rewrite eqb_plc_refl in *.
        solve_by_inversion.
      }
      door; ff.
      congruence. 
      }
      apply places'_cumul'.
      eauto.

- (* bseq case *)
  repeat ff.
  +
    left.
    rewrite String.eqb_eq in *; eauto.
  +
    right.
  
    assert (place_terms t1 p p0 <> [] \/ 
            place_terms t2 p p0 <> []).
            {
              apply app_not_empty.
              eassumption.
            }
    door.
    ++
      apply IHt1 in H0.
      assert (In p0 (places' t1 [])).
      {
        assert (p <> p0).
        {
          unfold not.
          intros.
          subst.
          rewrite eqb_plc_refl in *.
          solve_by_inversion.
        }
        door; ff.
        congruence. 
        }
  
        apply places'_cumul.
        eassumption.
    ++
      apply IHt2 in H0.
      assert (In p0 (places' t2 [])).
      {
        assert (p <> p0).
        {
          unfold not.
          intros.
          subst.
          rewrite eqb_plc_refl in *.
          solve_by_inversion.
        }
        door; ff.
        congruence. 
        }
  
      
            apply places'_cumul'.
            eauto.

- (* bpar case *)
  repeat ff.
  +
    left.
    rewrite String.eqb_eq in *; eauto.
  +
    right.
  
    assert (place_terms t1 p p0 <> [] \/ 
            place_terms t2 p p0 <> []).
            {
              apply app_not_empty.
              eassumption.
            }
    door.
    ++
      apply IHt1 in H0.
      assert (In p0 (places' t1 [])).
      {
        assert (p <> p0).
        {
          unfold not.
          intros.
          subst.
          rewrite eqb_plc_refl in *.
          solve_by_inversion.
        }
        door; ff.
        congruence. 
        }
  
        apply places'_cumul.
        eassumption.
    ++
      apply IHt2 in H0.
      assert (In p0 (places' t2 [])).
      {
        assert (p <> p0).
        {
          unfold not.
          intros.
          subst.
          rewrite eqb_plc_refl in *.
          solve_by_inversion.
        }
        door; ff.
        congruence. 
        }
        apply places'_cumul'.
        eauto.
Qed.


Lemma in_not_nil : forall A x (ls:list A),
In x ls -> 
ls <> [].
Proof.
  intros.
  destruct ls.
  -
  inversion H.
  -
  congruence.
Qed.
Require Import Term_Defs_Core Manifest Manifest_Generator Manifest_Generator_Facts Executable_Defs_Prop Manifest_Admits Eqb_EvidenceT.

Require Import Params_Admits.

Require Import StructTactics Auto.

Require Import Coq.Program.Tactics.

Require Import Coq.Program.Equality.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)


(*
(* Proof that the dynamic notion of executability respects the static notion of executability. *)
Theorem static_executability_implies_dynamic : 
    forall t p em,
      executable_global t p em -> 
      executable_dynamic t p em.
Proof.
  intros t. induction t; try ( intros; inversion H; specialize IHt1 with p em; specialize IHt2 with p em; simpl; split; auto).
  + intros. destruct a; try (apply I); auto.
  + intros. specialize IHt with p0 em. simpl in *. inversion H. apply H0.
Qed. 
*)

(*
Lemma top_plc_refl: forall t' p1,  In t' (place_terms t' p1 p1).
Proof.
  intros.
  unfold place_terms.
  destruct t'; ff; 
    try auto;
    try (rewrite eqb_plc_refl in *; solve_by_inversion).
Qed.
*)
(*
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
*)

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

(*
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
        door.
        +
          eauto.
        +
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

*)



(*

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
    destruct a; ff.
    +
    destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
      destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
      destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
    destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
    destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
    +
    destruct (eqb_plc p p0) eqn:hi.
      ++
      left.
      rewrite <- eqb_eq_plc.
      eassumption.
      ++
      solve_by_inversion.
- (* at case *)
ff.
destruct (eqb_plc p0 p1) eqn:hi.
+
  left.
  rewrite eqb_eq_plc in *.
  auto.
+
  apply IHt in H.
  door.
  ++
    eauto.
  ++
    eauto.
- (* lseq case *)
ff.
destruct (eqb_plc p p0) eqn:hi.
+
  left.
  rewrite eqb_eq_plc in *.
  auto.
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
  ff.
  destruct (eqb_plc p p0) eqn:hi.
  +
    left.
    rewrite eqb_eq_plc in *.
    auto.
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
  ff.
  destruct (eqb_plc p p0) eqn:hi.
  +
    left.
    rewrite eqb_eq_plc in *.
    auto.
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

*)

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

Lemma dist_exec_lseq : forall p t1 t2 em,
                distributed_executability t1 p em ->
                distributed_executability t2 p em -> 
                distributed_executability (lseq t1 t2) p em.
Proof.
  intros.
  unfold distributed_executability in *; intros.
  destruct_conjs.
  cbn in H2.
                
  destruct (eqb_plc p p0) eqn:hi.
  -
    invc H2; ff.
    door.
    +
      subst.
      edestruct H.
      split.
      left.
      reflexivity.
      apply top_plc_refl.

      edestruct H0.
      split.
      left.
      reflexivity.
      apply top_plc_refl.
      destruct_conjs.
      assert (x = x0) by congruence.
      subst.
      exists x0.
      split; eauto.
  +
  edestruct H.
      split.
      left.
      reflexivity.
      apply top_plc_refl.

      edestruct H0.
      split.
      left.
      reflexivity.
      apply top_plc_refl.
      destruct_conjs.
      assert (x = x0) by congruence.
      subst.
      exists x0.
      split; eauto.
      rewrite eqb_eq_plc in *.
      subst.
      eauto.
  -
    ff.
    assert (In t' (place_terms t1 p p0) \/ 
            In t' (place_terms t2 p p0)).
    {
      apply in_app_or.
      eassumption.
    }
  
    door.
      +

      apply H.
      split.
      right.
      assert (In p0 (places p t1)).
        
      apply in_plc_term.

    eapply in_not_nil; eauto.
      unfold places in H4.
      invc H4.
      rewrite eqb_plc_refl in *; solve_by_inversion.
    
      eassumption.

      eassumption.
  +
  apply H0.
      split.
      right.
      assert (In p0 (places p t2)).
        
      apply in_plc_term.

      eapply in_not_nil; eauto.
      unfold places in H4.
      invc H4.
      rewrite eqb_plc_refl in *; solve_by_inversion.
    
      eassumption.

      eassumption.
Qed.

Lemma dist_exec_bseq : forall p t1 t2 em s,
  distributed_executability t1 p em ->
  distributed_executability t2 p em -> 
  distributed_executability (bseq s t1 t2) p em.
Proof.
  intros.
  unfold distributed_executability in *; intros.
  destruct_conjs.
  cbn in H2.
  
  destruct (eqb_plc p p0) eqn:hi.
  -
    invc H2; ff.
    door.
    +
      subst.
      edestruct H.
      split.
      left.
      reflexivity.
      apply top_plc_refl.

      edestruct H0.
      split.
      left.
      reflexivity.
      apply top_plc_refl.
      destruct_conjs.
      assert (x = x0) by congruence.
      subst.
      exists x0.
      split; eauto.
  +
  edestruct H.
      split.
      left.
      reflexivity.
      apply top_plc_refl.

      edestruct H0.
      split.
      left.
      reflexivity.
      apply top_plc_refl.
      destruct_conjs.
      assert (x = x0) by congruence.
      subst.
      exists x0.
      split; eauto.
      rewrite eqb_eq_plc in *.
      subst.
      eauto.
  -
    ff.
    assert (In t' (place_terms t1 p p0) \/ 
            In t' (place_terms t2 p p0)).
    {
      apply in_app_or.
      eassumption.
    }
  
    door.
      +

      apply H.
      split.
      right.
      assert (In p0 (places p t1)).
        
      apply in_plc_term.

    eapply in_not_nil; eauto.
      unfold places in H4.
      invc H4.
      rewrite eqb_plc_refl in *; solve_by_inversion.
    
      eassumption.

      eassumption.
  +
  apply H0.
      split.
      right.
      assert (In p0 (places p t2)).
        
      apply in_plc_term.

      eapply in_not_nil; eauto.
      unfold places in H4.
      invc H4.
      rewrite eqb_plc_refl in *; solve_by_inversion.
    
      eassumption.

      eassumption.
Qed.

Lemma dist_exec_bpar : forall p t1 t2 em s,
  distributed_executability t1 p em ->
  distributed_executability t2 p em -> 
  distributed_executability (bpar s t1 t2) p em.

Proof.
  intros.
  unfold distributed_executability in *; intros.
  destruct_conjs.
  cbn in H2.
  
  destruct (eqb_plc p p0) eqn:hi.
  -
    invc H2; ff.
    door.
    +
      subst.
      edestruct H.
      split.
      left.
      reflexivity.
      apply top_plc_refl.

      edestruct H0.
      split.
      left.
      reflexivity.
      apply top_plc_refl.
      destruct_conjs.
      assert (x = x0) by congruence.
      subst.
      exists x0.
      split; eauto.
  +
  edestruct H.
      split.
      left.
      reflexivity.
      apply top_plc_refl.

      edestruct H0.
      split.
      left.
      reflexivity.
      apply top_plc_refl.
      destruct_conjs.
      assert (x = x0) by congruence.
      subst.
      exists x0.
      split; eauto.
      rewrite eqb_eq_plc in *.
      subst.
      eauto.
  -
    ff.
    assert (In t' (place_terms t1 p p0) \/ 
            In t' (place_terms t2 p p0)).
    {
      apply in_app_or.
      eassumption.
    }
  
    door.
      +

      apply H.
      split.
      right.
      assert (In p0 (places p t1)).
        
      apply in_plc_term.

    eapply in_not_nil; eauto.
      unfold places in H4.
      invc H4.
      rewrite eqb_plc_refl in *; solve_by_inversion.
    
      eassumption.

      eassumption.
  +
  apply H0.
      split.
      right.
      assert (In p0 (places p t2)).
        
      apply in_plc_term.

      eapply in_not_nil; eauto.
      unfold places in H4.
      invc H4.
      rewrite eqb_plc_refl in *; solve_by_inversion.
    
      eassumption.

      eassumption.
Qed.


(* Proof that the distributed notion of executability respects the static notion of executability. *)
Theorem static_executability_implies_distributed : 
    forall t p em,
      executable_global t p em -> 
      distributed_executability t p em.
Proof.
  intros t.
  induction t; intros.
  - (* asp case *)
    ff.
    destruct a; ff.
    + unfold distributed_executability; intros.
      invc H.
      ff.
      destruct_conjs.
      door; ff; subst.
      exists x.
      split; try eauto.
      door; ff; subst.
      unfold executable_local.
      trivial.
    + unfold distributed_executability; intros.
      invc H.
      ff.
      destruct_conjs.
      door; ff; subst.
      exists x.
      split; try eauto.
      door; ff; subst.
      unfold executable_local.
      trivial.
    + unfold distributed_executability; intros.
      subst.
      ff.
      destruct_conjs.
      door; ff; subst.
      unfold canRunAsp_Env in H.
      ff.
      exists m. 
      split; try eauto.
      door; ff.
      (*
      rewrite <- H0.
      cbn.
      break_let; ff. subst.
      split; try eassumption.
      cbv.
      trivial. *)

      + unfold distributed_executability; intros.
      subst.
      ff.
      destruct_conjs.
      door; ff; subst.
      door; ff; subst.
      unfold canRun_aspid_Env in H.
      ff.
      exists m. 
      split; try eauto.

      + unfold distributed_executability; intros.
      subst.
      ff.
      destruct_conjs.
      door; ff; subst.
      door; ff; subst.
      unfold canRun_aspid_Env in H.
      ff.
      exists m. 
      split; try eauto.

      + unfold distributed_executability; intros.
      subst.
      ff.
      destruct_conjs.
      door; ff; subst.
      door; ff; subst.
      unfold knowsPub_Env in H.
      ff.
      exists m. 
      split; try eauto.
      
  - (* at case *)
    simpl in *.
    invc H.
    assert (distributed_executability t p em) by eauto.

    unfold distributed_executability; intros.

    unfold places in *.
    simpl in *.
    destruct_conjs.

    door.
      +
        subst.
        rewrite eqb_plc_refl in *.
        invc H3; ff.
        unfold knowsOf_Env in *; ff.
        exists m. 
        split; try eauto.
      +
        door.
        ++
          subst.
          destruct (eqb_plc p0 p1) eqn:hi.
          +++
            invc H3; ff.
            assert (p0 = p1).
            {
              apply eqb_eq_plc; auto.
            }
            subst. 
            unfold knowsOf_Env in *; ff.
            exists m.
            split; try eauto.
          +++
            unfold distributed_executability in H.
            apply H.
            unfold places.
            split.
            econstructor.
            auto.
            eassumption.
        ++
          subst.
          destruct (eqb_plc p0 p1) eqn:hi.
          +++
            invc H3; ff.
            assert (p0 = p1).
            {
              apply eqb_eq_plc; auto.
            }
            subst. 
            unfold knowsOf_Env in *; ff.
            exists m.
            split; try eauto.
          +++
            unfold distributed_executability in H.
            apply H.
            unfold places.
            split.
            right.
            eassumption.
            eassumption.
  - (* lseq case *)
    invc H.
    assert (distributed_executability t1 p em) by eauto.
    assert (distributed_executability t2 p em) by eauto.

    

    apply dist_exec_lseq; eauto.

  - (* bseq case *)
  invc H.
  assert (distributed_executability t1 p em) by eauto.
  assert (distributed_executability t2 p em) by eauto.

  

  apply dist_exec_bseq; eauto.

  - (* bpar case *) 
  invc H.
  assert (distributed_executability t1 p em) by eauto.
  assert (distributed_executability t2 p em) by eauto.

  apply dist_exec_bpar; eauto.
  Qed.


(*

Theorem manifest_generator_executability_distributed :
    forall (t:Term) (p:Plc), 
        distributed_executability t p (manifest_generator t p).
Proof.
  intros.
  apply static_executability_implies_distributed.
  apply manifest_generator_executability_static.
Qed.
*)
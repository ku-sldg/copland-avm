Require Import Term_Defs AnnoFacts.
Require Import Preamble StructTactics Term_Facts.

Require Import Coq.Program.Tactics.

Require Import Lia.

Require Import List.
Import List.ListNotations.

Set Nested Proofs Allowed.

Lemma wf_lseq_pieces: forall r lr t1 t2,
    well_formed (alseq r lr t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_at_pieces: forall t r lr locs p,
    well_formed (aatt locs r lr p t) ->
    well_formed_r t.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_bseq_pieces: forall r lr s t1 t2,
    well_formed (abseq r lr s t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_bpar_pieces: forall r lr xlocs ylocs s t1 t2,
    well_formed (abpar r lr xlocs ylocs s t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Ltac do_wf_pieces :=
  match goal with
  | [H: well_formed (alseq _ _ _ _) |- _] =>
    (edestruct wf_lseq_pieces; eauto)
  | [H: well_formed (aatt _ _ _ _ ?t) |- _] =>   
    assert (well_formed t)
      by (eapply wf_at_pieces; eauto)
  | [H: well_formed (abseq _ _ _ _ _) |- _] =>
    (edestruct wf_bseq_pieces; eauto)
  | [H: well_formed (abpar _ _ _ _ _ _ _) |- _] =>
    (edestruct wf_bpar_pieces; eauto)     
  end.

Lemma well_formed_range_r:
  forall t,
    well_formed_r t ->
    snd (range t) = fst (range t) + esize t.
Proof.
    induction t;
    try (intros H; simpl; inv H; simpl;
         repeat find_apply_hyp_hyp; lia).
Defined.

Lemma well_formed_range:
  forall t,
    well_formed t ->
    snd (range t) = fst (range t) + esize t.
Proof.
  induction t;
    try (intros H; simpl; inv H; simpl;
    repeat find_apply_hyp_hyp; lia).
  -
    intros H.
    inv H.
    eapply well_formed_range_r.
    econstructor; eauto.
Defined.

Lemma well_formed_lrange:
  forall t,
    well_formed t ->
    length (lrange t) >= anss t.
Proof.
  induction t; intros H;
    try (simpl; inv H; simpl; repeat concludes; lia).

Lemma esize_nonempty: forall t, esize t > 0.
Proof.
  intros.
  induction t; intros;
    try (destruct a);
    (cbn; lia).
Defined.

Lemma wf_mono: forall t,
    well_formed t ->
    snd (range t) > fst (range t).
Proof.
  intros.
  rewrite well_formed_range.
  pose (esize_nonempty t).
  lia.
  eauto.
Defined.

Lemma anno_subtract: forall t i ls n l0 a,
    anno t i ls true = Some (n, (l0, a)) ->
    length l0 = length ls - (nss t).
Proof.
Admitted.

Lemma anno_full: forall t i l l' n a,
  length l = nss t ->
  anno t i l true = Some (n, (l',a)) ->
  l' = [].
Proof.
  (*
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff;
      assert (l' = []) by (destruct l'; solve_by_inversion);
      subst;
      eauto.
  -
    cbn in *.
    assert (exists x y, l = [x; y]).
    {
      destruct l; try solve_by_inversion.
      invc H.
      destruct l; try solve_by_inversion.
      invc H2.
      assert (l = []) by (destruct l; solve_by_inversion).
      subst.
      eauto.
    }
    destruct_conjs.
    subst.
    ff.
    (*
    +
      eauto.
    +
      exfalso.
      eapply false_succeeds; eauto.
    +
      destruct b;
        ff.
     *)
    
        
  -
    assert (l = lrange a).
    {
      eapply anno_lrange_eq; eauto.
    }

    rewrite H1 in *; clear H1.

    cbn in H0.
    repeat break_match; try solve_by_inversion.
    invc H0.



    assert (length l0 = length (lrange a) - (nss t1)).
    {
      eapply anno_subtract; eauto.
    }

    cbn in H.

    rewrite H in H0.

    assert (length l0 = nss t2) by lia.

    eauto.
  -
    assert (l = lrange a).
    {
      eapply anno_lrange_eq; eauto.
    }

    rewrite H1 in *; clear H1.

    cbn in H0.
    repeat break_match; try solve_by_inversion.
    invc H0.



    assert (length l0 = length (lrange a) - (nss t1)).
    {
      eapply anno_subtract; eauto.
    }

    cbn in H.

    rewrite H in H0.

    assert (length l0 = nss t2) by lia.

    eauto.
  -
    assert (l = lrange a).
    {
      eapply anno_lrange_eq; eauto.
    }

    rewrite H1 in *; clear H1.

    cbn in H0.
    repeat break_match; try solve_by_inversion.
    inv H0.

    cbn in *.
    repeat find_inversion.



    assert (length l0 = length l5 - (nss t1)).
    {
      eapply anno_subtract; eauto.
    }

    cbn in H.

    rewrite H1 in H.

    assert (length l0 = nss t2) by lia.

    eauto.
Defined.
   *)
  Admitted.

    

(*

    

    assert (l' = []) by eauto.
    subst.
    
    

    
    
    ff.

    assert (l = (lrange a0)).

    


    

    



    
    
      assert (length l0 < nss t2).
      {
        eapply list_too_short; eauto.
      }

      assert (length l = anss a + length l0).
      {
        eapply anno_len; eauto.
      }

      assert (nss t1 = anss a).
      {
        eapply nss_iff_anss; eauto.
      }
      lia.
    +
      exfalso.
      eapply false_succeeds; eauto.
    +
      destruct b.
      ++
        assert (length l < nss t1).
        {
          eapply list_too_short; eauto.
        }
        lia.
      ++
        exfalso.
        eapply false_succeeds; eauto.
  -
        ff.
    eauto.
    destruct b.
    +
      assert (length l0 < nss t2).
      {
        eapply list_too_short; eauto.
      }

      assert (length l = anss a + length l0).
      {
        eapply anno_len; eauto.
      }

      assert (nss t1 = anss a).
      {
        eapply nss_iff_anss; eauto.
      }
      lia.
    +
      exfalso.
      eapply false_succeeds; eauto.
    +
      destruct b.
      ++
        assert (length l < nss t1).
        {
          eapply list_too_short; eauto.
        }
        lia.
      ++
        exfalso.
        eapply false_succeeds; eauto.
  -
    ff;
      try (eauto; tauto).
    +
      destruct b.
      ++
        assert (length l0 < nss t2).
        {
          eapply list_too_short; eauto.
        }

        assert (length l4 = anss a + length l0).
        {
          eapply anno_len; eauto.
        }
        assert (nss t1 = anss a).
        {
          eapply nss_iff_anss; eauto.
        }
        lia.
      ++
        exfalso.
        eapply false_succeeds; eauto.
    +
      destruct b.
      ++
        assert (length l3 < nss t1).
        {
          eapply list_too_short; eauto.
        }

        lia.
      ++
        exfalso.
        eapply false_succeeds; eauto.
    +
      destruct b;
        ff.

    +
      destruct b;
        ff.
Defined.

*)





Lemma anno_full_ex: forall t i l,
  length l = nss t ->
  exists n a,
    anno t i l true = Some (n, ([],a)).
Proof.
  (*
  intros.
  edestruct anno_some; eauto.
  destruct_conjs.

  assert (l0 = []).
  {
    eapply anno_full; eauto.
  }

  subst.

  eexists. exists a.

  eassumption.
Defined.
   *)
Admitted.


(*
Lemma anno_full_ex_full: forall t i l l' l'' n a,
    length l = nss t ->
    anno t i l' true = Some (n, (l'',a)) ->
    anno t i l true =  Some (n, ([],a)).
Proof.
Admitted.
*)

Lemma asp_lrange_irrel: forall a i l l' l2 l2' a0 a1 n n' b,
    anno (asp a) i l b = Some (n, (l',a0)) ->
    anno (asp a) i l2 b= Some(n', (l2',a1)) ->
    a0 = a1.
Proof.
  intros.
  destruct a; ff.
Defined.

(*
Lemma lrange_nss: forall t i ls n a,
    anno t i ls true = Some (n, ([], a)) ->
    length (lrange a) = nss t.
Proof.
Admitted.
*)

Lemma anno_sub: forall t i n ls l a,
    length ls = nss t ->
    anno t i ls true = Some (n, (l, a)) ->
    anno t i (lrange a) true = Some (n, ([],a)).
Proof.
  (*

  intros.
  assert (l = []).
  {
    eapply anno_full; eauto.
  }
  subst.

  assert (ls = (lrange a)).
  {
    eapply anno_lrange_eq; eauto.
  }
  subst.
  eauto.
Defined.
   *)
Admitted.


(*
  intros.
  Check anno_some.
  edestruct anno_some with (l:=(lrange a)) (t:=t) (i:=i) (b:=true).
  eapply lrange_nss; eauto.

Admitted.
*)



(*
  
  intros.
  (*
  edestruct anno_some with (l:=(lrange a)) (t:=t) (i:=i) (b:=true).
  eapply lrange_nss; eauto.
  destruct x; destruct p. 
  assert (length (lrange a) = anss a0 + length l0).
  eapply anno_len; eauto.
  assert (length ls = anss a + length l).
  eapply anno_len; eauto.
   *)
  

  (*
  assert (length ls = nss t + (length l)).
  {
    assert (nss t = anss a).
    {
      eapply nss_iff_anss; eauto.
    }
    rewrite H3; clear H3.
    eauto.
  }

  assert (length (lrange a) = nss t + (length l0)).
  {
    assert (nss t = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }
    rewrite H4; clear H4.
    eauto. 
  }
   *)
  


  assert (anss a = nss t).
  {
    symmetry.
    eapply nss_iff_anss; eauto.
  }
  (*
  rewrite H0 in *; clear H0.
   *)

  (*

  assert (anss a0 = nss t).
  {
    symmetry.
    eapply nss_iff_anss; eauto.
  }
  rewrite H3 in *; clear H3.
*)
  
  

  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff.

  
    (*
    
    +
      assert (ls = l) by ff.
      subst.
      assert (lrange a0 = l) by ff.
      subst.
      assert (lrange a0 = []) by ff.
      
      rewrite H3 in *. clear H3.
      ff.
    +
       assert (ls = l) by ff.
      subst.
      assert (lrange a0 = l0) by ff.
      subst.
      assert (lrange a0 = []) by ff.
      
      rewrite H3 in *. clear H3.
      ff.
    +
       assert (ls = l) by ff.
      subst.
      assert (lrange a0 = l0) by ff.
      subst.
      assert (lrange a0 = []) by ff.

      
      rewrite H3 in *. clear H3.
      ff.
    +
       assert (ls = l) by ff.
      subst.
      assert (lrange a0 = l0) by ff.
      subst.
      assert (lrange a0 = []) by ff.
      
      rewrite H3 in *. clear H3.
      ff.
*)
  -
    ff.
  -
    (*

    assert (length l0 = 0).
    {
      assert (length (lrange a) = nss (lseq t1 t2)).
      {
        eapply lrange_nss; eauto.
      }
      ff.
      lia.
    }
    assert (l0 = []) by (destruct l0; try solve_by_inversion).
    subst.
    clear H3.
     *)
    
    
    assert (length l = 0).
    {
       assert (length (lrange a) = nss (lseq t1 t2)).
       {
         admit.
         (*
         rewrite <- H0.
         ff.
         erewrite <- nss_iff_anss.
         Focus 2.
         eassumption.
         
         
        eapply lrange_nss; eauto
          *)

       }

       assert (l = []).
       {
         admit.
       }
       subst.
       tauto.
    }


    assert (l = []).
    {
      admit.
    }
    subst.

    cbn in *.
    clear_refl_eqs.
    ff.
    
    
         
       
       ff.
       
      


    
    ff.

    assert (n3 = n1).
    {
      eapply same_anno_range; eauto.
    }
    subst.
    
    

    assert (n0 = n).
    {
      eapply same_anno_range; eauto.
    }
    subst.

    assert (l2 = l0) by congruence.
    assert (a3 = a1) by congruence.

    assert (l = []) by congruence.
    assert (a4 = a2) by congruence.
    subst.
    eauto.
  -


    assert (length l0 = 0).
    {
      assert (length (lrange a) = nss (bseq s t1 t2)).
      {
        eapply lrange_nss; eauto.
      }
      ff.
      lia.
    }
    assert (l0 = []) by (destruct l0; try solve_by_inversion).
    subst.
    clear H3.

        ff.

    assert (n3 = n1).
    {
      eapply same_anno_range; eauto.
    }
    subst.
    
    

    

    assert (l2 = l0) by congruence.
    assert (a3 = a1) by congruence.

    assert (l = []) by congruence.
    assert (a4 = a2) by congruence.
    subst.
    assert (n2 = n4) by congruence.
    subst.
    eauto.
  -

    assert (length l0 = 0).
    {
      assert (length (lrange a) = nss (bpar s t1 t2)).
      {
        eapply lrange_nss; eauto.
      }
      ff.
      lia.
     
    }
    assert (l0 = []) by (destruct l0; try solve_by_inversion).
    subst.
    clear H3.

    ff.
    assert (n2 = n8) by congruence.
    assert (a1 = a3) by congruence.
    assert (a2 = a4) by congruence.
    subst.
    eauto.
Defined.
*)



(*
Lemma anno_len:
  forall t i j ls ls' t',
    anno t i ls = Some (j, (ls', t')) ->
    length ls = anss t' + length ls'.
 *)

(*
Lemma lrange_nss: forall t i ls n l a,
    anno t i ls = Some (n, (l, a)) ->
    length (lrange a) = nss t.
 *)

(*
Lemma nss_iff_anss: forall t i ls n l a,
    anno t i ls = Some (n, (l, a)) ->
    nss t = anss a.
Proof.
Admitted.
*)


(*
Lemma lrange_len: forall t i ls n l a,
    anno t i ls true = Some (n, (l,a)) ->
    length ls = length (lrange a) + (length l).
Proof.
  intros.
  erewrite lrange_nss.
  Focus 2.
  Check anno_sub.
  eapply anno_sub.
  Focus 2.
  eassumption.
  
  eapply anno_sub; eassumption.

  erewrite nss_iff_anss.
  Focus 2.
  eapply anno_sub; eassumption.
  eapply anno_len; eauto.
Defined.
 *)

Print list_subset.

Example ls_ex: list_subset [5;5] [5].
Proof.
  intros.
  unfold list_subset.
  unfold incl.
  intros.
  econstructor; eauto.
  
  invc H; eauto.
  invc H0; eauto.
  solve_by_inversion.
Qed.


(*
Lemma nodup_sub: forall ls ls':list nat,
    NoDup ls ->
    list_subset ls' ls ->
    NoDup ls'.
Proof.
  intros.
  generalizeEverythingElse H.
  induction H; destruct ls'; intros.
  -
    econstructor.
  -
    unfold list_subset in *.
    pose (H0 n).
    assert (In n []).
    {
      eapply i.
      econstructor; eauto.
    }
    solve_by_inversion.
  -
    econstructor.
  -
    econstructor.
    unfold list_subset in *.
    pose (H1 n).
    unfold not; intros.
    assert (In n (x :: l)).
    {
      eapply i.
      econstructor; eauto.
    }

    invc H3.

    
    
    
    
    
    
    solve_by_inversion.
    
    assert (ls' = []).
    {
      admit.
    }
    subst.
    econstructor.
  -
    unfold list_subset in H1.
    


    
    assert (NoDup (x :: l

    assert (list_subset ls' l).
    {
      
      unfold list_subset in *.
      intros.
      
      
      admit.
    }
    eauto.
    

    
    eapply IHNoDup.

    unfold list_subset in *.
    intros.

    assert (In x0 (x :: l)) by eauto.

    Search ({_} + {_}).
    destruct (PeanoNat.Nat.eq_dec x x0).
    +
      subst.
      invc H3.

    invc H3.
    +
      

    
    
    unfold list_subset in *.
    eapply IHls.
    +
    invc H.
    eauto.
    +
      intros.
      repeat concludes.

      assert (In x (a :: ls)).
      {
        eauto.
      }
      invc H2; eauto.

      assert (In x (x :: ls)) by eauto.
      invc H2; try solve_by_inversion.
      
      
      
    
    
    
      
  unfold list_subset in *.
  Print NoDup.


  
Admitted.
*)






Lemma anno_has_enough:
  forall t i j ls ls' t',
    anno t i ls true = Some (j, (ls', t')) ->
    length ls >= nss t.
Proof.
Admitted.

Lemma nodup_extra_app
  : forall ls ls' ls'' : list nat, NoDup (ls ++ ls') -> NoDup ls.
Proof.
Admitted.


(*
Lemma nodup_extra_app: forall (ls ls' ls'':list nat),
    NoDup (ls ++ ls' ++ ls'') ->
    NoDup (ls ++ ls').
Proof.
  intros.
  rewrite app_assoc in *.
  eapply nodup_extra_app_2; eauto.
Defined.
 *)

Lemma nodup_anno: forall t i ls l n a,
    NoDup ls ->
    anno t i ls true = Some (n, (l, a)) ->
    NoDup l.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.

  -
    destruct a; ff.
  -
    ff.
    


  
Admitted.

Lemma anno_step: forall t i ls l n a,
    anno t i ls true = Some (n, (l, a)) ->
    ls = (lrange a) ++ l.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.

  -
    destruct a; ff.
  -
    ff.
  -
    assert (l = []). admit.
    subst.
    rewrite app_nil_r.
    cbn in *.
    repeat break_match; try solve_by_inversion.

    (*
    subst.
    inv H.
    ff.
    admit.
     *)
    
  -
     cbn in *.
    repeat break_match; try solve_by_inversion.
    subst.
    inv H.
    ff.
    admit.
  -
    ff.
    
    
    
    
    
    


  
Admitted.

Lemma anno_well_formed:
  forall t i j ls ls' t',
    length ls = nss t ->
    NoDup ls ->
    anno t i ls true = Some (j, (ls', t')) ->
    well_formed t'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    ff.
  -
    ff.
    econstructor.
    eapply anno_well_formed_r; eauto.

    simpl.

    erewrite anno_range.
    tauto.
    eassumption.
    simpl.

    erewrite anno_range.
    tauto.
    eassumption.
    simpl.

    assert (n2 > S i).
    {
      eapply anno_mono; eauto.
    }
    lia.

    simpl.
    invc H0.
    unfold not in *.
    intros.
    eapply H3.
    subst.
    econstructor; eauto.
    simpl.
    tauto.
    simpl.
    tauto.
  -
    ff.
    econstructor.
    eapply IHt1; try eauto.

    lia.



    assert (NoDup l).
    {
      eapply nodup_anno; eauto.
    }
    assert (length l >= nss t2).
    {
      admit.
    }
    

    eapply IHt2.
    eassumption.
    eassumption.
    eassumption.

    simpl.
    erewrite anno_range.
    tauto.
    eassumption.

    repeat erewrite anno_range.
    tauto.
    eassumption.
    eassumption.

    simpl.
    erewrite anno_range.
    tauto.
    eassumption.

    eapply anno_lrange'; eauto.

    assert (list_subset (lrange a0) l).
    eapply anno_lrange'; eauto.

    assert (list_subset l ls).
    {
      eapply anno_sub'; eauto.
    }

    unfold list_subset in *.
    eapply incl_tran; eauto.


    assert (ls = (lrange a) ++ l).
    {
      eapply anno_step; eauto.
    }
    subst.

    assert (l = (lrange a0) ++ ls').
    {
      eapply anno_step; eauto.
    }
    subst.

    rewrite app_assoc in *.



    eapply nodup_extra_app; eauto.
  -

        ff.
    econstructor.
    eauto.

    assert (NoDup l).
    {
      eapply nodup_anno; eauto.
    }

    eapply IHt2.
    apply H0.
    eassumption.

    simpl.
    erewrite anno_range.
    tauto.
    eassumption.

    repeat erewrite anno_range.
    tauto.
    eassumption.
    eassumption.

    simpl.
    erewrite anno_range.
    tauto.
    eassumption.

    eapply anno_lrange'; eauto.

    assert (list_subset (lrange a0) l).
    eapply anno_lrange'; eauto.

    assert (list_subset l ls).
    {
      eapply anno_sub'; eauto.
    }

    unfold list_subset in *.
    eapply incl_tran; eauto.


    assert (ls = (lrange a) ++ l).
    {
      eapply anno_step; eauto.
    }
    subst.

    assert (l = (lrange a0) ++ ls').
    {
      eapply anno_step; eauto.
    }
    subst.



    rewrite app_assoc in *.
    eapply nodup_extra_app; eauto.
  -


    
    ff.
    econstructor.

    assert (NoDup l4).
    {
      invc H.
      invc H3.
      invc H4.
      invc H5.
      eauto.
    }
    eauto.

    assert (NoDup l4).
    {
      invc H.
      invc H3.
      invc H4.
      invc H5.
      eauto.
    }

    
    assert (NoDup l).
    {
      
      eapply nodup_anno; eauto.
    }

    eauto.

    (*

    eapply IHt2.
    apply H0.
    eassumption. *)

    simpl.
    erewrite anno_range.
    tauto.
    eassumption.

    repeat erewrite anno_range.
    tauto.
    eassumption.
    eassumption.

    simpl.
    erewrite anno_range.
    tauto.
    eassumption.

    repeat erewrite anno_range.
    Focus 2.
    eassumption.
    Focus 2.
    eassumption.
    simpl.
    eapply anno_mono; eauto.

    assert (list_subset (lrange a) l4).
    {
      eapply anno_lrange'; eauto.
    }
    unfold list_subset in *.
    eapply incl_tran; eauto.
    right.
    right.
    right.
    right.
    eauto.

    assert (list_subset (lrange a0) l).
    {
      eapply anno_lrange'; eauto.
    }
    assert (list_subset l l4).
    {
      eapply anno_sub'; eauto.
    }
    

    
    unfold list_subset in *.
    eapply incl_tran; eauto.
    right.
    right.
    right.
    right.
    eauto.

    ff.
    unfold list_subset.
    unfold incl.
    intros.
    invc H0.
    ++
      econstructor; tauto.
    ++
      invc H1.
      +++
        right.
        econstructor; eauto.
      +++
        invc H0.
        ++++
          right.
          right.
          econstructor; eauto.
        ++++
          invc H1.
          +++++
            right.
          right.
          right.
          econstructor; eauto.
          +++++
            solve_by_inversion.
    ++
      ff.

      assert (l4 = (lrange a) ++ l).
      {
        eapply anno_step; eauto.
      }
      subst.

      assert (l = (lrange a0) ++ ls').
      {
        eapply anno_step; eauto.
      }
      subst.

      assert (n1 :: n2 :: n3 :: n4 :: lrange a ++ lrange a0 ++ ls' = (n1 :: n2 :: n3 :: n4 :: lrange a ++ lrange a0) ++ ls').
      rewrite app_assoc.
      tauto.
      rewrite H0 in *.

      Check nodup_extra_app.

      eapply nodup_extra_app; eauto.
Defined.

      



      

      
      
          
       (*   
          
        
      

    
    
    

    

    eapply anno_lrange'; eauto.

    assert (list_subset (lrange a0) l).
    eapply anno_lrange'; eauto.

    assert (list_subset l ls).
    {
      eapply anno_sub'; eauto.
    }

    unfold list_subset in *.
    eapply incl_tran; eauto.


    assert (ls = (lrange a) ++ l).
    {
      admit.
    }
    subst.

    assert (l = (lrange a0) ++ ls').
    {
      admit.
    }
    subst.



    eapply nodup_extra_app; eauto.
    
    
    
    
    
    
    
    

    
    

    eapply anno_lrange'.

    

    

    
    
    

    
    eapply IHt2.

    
    
    *)
    
    





  
  (*



  intros.

  (*
  assert (ls' = []).
  {
    eapply anno_full; eauto.
  }
  subst.
   *)

  (*
  assert (length ls >= nss t).
  {
    eapply anno_has_enough; eauto.
  }
   *)
  
  

  generalizeEverythingElse t.
  
  
  induction t; intros; simpl;
    try (auto;
    repeat expand_let_pairs;
    econstructor; simpl; auto;
    repeat rewrite anno_lrange;
    repeat rewrite anno_range; simpl; reflexivity).
  -
   
    destruct a;
      ff.
    (*
    
      cbn in *;
      find_inversion;
      eauto;
    
      assert (ls' = []) by (destruct ls'; solve_by_inversion);
      solve_by_inversion.
     *)
    
  -
    ff.
    (*
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion. *)
    (*
    assert (ls' = []) by (destruct ls'; try solve_by_inversion). *)
    
    subst.
    econstructor.

    eapply anno_well_formed_r; eauto.

    simpl.
    erewrite anno_range.
    Focus 2.
    eassumption.
    simpl.
    tauto.
    simpl.

    assert (n2 = snd (range a)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      simpl.
      tauto.
    }
    congruence.
    simpl.

    assert (n2 > S i).
    {

      eapply anno_mono.
      eassumption.
    }
    lia.
    simpl.
    tauto.
    simpl.
    tauto.


    invc H.
    econstructor.
    unfold not in *.
    intros.

    apply H2.
    econstructor.
    invc H; eauto.

    solve_by_inversion.
    econstructor.
    unfold not; intros.
    solve_by_inversion.
    econstructor.

    tauto.

  -
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    
    econstructor;
      try tauto;
      try solve_by_inversion.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }
    rewrite H1 in H0.

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4.

    eapply IHt1.
    eassumption.
    eassumption.
    lia.
  
  (*

    eapply IHt2.

    
    
    eassumption.
    eassumption.
   *)

    admit.


          simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    erewrite anno_range.
    Focus 2.
    eassumption.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    simpl.
    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

(*
    assert (n0 = snd (range a0)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
    }
    congruence. *)



  




    eapply anno_lrange'.
    apply Heqo.

    assert (list_subset l ls).
    {
      eapply anno_sub'; eauto.
    }

    assert (list_subset (lrange a0) l).
    {
      eapply anno_lrange'; eauto.
    }

    unfold list_subset in *.
    eauto.

    

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    

    
    rewrite <- H2 in *; clear H2.
    rewrite H3 in *; clear H3.
    lia.
    assert (nss t2 = length l) by lia.

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }

    rewrite H5 in H4.
    assert (length ls' = 0) by lia.

    

    rewrite H1.

    rewrite <- H2 in *; clear H2.
    rewrite <- H3 in *; clear H3.

    rewrite H5 in *; clear H5.


    (*
    Search (_ + 0).
    rewrite Nat.add_0_r in *.
    clear_dups.
    clear_refl_eqs.
     *)
    
    

    assert (length ls = length (lrange a) + (length l)).
    {
      
      
      eapply lrange_len; eauto.
    }

    assert (length l = length (lrange a0) + (length ls')).
    {
      eapply lrange_len; eauto.
    }
    lia.






    
    
    


(*
    assert (length ls' = 0).
    {
      lia.
    }

    assert (ls' = []) by (destruct ls'; try solve_by_inversion).

    rewrite H3 in *; clear H3.

  

    rewrite H4 in *; clear H4. *)

    assert (l = (lrange a0)).
    {
      eapply anno_lrange_eq; eauto.
      erewrite nss_iff_anss; eauto.
    }

    rewrite H3 in *; clear H3.

    
    
      

    eapply IHt1 with (ls:=(lrange a)).
    Focus 3.

    eapply anno_full_ex_full.

    eapply anno_sub with (ls:=lrange a).

    symmetry.
    eapply anno_lrange_eq.
    


    
    eapply lrange_nss; eauto.

    


    
    rewrite PeanoNat.Nat.add_0_r in *.
    edestruct anno_full_ex.

    Check anno_subtract.

    assert (length (lrange a0) = length ls - nss t1).
    {
      eapply anno_subtract; eauto.
    }

    erewrite <- nss_iff_anss in H2; eauto.
    eassumption.
    eassumption.
    
    

    eapply anno_sub.

    edestruct anno_full_ex.
    eassumption.

    destruct_conjs

    edestruct anno_some.
    Search (_ + 0).

    rewrite PeanoNat.Nat.add_0_r in *.
    apply H2.

    destruct_conjs.

    eapply anno_sub.
    rewrite PeanoNat.Nat.add_0_r in *.

    eassumption.
    
    eassumption.
    


    
    edestruct anno_some.
    
    apply H2.
    Focus 2.
    

    eapply anno_sub; eauto.

    assert (list_subset (lrange a) ls).
    {
      eapply anno_lrange'; eauto.
    }

    Check anno_full.

    
    eapply nodup_sub; eauto.
    
    



    eapply anno_sub; eauto.

    eapply nodup_sub; eauto.
    eapply anno_lrange'; eauto.
    eapply anno_sub; eauto.

    eapply IHt2 with (ls:=(lrange a0)).   
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a0) ls).
    {
      assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l ls).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.
    }

    eapply anno_sub; eauto.

    eapply nodup_sub; eauto.

    assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l ls).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.

      eapply anno_sub; eauto.

      (*
    

    eapply anno_lrange'; eauto.
    eapply anno_sub; eauto.

    eapply anno_sub; eauto.
       *)
      

      simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    erewrite anno_range.
    Focus 2.
    eassumption.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    simpl.
    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

(*
    assert (n0 = snd (range a0)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
    }
    congruence. *)



  




    eapply anno_lrange'.
    apply Heqo.

    assert (list_subset l ls).
    {
      eapply anno_sub'; eauto.
    }

    assert (list_subset (lrange a0) l).
    {
      eapply anno_lrange'; eauto.
    }

    unfold list_subset in *.
    eauto.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    (*
    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4. *)
    assert (nss t2 = length l) by lia.

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }

    rewrite H5 in H4.
    assert (length ls' = 0) by lia.

    

    rewrite H1.

    rewrite <- H2 in *; clear H2.
    rewrite <- H3 in *; clear H3.

    rewrite H5 in *; clear H5.


    (*
    Search (_ + 0).
    rewrite Nat.add_0_r in *.
    clear_dups.
    clear_refl_eqs.
     *)
    
    

    assert (length ls = length (lrange a) + (length l)).
    {
      
      
      eapply lrange_len; eauto.
    }

    assert (length l = length (lrange a0) + (length ls')).
    {
      eapply lrange_len; eauto.
    }
    lia.
 *)



  (*
  -

        cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    
    econstructor;
      try tauto;
      try solve_by_inversion.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }
    rewrite H2 in H1.

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4.
    
    



    assert (length ls' = 0).
    {
      lia.
    }

    rewrite H3 in *.

    eapply IHt1 with (ls:=(lrange a)).
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a) ls).
    {
      eapply anno_lrange'; eauto.
    }

    (*
    eapply nodup_sub; eauto. *)
    
    



    eapply anno_sub; eauto.

    eapply nodup_sub; eauto.
    eapply anno_lrange'; eauto.
    eapply anno_sub; eauto.

    eapply IHt2 with (ls:=(lrange a0)).   
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a0) ls).
    {
      assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l ls).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.
    }

    eapply anno_sub; eauto.

    eapply nodup_sub; eauto.

    assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l ls).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.

      eapply anno_sub; eauto.

      (*
    

    eapply anno_lrange'; eauto.
    eapply anno_sub; eauto.

    eapply anno_sub; eauto.
       *)
      

      simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    erewrite anno_range.
    Focus 2.
    eassumption.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    simpl.
    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

(*
    assert (n0 = snd (range a0)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
    }
    congruence. *)



  




    eapply anno_lrange'.
    apply Heqo.

    assert (list_subset l ls).
    {
      eapply anno_sub'; eauto.
    }

    assert (list_subset (lrange a0) l).
    {
      eapply anno_lrange'; eauto.
    }

    unfold list_subset in *.
    eauto.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    (*
    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4. *)
    assert (nss t2 = length l) by lia.

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }

    rewrite H5 in H4.
    assert (length ls' = 0) by lia.

    

    rewrite H1.

    rewrite <- H2 in *; clear H2.
    rewrite <- H3 in *; clear H3.

    rewrite H5.

    assert (length ls = length (lrange a) + (length l)).
    {
      eapply lrange_len; eauto.
    }

    assert (length l = length (lrange a0) + (length ls')).
    {
      eapply lrange_len; eauto.
    }

    lia.
















    

    (*

    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    
    econstructor;
      try tauto;
      try solve_by_inversion.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }
    rewrite H2 in H1.

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4.
    
    



    assert (length ls' = 0).
    {
      lia.
    }

    rewrite H3 in *.

    eapply IHt1 with (ls:=(lrange a)).
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a) ls).
    {
      eapply anno_lrange'; eauto.
    }

    eapply nodup_sub; eauto.
    
    



    eapply anno_sub; eauto.

    eapply IHt2 with (ls:=(lrange a0)).   
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a0) ls).
    {
      assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l ls).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.
    }

    eapply nodup_sub; eauto.

    eapply anno_sub; eauto.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    erewrite anno_range.
    Focus 2.
    eassumption.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    simpl.


    assert (n0 = snd (range a0)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
    }
    congruence.

  




    eapply anno_lrange'.
    apply Heqo.

    assert (list_subset l ls).
    {
      eapply anno_sub'; eauto.
    }

    assert (list_subset (lrange a0) l).
    {
      eapply anno_lrange'; eauto.
    }

    unfold list_subset in *.
    eauto.

    assert (length ls = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    (*
    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4. *)
    assert (nss t2 = length l) by lia.

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }

    rewrite H5 in H4.
    assert (length ls' = 0) by lia.

    

    rewrite H1.

    rewrite <- H2 in *; clear H2.
    rewrite <- H3 in *; clear H3.

    rewrite H5.

    assert (length ls = length (lrange a) + (length l)).
    {
      eapply lrange_len; eauto.
    }

    assert (length l = length (lrange a0) + (length ls')).
    {
      eapply lrange_len; eauto.
    }

    lia.
     
    
  -
    ff.



    econstructor;
      try tauto;
      try solve_by_inversion.

    assert (length l4 = anss a + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a0 + length ls').
    {
      eapply anno_len; eauto.
    }
    rewrite H1 in H.

    assert (nss t1 = anss a).
    {
      eapply nss_iff_anss; eauto.
    }

    assert (nss t2 = anss a0).
    {
      eapply nss_iff_anss; eauto.
    }

    rewrite <- H3 in *; clear H3.
    rewrite H4 in *; clear H4.
    
    



    assert (length ls' = 0).
    {
      lia.
    }

    rewrite H3 in *.

    eapply IHt1 with (ls:=(lrange a)).
    eapply lrange_nss; eauto.

    eapply anno_sub; eauto.

    assert (list_subset (lrange a) l4).
    {
      eapply anno_lrange'; eauto.
    }

    Check nodup_sub.
    eapply nodup_sub with (ls:=l4); eauto.
    invc H0. invc H8.  invc H9. invc H10.
    eauto.
    
    



    eapply anno_sub; eauto.

    eapply IHt2 with (ls:=(lrange a0)).   
    eapply lrange_nss; eauto.

    assert (list_subset (lrange a0) l4).
    {
      assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l l4).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.
    }

    eapply anno_sub; eauto.

    eapply nodup_sub; eauto.

     assert (list_subset (lrange a0) l4).
    {
      assert (list_subset (lrange a0) l).
      {
        eapply anno_lrange'; eauto.
      }

      assert (list_subset l l4).
      {
        eapply anno_sub'; eauto.
      }

      unfold list_subset in *; eauto.
    }


    
    unfold list_subset in *.
    intros.
    right.
    right.
    right.
    right.
    eauto.

    eapply anno_sub; eauto.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    erewrite anno_range.
    Focus 2.
    eassumption.

    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    tauto.

    simpl.


    assert (n0 = snd (range a0)).
    {
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
    }
    congruence.

    erewrite anno_range.
    Focus 2.
    eassumption.
    simpl.

    erewrite anno_range.
    Focus 2.
    eassumption.
    simpl.

    eapply anno_mono; eauto.

    assert (list_subset (lrange a) l4).
    {
      eapply anno_lrange'; eauto.
    }
    unfold list_subset in *.
    intros.
    right.
    right.
    right.
    right.
    eauto.


    assert (list_subset (lrange a0) l).
    {
      eapply anno_lrange'; eauto.
    }

    assert (list_subset l l4).
    {
      eapply anno_sub'; eauto.
    }
    unfold list_subset in *.
    intros.
    right.
    right.
    right.
    right.
    eauto.
    

    simpl.
    tauto.
    simpl.
    tauto.
    simpl.
    tauto.
    simpl.
    tauto.

    simpl.

    assert (length (lrange a) = nss t1).
    {
      eapply lrange_nss; eauto.
      eapply anno_sub; eauto.
    }

    assert (length (lrange a0) = nss t2).
    {
      eapply lrange_nss; eauto.
      eapply anno_sub; eauto.
    }
    lia.
Defined.
     *)

*)
Admitted.




(*

    ff.

    econstructor.
    
    

    
    
    
    

    assert (length (lrange a) = nss t1).
    {
      eapply lrange_nss; eauto.
    }

    eapply IHt1.
    eassumption.

    
    

    erewrite anno_len.
    Focus 2.
    apply Heqo.

    erewrite anno_len.
    Focus 2.
    apply Heqo0.

    assert (length ls = length (lrange a) + (length l)).
    {
      admit.
    }

    assert (length l = length (lrange a0) + (length ls')).
    {
      admit.
    }

    assert (nss t1 + (nss t2 + length ls') = length ls + length ls').
    {
      lia.
    }

    rewrite H2; clear H2.

    rewrite H0; clear H0.

    rewrite H1; clear H1.
    
    

    assert (nss t1 + (nss t2 + length ls') = length (lrange a) + length l + length ls').
    {
      admit.
    }

    rewrite H2.

    rewrite H1.
    

    lia.
    
    
    
    

    eapply anno_lrange'.
    apply Heqo0.


    

    eapply IHt1.
    Focus 2.
    eassumption.
    

    Lemma anno_subterm:
      anno t1 i ls = Some (n, (l,a)) ->
      exists ls' l' a',
        anno t1 i ls' = Some(n, (l',a'))
      well_formed a
    
    

    

    eapply IHt1.
    eassumption.
    

    (*
    assert (ls' = []).
    {
      admit.
    }
     *)

    (*
    subst.
    eapply IHt.
    Focus 2.
    eassumption.
    Check anno_lrange.
    assert (list_subset [] (lrange a)).
    {
      eapply anno_lrange.
      Focus 2.
      eassumption.
      

      
      admit.
    }
     *)
    

    solve_by_inversion.
    solve_by_inversion.
    
    
    simpl.
    erewrite anno_range; simpl; try reflexivity.
    eassumption.
    simpl.
    erewrite anno_range; simpl; try reflexivity.
    eassumption.
    simpl.
    assert (n2 > (S i)).
    {
      eapply anno_mono; eauto.
    }
    lia.
    simpl.
    cbn in *.
    repeat break_match; try solve_by_inversion.
    simpl.
    cbn in *.
    repeat break_match; try solve_by_inversion.
    cbn in *.
    repeat break_match; try solve_by_inversion.
  -
    cbn in *.
    repeat break_match; try solve_by_inversion.
    repeat find_inversion.
    econstructor.
    
    admit.
    admit.
    
    admit.
    admit.
    admit.

    admit.

    admit.
    admit.

    

    Check anno_lrange.

    




    
    eapply IHt1.
    Focus 2.
    eassumption.
    
    
    
    
    
    eapply IHt.
    Focus 2.
    eassumption.
    Check anno_lrange.

    simpl.
    try solve_by_inversion.
      




  
  -
    auto.
    repeat break_let.
    simpl.
    econstructor;
      try (simpl; lia).
    +
      pose (IHt (S i) (S (S loc))).
      rewrite Heqp in *. eassumption.
    +
      simpl.
      assert (a = snd (snd (anno t (S i) (S (S loc))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_range.
      tauto.
    +
      simpl.
      assert (a = snd (snd (anno t (S i) (S (S loc))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_range.
      simpl.
      rewrite Heqp.
      tauto.
    +
      simpl.
      assert (n0 > (S i)).
      eapply anno_mono; eauto.
      lia.
    +
       simpl.
      assert (a = snd (snd (anno t (S i) (S (S loc))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_lrange.
      simpl.
      lia.

      (*
      rewrite Heqp.
      tauto.



      
      simpl in *.
      Check lrange_anno_mono.
      Check anno_lrange.

      assert (
      
      assert (fst (lrange a) >= (S (S loc))).
      {
        eapply lrange_anno_mono'; eauto.
      }
      
      assert (n1 >= (S (S loc))).
      {
        eapply lrange_anno_mono; eauto.
      }
      lia. *)
      
      
      (*
  -
    repeat break_let.
    simpl in *.
    econstructor;
      try (simpl; lia).
    +
      pose (IHt1 i loc).
      rewrite Heqp in *. eassumption.
    +
      pose (IHt2 n n0).
      rewrite Heqp1 in *. eassumption.
    +
      simpl.
       *)
    
      
    +
      simpl.
      assert (n1 >= S (S loc)).
      {  
        eapply lrange_anno_mono; eauto.   
      }
      lia.
    +
      simpl in *.

      simpl.
      assert (a = snd (snd (anno t (S i) (S (S loc))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_lrange.
      simpl.
      rewrite Heqp.
      simpl.
      lia.
      
      
      
    
  -
    repeat break_let.
    simpl in *.
    econstructor;
      try (simpl; lia).

    +  
      pose (IHt1 (S i) (S (S (S (S loc))))).
      rewrite Heqp in *. eassumption.
    +
      pose (IHt2 n n0).
      rewrite Heqp1 in *. eassumption.
    +
      simpl.
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_range.
      simpl.
      tauto.
    +
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
      subst.
      rewrite anno_range.
      rewrite anno_range.
      simpl.
      rewrite Heqp.
      simpl.
      tauto.
    +
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
      subst.
      simpl.
      rewrite Heqp1.
      simpl.
      rewrite anno_range.
      simpl.
      rewrite Heqp1.
      simpl.
      tauto.
    +
      assert (n1 > n).
      eapply anno_mono; eauto.
      assert (n > (S i)).
      eapply anno_mono; eauto.
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
      subst.
      rewrite anno_range.
      rewrite anno_range.
      simpl.
      lia.
    +
      simpl.
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_lrange.
      
      simpl.
      lia.
    +
      simpl.
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
     
      subst.
      rewrite anno_lrange.
      
      simpl.
      rewrite Heqp1.
      simpl.
      lia.
    +
      simpl.
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      subst.
      rewrite anno_lrange.
      
      simpl.
      lia.
    +
      assert (a = snd (snd (anno t1 (S i) (S (S (S (S loc))))))) by (rewrite Heqp; tauto).
      assert (a0 = snd (snd (anno t2 n n0))) by (rewrite Heqp1; tauto).
      subst.
      repeat (rewrite anno_lrange).
      simpl.
      rewrite Heqp.
      simpl.
      lia.      
Defined.
   *)



Lemma anno_well_formed':
  forall t ls,
    length ls = nss t ->
    NoDup ls ->
    well_formed (annotated t ls).
Proof.
  intros.
  edestruct anno_some with (t := t) (i:=0).
  eassumption.
  destruct x.
  destruct p.
  unfold annotated.
  unfold anno'.
  simpl.
  rewrite H1.
  simpl.
  eapply anno_well_formed.
  eassumption.
  eassumption.
Defined.

(** Eval for annotated terms. *)

Fixpoint aeval t p e :=
  match t with
  | aasp _ _ x => eval (asp x) p e
  | aatt _ _ _ q x => aeval x q e
  | alseq _ _ t1 t2 => aeval t2 p (aeval t1 p e)
  | abseq _ _ s t1 t2 => ss (aeval t1 p ((splitEv_T (fst s)) e))
                         (aeval t2 p ((splitEv_T (snd s)) e)) 
  | abpar _ _ _ _ s t1 t2 => pp (aeval t1 p ((splitEv_T (fst s)) e))
                         (aeval t2 p ((splitEv_T (snd s)) e))
  end. 

(*
Lemma eval_aeval:
  forall t p e i loc,
    eval t p e = aeval (snd (snd ((anno t i loc)))) p e.
Proof.
  induction t; intros; simpl; auto;
    repeat expand_let_pairs; simpl;
      try (repeat jkjk; auto;congruence);
      try (repeat jkjk'; auto).
Defined.
*)

(** This predicate specifies when a term, a place, and some initial
    evidence is related to an event.  In other words, it specifies the
    set of events associated with a term, a place, and some initial
    evidence. *)

Inductive events: AnnoTerm -> Plc -> Ev -> Prop :=
| evtscpy:
    forall r lr i p,
      fst r = i ->
      events (aasp r lr CPY) p (copy i p)
| evtsusm:
    forall i id args r lr p,
      fst r = i ->
      events (aasp r lr (ASPC id args)) p (umeas i p id args)
| evtssig:
    forall r lr i p,
      fst r = i ->
      events (aasp r lr SIG) p (sign i p) 
| evtshsh:
    forall r lr i p,
      fst r = i ->
      events (aasp r lr HSH) p (hash i p)
| evtsattreq:
    forall r lr q t i p req_loc rpy_loc,
      fst r = i ->
      events (aatt r lr (req_loc, rpy_loc) q t) p (req i req_loc p q (unanno t))
| evtsatt:
    forall r lr q t ev p locs,
      events t q ev ->
      events (aatt r lr locs q t) p ev
| evtsattrpy:
    forall r lr q t i p req_loc rpy_loc,
      snd r = S i ->
      events (aatt r lr (req_loc, rpy_loc) q t) p (rpy i rpy_loc p q)
| evtslseql:
    forall r lr t1 t2 ev p,
      events t1 p ev ->
      events (alseq r lr t1 t2) p ev
| evtslseqr:
    forall r lr t1 t2 ev p,
      events t2 p ev ->
      events (alseq r lr t1 t2) p ev
| evtsbseqsplit:
    forall r lr i s t1 t2 p,
      fst r = i ->
      events (abseq r lr s t1 t2) p
             (Term_Defs.split i p)
| evtsbseql:
    forall r lr s t1 t2 ev p,
      events t1 p ev ->
      events (abseq r lr s t1 t2) p ev
| evtsbseqr:
    forall r lr s t1 t2 ev p,
      events t2 p ev ->
      events (abseq r lr s t1 t2) p ev
| evtsbseqjoin:
    forall r lr i s t1 t2 p,
      snd r = S i ->
      events (abseq r lr s t1 t2) p
             (join i p)

| evtsbparsplit:
    forall r lr i s t1 t2 p xi xi' yi yi',
      fst r = i ->
      events (abpar r lr (xi,xi') (yi,yi') s t1 t2) p
             (splitp i xi yi p)
| evtsbparl:
    forall r lr s t1 t2 ev p xlocs ylocs,
      events t1 p ev ->
      events (abpar r lr xlocs ylocs s t1 t2) p ev
| evtsbparr:
    forall r lr s t1 t2 ev p xlocs ylocs,
      events t2 p ev ->
      events (abpar r lr xlocs ylocs s t1 t2) p ev
| evtsbparjoin:
    forall r lr i s t1 t2 p xi xi' yi yi',
      snd r = S i ->
      events (abpar r lr (xi,xi') (yi,yi') s t1 t2) p
             (joinp i (xi') (yi') p).
Hint Constructors events : core.

(*
Lemma events_range_r:
  forall t v p,
    well_formed_r t ->
    events t p v ->
    fst (range t) <= ev v < snd (range t).
Proof.
    (*
  intros t v p H H0.
  pose proof H as G.
  apply well_formed_range_r in G.
  rewrite G.
  clear G.
  induction H0; inv H; simpl in *; auto;
    try (repeat find_apply_hyp_hyp;
         repeat (find_apply_lem_hyp well_formed_range); lia).
     *)
Admitted.
*)

  
Lemma events_range:
  forall t v p,
    well_formed_r t ->
    events t p v ->
    fst (range t) <= ev v < snd (range t).
Proof.
  
  intros t v p H H0.
  pose proof H as G.
  apply well_formed_range_r in G.
  rewrite G.
  clear G.
  induction H0;
    try (inv H; simpl in *; auto;
         repeat find_apply_hyp_hyp;
         repeat (find_apply_lem_hyp well_formed_range_r); lia).
Defined.

Require Import Compare_dec.

Lemma at_range:
  forall x r i,
    S (fst r) = fst x ->
    snd r = S (snd x) ->
    fst r <= i < snd r ->
    i = fst r \/
    fst x <= i < snd x \/
    i = snd x.
Proof.
  intros.
  pose proof lt_dec i (S (fst r)) as G.
  destruct G as [G|G]; [left; lia| right].
  pose proof lt_dec i (snd x) as F.
  destruct F as [F|F]; [left; lia| right].
  lia.
Qed.

Lemma lin_range:
  forall x y i,
    snd x = fst y ->
    fst x <= i < snd y ->
    fst x <= i < snd x \/
    fst y <= i < snd y.
Proof.
  intros.
  pose proof lt_dec i (snd x) as G.
  destruct G; lia.
Qed.

Lemma bra_range:
  forall x y r i,
    S (fst r) = fst x ->
    snd x = fst y ->
    snd r = S (snd y) ->
    fst r <= i < snd r ->
    i = fst r \/
    fst x <= i < snd x \/
    fst y <= i < snd y \/
    i = snd y.
Proof.
  intros.
  pose proof lt_dec i (S (fst r)) as G.
  destruct G as [G|G]; [left; lia| right].
  pose proof lt_dec i (snd x) as F.
  destruct F as [F|F]; [left; lia| right].
  pose proof lt_dec i (snd y) as E.
  destruct E; lia.
Qed.

Require Import Coq.Program.Tactics.
(** Properties of events. *)

Lemma events_range_event:
  forall t p i,
    well_formed_r t ->
    fst (range t) <= i < snd (range t) ->
    exists v, events t p v /\ ev v = i.
Proof.
  intros t p i H; revert i; revert p.
  induction H; intros; simpl in *.
  - destruct x; eapply ex_intro; split; auto;
      (*destruct r as [j k];*) simpl in *; lia.
  - find_eapply_lem_hyp at_range; eauto.
    (*eapply at_range in H2; eauto. *)
    destruct r; destruct locs.
    repeat destruct_disjunct; subst; eauto.
    (* + eapply ex_intro; split; auto. *)
    Ltac find_eapply_hyp_hyp :=
      match goal with
      | [ H : forall _, _ -> _,
            H' : _ |- _ ] =>
        eapply H in H'; [idtac]
      | [ H : _ -> _ , H' : _ |- _ ] =>
        eapply H in H'; auto; [idtac]
      end.
    + 
      find_eapply_hyp_hyp.
      (*apply IHwell_formed with (p:=p) in H2. *)
      destruct_conjs.
      eauto.
      (*
      destruct H2 as [v].
      destruct H2; subst.
      exists v; split; eauto. 
    + eapply ex_intro; split.
      apply evtsattrpy; auto.
      * rewrite H1; auto.
      * simpl; auto.
      *)
      
  - eapply lin_range with (i:=i) in H2; eauto;
    repeat destruct_disjunct;
      try lia;
      try (find_eapply_hyp_hyp; eauto;
        destruct_conjs;
        eauto).

    

  - 
    apply bra_range with (i:=i) (r:=r) in H2; eauto;
      repeat destruct_disjunct; subst;
        try lia;
        try (find_eapply_hyp_hyp; eauto;
             destruct_conjs;
             eauto; tauto).
      

    + eapply ex_intro; split; try (auto; eauto;tauto).
    + eapply ex_intro; split; try (eauto; auto; tauto).

  -
    destruct xlocs; destruct ylocs.
    apply bra_range with (i:=i) (r:=r) in H2; eauto;
      repeat destruct_disjunct; subst;
        try lia;
        try (find_eapply_hyp_hyp; eauto;
             destruct_conjs;
             eauto; tauto).

    + eapply ex_intro; split; auto.
    + eapply ex_intro; split; eauto.
Qed.


Ltac events_event_range :=
  repeat match goal with
         | [ H: events _ _ _ |- _ ] =>
           apply events_range in H; auto
         end; lia.

Ltac aba :=
  match goal with
  | [H: events _ _ _, H': events _ _ _ |- _] => inv H; inv H'
  end.

Ltac wfr :=
  match goal with
  | [H: AnnoTerm, H': well_formed_r ?H |- _] => pose_new_proof (well_formed_range_r H H')
  end.

Lemma events_injective:
  forall t p v1 v2,
    well_formed_r t ->
    events t p v1 ->
    events t p v2 ->
    ev v1 = ev v2 ->
    v1 = v2.
Proof.
  intros t p v1 v2 H; revert v2; revert v1;
    revert p.
  induction H; intros;
    try (
        repeat wfr;
        aba; simpl in *; subst; auto;
        try (events_event_range; tauto);
        try (find_eapply_hyp_hyp; eauto);
        eauto).
Qed.

(*
repeat find_apply_lem_hyp well_formed_range.

find_apply_lem_hyp well_formed_range.
find_apply_lem_hyp well_formed_range
apply well_formed_range in G.
apply well_formed_range in G0.
Check well_formed_range.
 *)


Inductive splitEv_T_R : SP -> Evidence -> Evidence -> Prop :=
| spAll: forall e, splitEv_T_R ALL e e
| spNone: forall e, splitEv_T_R NONE e mt.

Inductive evalR : Term -> Plc -> Evidence -> Evidence -> Prop :=
| evalR_asp: forall a p e,
    evalR (asp a) p e (eval_asp a p e)
| evalR_att: forall t1 q e e' p,
    evalR t1 q e e' ->
    evalR (att q t1) p e e'
| evalR_lseq: forall t1 t2 p e e' e'',
    evalR t1 p e e' ->
    evalR t2 p e' e'' ->
    evalR (lseq t1 t2) p e e''
| evalR_bseq: forall s e e1 e2 e1' e2' p t1 t2,
    splitEv_T_R (fst s) e e1 ->
    splitEv_T_R (snd s) e e2 ->
    evalR t1 p e1 e1' ->
    evalR t2 p e2 e2' ->
    evalR (bseq s t1 t2) p e (ss e1' e2')
| evalR_bpar: forall s e e1 e2 e1' e2' p t1 t2,
    splitEv_T_R (fst s) e e1 ->
    splitEv_T_R (snd s) e e2 ->
    evalR t1 p e1 e1' ->
    evalR t2 p e2 e2' ->
    evalR (bpar s t1 t2) p e (pp e1' e2').

Ltac jkjke :=
  match goal with
  | [H: _ |-  _ ] => erewrite H; eauto
  end.
Ltac kjkj :=
  match goal with
  | [H: evalR ?t ?p ?e ?e' |- _] => assert_new_proof_by (eval t p e = e') eauto
  end.


Ltac do_split :=
  match goal with
  | [H: Split |- _] => destruct H
  end.
      
Ltac do_sp :=
  match goal with
  | [H: SP |- _] => destruct H
  end.

Lemma eval_iff_evalR: forall t p e e',
    evalR t p e e' <-> eval t p e = e'.
Proof.
  split.
  - (* -> case *)
    intros.
    generalize dependent p.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros;
      try (
          inv H;
          simpl;
          repeat kjkj;
          

          try (do_split;
               repeat do_sp);
          try (inv H3; inv H4; reflexivity);
          repeat jkjk;
          eauto).

  (*try (
    inv H;
    simpl;
    repeat kjkj). *)
    
 (*         
    + destruct a; solve_by_inversion.
    + 
      inv H. simpl.
      eauto.
    + inv H.

      simpl.
      repeat kjkj.
      eauto.
      (*
      repeat jkjk.
      eauto. *)

    
    +
      inv H.
      simpl.
      repeat kjkj.

      do_split;
        do_sp;
        try (inv H3; inv H4; reflexivity).
    +
      inv H.
      simpl.
      repeat kjkj.
      
      do_split;
        do_sp;
        try (inv H3; inv H4; reflexivity).
*)
    

  - (* <- case *)
    intros.
    generalize dependent p.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros;
      inv H;
      try (destruct a);
      try (do_split; repeat do_sp);
      repeat econstructor; eauto.
Defined.


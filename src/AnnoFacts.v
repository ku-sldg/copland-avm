Require Import Defs List_Facts Term_Defs StructTactics Preamble Term_Facts.

Require Import Lia Coq.Program.Tactics.

Require Import List.
Import List.ListNotations.

(*

Require Import Lists.List.
*)

Set Nested Proofs Allowed.

Ltac same_index :=
  match goal with
  | [H: anno ?t _ _ _ = Some (?n, _),
        H': anno ?t _ _ _ = Some (?n', _) |- _] =>
    assert_new_proof_by (n = n') eauto
  end.

Lemma same_anno_range: forall t i l l2 a b n n' bo bo',
    anno t i l bo = Some (n,a) ->
    anno t i l2 bo' = Some (n',b) ->
    n = n'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
    (* Full automation causes proof to take ~3x longer *)
    (*
    try
      (destruct a;
       ff; tauto);
    try (ff; tauto);
    try (
        ff;
        repeat (same_index; subst);
        congruence).
     *)
  -
    destruct a; ff.
  -
    ff.
  -
    ff.
    repeat (same_index; subst);
      congruence.
    (*
  -
    ff;
    repeat (same_index; subst);
    congruence.
  -
    ff;
      repeat (same_index; subst);
      congruence. *)
 Defined.
  
Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm) (ls:LocRange) b,
  anno t i ls b = Some (j,t') ->
  j > i.
Proof.
  induction t; intros; (*i j t' ls b H; *)
    ff;
    repeat find_apply_hyp_hyp;
    lia.
Defined.
Hint Resolve anno_mono : core.

Lemma anno_range:
  forall x i j ls t' b,
     anno x i ls b = Some (j,t') ->
    range (t') = (i, j).
Proof.
  induction x; intros; ff.
Defined.

Ltac haha :=
  let asdff := eapply anno_mono; eauto in
  match goal with
  | [H: anno _ ?x = (?y,_) |- _] => assert_new_proof_by (y > x) (asdff)
  end.

Ltac hehe :=
  match goal with
  | [H: anno ?x ?y = (_,_) |- _] => pose_new_proof (anno_range x y)
  end.

Ltac hehe' :=
  match goal with
  | [x: Term, y:nat |- _] => pose_new_proof (anno_range x (S y))
  end.

Ltac hehe'' :=
  match goal with
  | [x: Term, y:nat |- _] => pose_new_proof (anno_range x y)
  end.

Ltac do_list_empty :=
  match goal with
    [H: length ?ls = 0 |- _] =>
    assert_new_proof_by (ls = []) ltac:(destruct ls; solve_by_inversion)
  end.

Lemma anno_lrange:
  forall x i j ls t' b,
    length ls = nss x ->
    anno x i ls b = Some (j,t') ->
    list_subset ls (lrange t').
Proof.
  induction x; intros;
    try (ff';
         try do_list_empty;
         ff';
         try tauto;
         congruence).
Defined.

Lemma anno_lrange'
  : forall (x : Term) (i j : nat) (ls : list nat) 
      (t' : AnnoTerm),
    (*length ls = nss x -> *)
    anno x i ls true = Some (j, t') ->
    list_subset (lrange t') ls.
Proof.
  intros.
  generalizeEverythingElse x.
  induction x; intros;
    try (ff'; tauto).
Defined.

Lemma both_anno_lrange
  : forall (x : Term) (i j : nat) (ls : list nat) 
      (ls' : LocRange) (t' : AnnoTerm),
    length ls = nss x ->
    anno x i ls true = Some (j,t') ->
    list_subset (lrange t') ls /\ list_subset ls (lrange t').
Proof.
  split.
  - eapply anno_lrange'; eauto.
  - eapply anno_lrange; eauto.
Defined.

Lemma false_succeeds: forall t i ls,
    anno t i ls false = None ->
    False.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try destruct a;
    ff;
    eauto.
Defined.

Lemma nss_iff_anss: forall t i ls n a b,
    anno t i ls b = Some (n,a) ->
    nss t = anss a.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    try destruct a;
    ff;
    try eauto;
    try (
        repeat find_apply_hyp_hyp;
        lia).
Defined.

Ltac list_facts' :=
  do_firstn_skipn_len;
  (*do_anno_some_fact; *)
  do_firstn_factt;
  do_firstn_skipn;
  nodup_list_firstn;
  nodup_list_skipn;
  do_nodup_firstn;
  do_nodup_skipn;
  do_nodup_contra.

Lemma anno_some_fact: forall t i ls n a,
    anno t i ls true = Some (n, a) ->
    length ls >= nss t.
Proof.
  induction t; intros.
  -
    ff.
    destruct ls; ff; lia.
  -
    ff.
    lia.
  -
    ff.
    list_facts'.
    
    assert (length ((firstn (nss t1) ls)) >= nss t1) by eauto.
    assert (length (skipn (nss t1) ls) >= nss t2) by eauto.

    (*

    assert (length ls = length (firstn (nss t1) ls) +
                        length (skipn (nss t1) ls)).
    {
      eapply firstn_skipn_len.
    } *)
    lia.
    (*
  -
    ff.
    list_facts'.
    assert (length ((firstn (nss t1) ls)) >= nss t1) by eauto.
    assert (length (skipn (nss t1) ls) >= nss t2) by eauto.
    lia.

  (*

    assert (length ls = length (firstn (nss t1) ls) +
                        length (skipn (nss t1) ls)).
    {
      eapply firstn_skipn_len.
    }
    lia. *)
  -
    ff.
    +
      
      list_facts'.
      assert (length ((firstn (nss t1) l0)) >= nss t1) by eauto.
      assert (length (skipn (nss t1) l0) >= nss t2) by eauto.
      ff.
      lia.

      (*

    +
      list_facts'.
      assert (length ((firstn (nss t1) [])) >= nss t1) by eauto.
      assert (length (skipn (nss t1) []) >= nss t2) by eauto.
      ff.
      lia.
    +
      list_facts'.
      assert (length ((firstn (nss t1) l2)) >= nss t1) by eauto.
      assert (length (skipn (nss t1) l2) >= nss t2) by eauto.
      ff.
      lia. *)
*)
Defined.

Ltac do_anno_some_fact :=
  repeat
    match goal with
    | [H: anno ?t _ ?ls _ = Some (_,_) |- _] =>
      assert_new_proof_by (length ls >= nss t) ltac:(eapply anno_some_fact; apply H)
    end.

Ltac list_facts :=
  do_firstn_skipn_len;
  do_anno_some_fact;
  do_firstn_factt;
  do_firstn_skipn;
  nodup_list_firstn;
  nodup_list_skipn;
  do_nodup_firstn;
  do_nodup_skipn;
  do_nodup_contra.

Lemma list_too_short: forall t i ls,
      anno t i ls true = None ->
      length ls < nss t.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff.
  -
    ff.
    exfalso.
    eapply false_succeeds; eauto.
  -
    ff.
    list_facts.
    
    +

      
      assert (length (skipn (nss t1) ls) < nss t2) by eauto.
      lia.

      (*

      assert (length (firstn (nss t1) ls) >= nss t1).
      {
        eapply anno_some_fact; eauto.
      }

      assert (length (firstn (nss t1) ls) = nss t1).
      {
        eapply firstn_factt; eauto.
      }

      assert (length ls = length (firstn (nss t1) ls) + length (skipn (nss t1) ls)).
      {
        eapply firstn_skipn_len; eauto.
      }
      lia. *)

    +
      assert (length (firstn (nss t1) ls) < nss t1) by eauto.
      

      assert (length ls < (nss t1)).
      {
        eapply firstn_fact'; eauto.
      }

      lia.
      (*
  -
    ff.
    list_facts.
    +    
      assert (length (skipn (nss t1) ls) < nss t2) by eauto.
      lia.
      (*

      assert (length (firstn (nss t1) ls) >= nss t1).
      {
        eapply anno_some_fact; eauto.
      }

      assert (length (firstn (nss t1) ls) = nss t1).
      {
        eapply firstn_factt; eauto.
      }

      assert (length ls = length (firstn (nss t1) ls) + length (skipn (nss t1) ls)).
      {
        eapply firstn_skipn_len; eauto.
      }
      lia. *)

    +
      assert (length (firstn (nss t1) ls) < nss t1) by eauto.

      assert (length ls < (nss t1)).
      {
        eapply firstn_fact'; eauto.
      }

      lia.
  -
    ff;
      try (
      list_facts;
      lia).

      
    +
      list_facts.
      assert (length (skipn (nss t1) l0) < nss t2) by eauto.
      ff.
      lia.

      (*

      assert (length (firstn (nss t1) []) = (nss t1)).
      {
        assert (length (firstn (nss t1) l2) >= (nss t1)).
        {
          eapply anno_some_fact; eauto.
        }

        eapply firstn_factt; eauto.
      }

      assert (length l2 = length (firstn (nss t1) l2) + length (skipn (nss t1) l2)).
      {
        eapply firstn_skipn_len; eauto.
      }
      lia. *)
    +

      assert (length (firstn (nss t1) l0) < nss t1) by eauto.
      ff.
      assert (nss t1 > length l0).
      {
        eapply firstn_fact'; eauto.
      }
      
      lia.
*)
Defined.

Lemma anno_some: forall t i l b,
  length l = nss t ->
  exists res,
    anno t i l b = Some res.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff;
      eauto.
  -
    cbn in *.
    assert (exists x y, l = [x; y]).
    {
      destruct l; try solve_by_inversion.
      invc H.
      destruct l; try solve_by_inversion.
      invc H1.
      assert (l = []) by (destruct l; solve_by_inversion).
      subst.
      eauto.
    }
    destruct_conjs.
    subst.
    ff.
    +
      eauto.
    +
      exfalso.
      eapply false_succeeds; eauto.
    +
      destruct b;
        ff.
        
  -
    ff.
    +
      eauto.
    +
      
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto).
    ++
      assert (length ((skipn (nss t1) l)) < nss t2).
      {
        eapply list_too_short; eauto.
      }

      assert (length (firstn (nss t1) l) = nss t1).
      {
        assert (length (firstn (nss t1) l) >= nss t1).
        {
          eapply anno_some_fact; eauto.
        }
        eapply firstn_factt; eauto.
      }

      assert (length l = length (firstn (nss t1) l) + length (skipn (nss t1) l)).
      {
        eapply firstn_skipn_len; eauto.
      }
      lia.
    +
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto).
      ++
        
        assert (length ((firstn (nss t1) l)) < nss t1).
        {
          eapply list_too_short; eauto.
        }
        (*
         assert (length l = length (firstn (nss t1) l) + length (skipn (nss t1) l)).
        {
          eapply firstn_skipn_len; eauto.
        }
         *)
        assert (length l < nss t1).
        {
          eapply firstn_fact'; eauto.
        }
        lia.
        (*

  -
    ff.
    +
      eauto.
    +
      
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto).
      ++
        assert (length ((skipn (nss t1) l)) < nss t2).
        {
          eapply list_too_short; eauto.
        }

        assert (length (firstn (nss t1) l) = nss t1).
        {
          assert (length (firstn (nss t1) l) >= nss t1).
          {
            eapply anno_some_fact; eauto.
          }
          eapply firstn_factt; eauto.
        }

        assert (length l = length (firstn (nss t1) l) + length (skipn (nss t1) l)).
        {
          eapply firstn_skipn_len; eauto.
        }
        lia.
    +
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto).
      ++
        
        assert (length ((firstn (nss t1) l)) < nss t1).
        {
          eapply list_too_short; eauto.
        }
        (*
         assert (length l = length (firstn (nss t1) l) + length (skipn (nss t1) l)).
        {
          eapply firstn_skipn_len; eauto.
        }
         *)
        assert (length l < nss t1).
        {
          eapply firstn_fact'; eauto.
        }
        lia.
  -
    ff;
      try (eauto; tauto);
      try lia.
    +
      destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto; tauto).
      ++
      
      assert (length (skipn (nss t1) l1) < nss t2).
      {
        eapply list_too_short; eauto.
      }

      assert (length (firstn (nss t1) l1) = nss t1).
      {

        assert (length (firstn (nss t1) l1) >= nss t1).
        {
          eapply anno_some_fact; eauto.
        }

        eapply firstn_factt; eauto.
      }
      list_facts.

      lia.

      (*

      assert (length l3 = length (firstn (nss t1) l3) + length (skipn (nss t1) l3)).
        {
          eapply firstn_skipn_len; eauto.
        }
        lia. *)
    +
       destruct b;
        try (exfalso;
             eapply false_succeeds;
             eauto; tauto).
       ++
         assert (length (firstn (nss t1) l1) < nss t1).
         {
           eapply list_too_short; eauto.
         }

         assert (length l1 < nss t1).
         {
           eapply firstn_fact'; eauto.
         }

         lia.
    +
      destruct b.
      ++
        ff.
      ++
        ff.
        (*
    +
      destruct b;
        ff. *)
*)
      Unshelve.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      (*
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto. *)
Defined.

(*
Lemma anno_len_exact:
  forall t i j ls t',
    anno t i ls true = Some (j, ([], t')) ->
    length ls = anss t'.
Proof.
  intros.
  assert (length ls = anss t' + (length ([]:list nat))).
  {
    eapply anno_len; eauto.
  }
  simpl in *.
  lia.
Defined.
*)



Lemma lrange_nss: forall t i ls  n a,
    length ls = nss t ->
    anno t i ls true = Some (n, a) ->
    length (lrange a) = nss t. (* + length ls'. *)
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
    ff.
Defined.

(*

    
    
    ff; eauto.

    assert (length (lrange a0) = nss t1) by eauto.

    assert (length (lrange a1) = nss t2) by eauto.

    assert (length (firstn (nss t1) ls) = nss t1).
    {
      assert (length (firstn (nss t1) ls) >= nss t1).
      {
        eapply anno_some_fact; eauto.
      }

      eapply firstn_factt; eauto.
    }

    (*
    assert (length (skipn (nss t1) ls) = nss t2).
    {
      assert (length (skipn (nss t1) ls) >= nss t2).
      {
        eapply anno_some_fact; eauto.
      }

      
      
      admit.
    }
     *)
    

     assert (length ls = length (firstn (nss t1) ls) + length (skipn (nss t1) ls)).
        {
          eapply firstn_skipn_len; eauto.
        }
    
        lia.
  -
    
    
      
    

    (*assert (length (lrange a0) = nss t1) by eauto. *)

    assert (length ls = anss a0 + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a1).
    {
    
      assert (anss a1 = anss a1 + (length ([]:list nat))).
      {
        eauto.
      }
      rewrite H1.
      
      eapply anno_len; eauto.
    }

    

    


    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    lia.
  -
    ff.
    ff.
    ff; eauto.

    assert (length (lrange a1) = nss t2) by eauto.

    assert (length ls = anss a0 + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a1).
    {
      assert (anss a1 = anss a1 + (length ([]:list nat))).
      {
        eauto.
      }
      rewrite H1.
      
      eapply anno_len; eauto.
    }

    


    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    lia.
  -
    ff.
    ff; eauto.

    assert (length (lrange a1) = nss t2) by eauto.

    assert (length l4 = anss a0 + length l).
    {
      eapply anno_len; eauto.
    }

    assert (length l = anss a1).
    {
      assert (anss a1 = anss a1 + (length ([]:list nat))).
      {
        eauto.
      }
      rewrite H1.
      
      eapply anno_len; eauto.
    }

    


    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    erewrite nss_iff_anss.
    Focus 2.
    eassumption.

    lia.
Defined.
*)










Lemma anno_well_formed_r:
  forall t i j ls t',
    (* length ls = nss t ->
    NoDup ls -> *)
    anno t i ls false = Some (j, t') ->
    well_formed_r t'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff.
  -
    ff.
    +
      econstructor.
      eauto.
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

      simpl.
      assert (n0 > S i) by (eapply anno_mono; eauto).
      lia.
    +
      econstructor.
      eauto.
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

      simpl.
      assert (n0 > S i) by (eapply anno_mono; eauto).
      lia.
    +
      econstructor.
      eauto.
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

      simpl.
      assert (n0 > S i) by (eapply anno_mono; eauto).
      lia.
  -
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
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
  -
        ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.
  -  
    ff.
    econstructor.
    eauto.
    eauto.

     simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia.

      econstructor.
      eauto.
      eauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
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

       assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia.

      econstructor.
      eauto.
      eauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
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

       assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia.

      (*

            econstructor.
      eauto.
      eauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
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

       assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia.


            econstructor.
      eauto.
      eauto.

      simpl.
      erewrite anno_range.
      Focus 2.
      eassumption.
      tauto.

      simpl.
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

       assert (n > (S i)) by (eapply anno_mono; eauto).

      assert (n0 > n) by (eapply anno_mono; eauto).

      repeat erewrite anno_range.
      Focus 2.
      eassumption.
      Focus 2.
      eassumption.

      simpl.
      lia. *)
*)
Defined.

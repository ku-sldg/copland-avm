Require Import Term_Defs StructTactics Preamble Term_Facts.

Require Import Lia.

Require Import List.
Import List.ListNotations.

Lemma same_anno_range: forall t i l l' l2 l2' a b n n' bo bo',
    anno t i l bo = Some (n, (l',a)) ->
    anno t i l2 bo' = Some (n', (l2',b)) ->
    n = n'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff.
  -
    ff.
  -
    ff.
    assert (n0 = n2) by eauto.
    subst.
    assert (n = n') by eauto.
    tauto.
  -
     ff.

    assert (n0 = n2) by eauto.
    subst.
    assert (n3 = n1) by eauto.
    congruence.
  -
     ff;
       try (
           repeat (new_anno_eq; subst);
           congruence).
  Defined.
  
Lemma anno_mono : forall (t:Term) (i j:nat) (t':AnnoTerm) (ls ls':LocRange) b,
  anno t i ls b = Some (j, (ls',t')) ->
  j > i.
Proof.
  induction t; intros i j t' ls ls' b H;
    try (
        simpl in *;
        try destruct b;
        repeat break_let;
        repeat break_match;
        try solve_by_inversion;
        find_inversion;
        repeat find_apply_hyp_hyp;
        lia).
Defined.
Hint Resolve anno_mono : core.

Lemma anno_range:
  forall x i j ls ls' t' b,
     anno x i ls b = Some (j, (ls',t')) ->
    
    range (t') = (i, j).
Proof.
  induction x; intros; simpl in *; auto;
    repeat expand_let_pairs;
    repeat break_match;
    try solve_by_inversion;
    simpl; auto.
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

Lemma both_subsets{A:Type}: forall (ls ls': list A),
  list_subset ls ls' ->
  list_subset ls' ls ->
  ls = ls'.
Proof.
Admitted.


Lemma anno_lrange:
  forall x i j ls ls' t' b,
    length ls = nss x ->
    anno x i ls b = Some (j, (ls',t')) ->
    list_subset ls (lrange t').
Proof.
  induction x; intros;
    try (
        simpl in *; auto;
        repeat break_match; try solve_by_inversion;
        repeat find_inversion;
        simpl in *;
        repeat expand_let_pairs;
        repeat break_match; try solve_by_inversion;
        try unfold list_subset;
        simpl in *; tauto).
  -
    destruct a;
      simpl in *;
      repeat expand_let_pairs;
      repeat break_match;
      find_inversion;
      simpl;
      assert (ls' = []) by (destruct ls'; solve_by_inversion);
      congruence.
  -
    ff.
    assert (ls' = []) by (destruct ls'; solve_by_inversion);
      congruence.
Defined.

Lemma anno_lrange'
  : forall (x : Term) (i j : nat) (ls : list nat) 
      (ls' : LocRange) (t' : AnnoTerm),
    (*length ls = nss x -> *)
    anno x i ls true = Some (j, (ls', t')) ->
    list_subset (lrange t') ls.
Proof.
  intros.
  generalizeEverythingElse x.
  induction x; intros.
  -
    destruct a;
    
      ff;
      unfold list_subset;
      intros;
      solve_by_inversion.
  -
    ff.
    unfold list_subset.
    intros.
    invc H.
    econstructor.
    eauto.
    invc H0.
    right.
    left.
    eauto.
    solve_by_inversion.
  -
    ff.
    unfold list_subset.
    eauto.
  -
    ff.
    unfold list_subset.
    eauto.
  -
    ff.
    unfold list_subset.
    eauto.
Defined.

Lemma both_anno_lrange
  : forall (x : Term) (i j : nat) (ls : list nat) 
      (ls' : LocRange) (t' : AnnoTerm),
    length ls = nss x ->
    anno x i ls true = Some (j, (ls', t')) ->
    list_subset (lrange t') ls /\ list_subset ls (lrange t').
Proof.
  split.
  - eapply anno_lrange'; eauto.
  - eapply anno_lrange; eauto.
Defined.

Lemma anno_lrange_eq
  : forall (x : Term) (i j : nat) (ls : list nat) 
      (ls' : LocRange) (t' : AnnoTerm),
    length ls = nss x ->
    anno x i ls true = Some (j, (ls', t')) ->
    ls = (lrange t').
Proof.
  intros.
  edestruct both_anno_lrange; eauto.
  eapply both_subsets; eauto.
Defined.

(*
Lemma lrange_anno_mono': forall (t:Term) (i j:nat) (t':AnnoTerm) (ls ls':LocRange),
    length ls = nss t ->
    anno t i ls = Some (j, (ls', t')) ->
    length ls = length (lrange t') /\ list_subset ls' ls.
    (* fst (lrange t') >= loc. *)
Proof.
*)


Lemma anno_sub': forall t i ls n l a,
    anno t i ls true = Some (n, (l, a)) ->
    list_subset l ls.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
    
      ff;
      unfold list_subset; eauto.
  -
    ff.
    unfold list_subset.
    intros.
    right.
    right.
    eauto.
    (*
    invc H.
    right.
    right.
    econstructor. eauto.
    solve_by_inversion. *)
  -
    ff.
    unfold list_subset.
    intros.

    assert (list_subset l l0) by eauto.

    unfold list_subset in *.
    specialize H0 with (x:=x).
    concludes.

    assert (forall x:nat, In x l0 -> In x ls).
    {
      eapply IHt1; eauto.
    }
    eauto.
  -
    ff.
    unfold list_subset.
    intros.

    assert (list_subset l l0) by eauto.

    unfold list_subset in *.
    specialize H0 with (x:=x).
    concludes.

    assert (forall x:nat, In x l0 -> In x ls).
    {
      eapply IHt1; eauto.
    }
    eauto.
  -

    ff.
    unfold list_subset.
    intros.

    assert (list_subset l l0) by eauto.

    unfold list_subset in *.
    specialize H0 with (x:=x).
    concludes.

    assert (forall x:nat, In x l0 -> In x l5).
    {
      eapply IHt1; eauto.
    }
    right.
    right.
    right.
    right.
    eauto.
Defined.

Lemma anno_len:
  forall t i j ls ls' t',
    anno t i ls true = Some (j, (ls', t')) ->
    length ls = anss t' + length ls'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      ff.
  -
    ff.
      
  -
    ff.
    assert (length ls = anss a + length l) by eauto.
    assert (length l = anss a0 + length ls') by eauto.
    lia.
  -
    ff.
    assert (length ls = anss a + length l) by eauto.
    assert (length l = anss a0 + length ls') by eauto.
    lia.
  -
    ff.
    assert (length l4 = anss a + length l) by eauto.
    assert (length l = anss a0 + length ls') by eauto.
    lia.
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

Lemma nss_iff_anss: forall t i ls n l a b,
    anno t i ls b = Some (n, (l, a)) ->
    nss t = anss a.
Proof.
    intros.
  generalizeEverythingElse t.
  induction t; intros.
    -
      destruct a;
        ff.
    -
      ff.
    -
      ff.
      eauto.
    -
      ff.
      eauto.
    -
      ff.

      assert (nss t1 = anss a0) by eauto.
      assert (nss t2 = anss a1) by eauto.
      lia.

      assert (nss t1 = anss a0) by eauto.
      assert (nss t2 = anss a1) by eauto.
      lia.

      assert (nss t1 = anss a0) by eauto.
      assert (nss t2 = anss a1) by eauto.
      lia.

      assert (nss t1 = anss a0) by eauto.
      assert (nss t2 = anss a1) by eauto.
      lia.

      assert (nss t1 = anss a0) by eauto.
      assert (nss t2 = anss a1) by eauto.
      lia.
Defined.

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

    assert (length l < nss t2) by eauto.

    assert (length ls = nss t1 + length l).
    {
      erewrite nss_iff_anss.
      Focus 2.
      eassumption.
      eapply anno_len; eauto.
    }
    lia.

    assert (length ls < nss t1) by eauto.
    lia.
  -
    ff.

    assert (length l < nss t2) by eauto.

    assert (length ls = nss t1 + length l).
    {
      erewrite nss_iff_anss.
      Focus 2.
      eassumption.
      eapply anno_len; eauto.
    }
    lia.

    assert (length ls < nss t1) by eauto.
    lia.
  -
    
    ff;
      try lia.
    +
      

    assert (length l < nss t2) by eauto.

    assert (length l3 = nss t1 + length l).
    {
      erewrite nss_iff_anss.
      Focus 2.
      eassumption.
      eapply anno_len; eauto.
    }
    lia.
    +
      assert (length l2 < nss t1) by eauto.

      lia.
Defined.

 Require Import Coq.Program.Tactics.

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

Lemma lrange_nss: forall t i ls  n a,
    anno t i ls true = Some (n, ([], a)) ->
    length (lrange a) = nss t. (* + length ls'. *)
Proof.

  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    cbn in H.
    cbn.
    destruct a; ff.
  -
    ff; eauto.
  -
    ff.
    ff; eauto.

    assert (length (lrange a1) = nss t2) by eauto.

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












Lemma anno_well_formed_r:
  forall t i j ls ls' t',
    (* length ls = nss t ->
    NoDup ls -> *)
    anno t i ls false = Some (j, (ls', t')) ->
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
Defined.

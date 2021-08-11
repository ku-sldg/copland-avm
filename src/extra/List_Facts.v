Require Import Defs StructTactics Preamble More_lists.

Require Import Coq.Program.Tactics.

Require Import List Lia.
Import List.ListNotations.



Lemma firstn_fact: forall (ls: list nat) n,
    length ls >= n ->
    length (firstn n ls) = n.
Proof.
  apply firstn_length_le.
Defined.

Lemma firstn_fact': forall (ls:list nat) n,
    length (firstn n ls) < n ->
    length ls < n.
Proof.
  induction ls; intros; simpl.
  -
    rewrite firstn_nil in *.
    tauto.
  -
    destruct n;
      ff;
      try (assert (length (firstn n ls) < n) by lia);
      eauto.
    +
      assert (length ls < n) by eauto.
      lia.
Defined.

Lemma firstn_factt: forall (ls:list nat) n,
    length (firstn n ls) >= n ->
    length (firstn n ls) = n.
Proof.
  intros.
  assert (length (firstn n ls) <= n).
  {
    eapply firstn_le_length.
  }
  lia.
Defined.

Lemma firstn_skipn_len: forall (ls:list nat) n,
    length ls = length (firstn n ls) + length (skipn n ls).
Proof.
  intros.
  assert ( ls = 
           (firstn n ls) ++ (skipn n ls)).
  {
    symmetry.
    eapply firstn_skipn.
  }
  rewrite H at 1.
  eapply app_length; eauto.
Defined.

Lemma nodup_extra_app : forall (ls ls' : list nat),
    NoDup (ls ++ ls') -> NoDup ls /\ NoDup ls'.
Proof.
  intros.
  generalizeEverythingElse ls.
  induction ls; destruct ls'; intros.
  -
    split; econstructor.
  -
    simpl in *.
    split.
    econstructor.
    eassumption.
  -
    simpl in *.
    rewrite app_nil_r in *.
    split; eauto.
    econstructor.
  -
    assert (NoDup (ls ++ (n :: ls'))) as HH.
    {
      invc H.
      eassumption.
    }

    edestruct IHls.
    apply HH.

    split.
    +
      invc H.
      unfold not in *.
      econstructor.
      ++
        unfold not in *.
        intros.
        eapply H4.
        eapply in_or_app.
        eauto.
      ++
        edestruct IHls.
        apply H5.
        eassumption.
    +
      eassumption.
Defined.

Lemma nodup_app_not_in: forall (ls ls':list nat),
    NoDup (ls ++ ls') ->
    disjoint_lists ls ls'.
Proof.
  intros.
  unfold disjoint_lists.
  intros.

  edestruct in_split.
  apply H0.

  edestruct in_split.
  apply H1.
  destruct_conjs.
  subst.

  clear H0; clear H1.

  assert (((x0 ++ x :: H2) ++ x1 ++ x :: H3) =
          (((x0 ++ x :: H2) ++ x1 ++ [x]) ++ H3)).
  {
    repeat rewrite <- app_assoc.
    tauto.
  }

  rewrite H0 in *.

  edestruct nodup_extra_app.
  apply H.
  clear H4.

  assert ((x0 ++ x :: H2) ++ x1 ++ [x] =
          x0 ++ ((x :: H2) ++ x1 ++ [x])).
  {
    repeat rewrite <- app_assoc.
    tauto.
  }
  rewrite H4 in *; clear H4.

  edestruct nodup_extra_app.
  apply H1.

  invc H5.
  unfold not in *.
  apply H8.

  eapply in_or_app.
  right.
  eapply in_or_app.
  right.
  econstructor; eauto.
Defined.

Lemma nodup_contra: forall (x: nat) ls ls',
    In x ls  ->
    In x (* y *) ls' ->
    NoDup (ls ++ ls') ->
    False.
Proof.
  intros.
  edestruct in_split.
  apply H.

  edestruct in_split.
  apply H0.
  destruct_conjs.
  subst.
  clear H0.
  clear H.

  eapply nodup_app_not_in with (x:=x).
  apply H1.
  eapply in_or_app.
  right.
  econstructor; eauto.

  eapply in_or_app.
  right.
  econstructor; eauto.
Defined.

Lemma firstn_subset: forall (ls:list nat) n,
    list_subset (firstn n ls) ls.
Proof.
  induction ls; intros; ff'; intros.
  -
    rewrite firstn_nil in *.
    ff'.
  -
    destruct n.
    +
      ff'.
    +
      ff'.
      destruct_disjunct.
      ++
        ff.
      ++
        eauto.
Defined.

Lemma skipn_subset: forall (ls:list nat) n,
    list_subset (skipn n ls) ls.
Proof.
  induction ls; intros; ff'; intros.
  -
    rewrite skipn_nil in *.
    ff'.
  -
    destruct n.
    +
      ff'.
    +
      ff'.
      right. eauto.
Defined.

Lemma nodup_firstn: forall (ls:list nat) n,
    NoDup ls ->
    NoDup (firstn n ls).
Proof.
  induction ls; intros.
  -
    rewrite firstn_nil.
    ff'.
  -
    ff'.
    invc H.
    edestruct IHls.
    +
      eassumption.
    +
      
      unfold not in *.

      destruct n.
      ++
        ff'.
        econstructor.
      ++
        ff'.
        econstructor.
        +++
          unfold not in *; intros.
          apply H2.
          eapply firstn_subset; eauto.
        +++
          eauto.
    +
      ff'.
      destruct n.
      ++
        ff'.
        econstructor.
      ++
        ff'.
        econstructor.
        +++
          unfold not in *; intros.
          apply H2.
          eapply firstn_subset; eauto.
        +++

          eauto.
          Unshelve.
          eauto.
Defined.

Lemma nodup_skipn: forall (ls:list nat) n,
    NoDup ls ->
    NoDup (skipn n ls).
Proof.
  induction ls; intros.
  -
    rewrite skipn_nil.
    ff'.
  -
    ff'.
    invc H.
    edestruct IHls.
    +
      eassumption.
    +
      
      unfold not in *.

      destruct n.
      ++
        ff'.
        econstructor.
        +++
          eauto.
        +++
          eauto.
          
      ++
        ff'.
    +
      ff'.
      destruct n.
      ++
        ff'.
        econstructor.
        +++
          eauto.
        +++
          eauto.
      ++
        ff'.
        Unshelve.
        eauto.
Defined.

Lemma list_subset_app: forall (ls ls' l2:list nat),
    list_subset ls l2 ->
    list_subset ls' l2 ->
    list_subset (ls ++ ls') l2.
Proof.
  intros.
  ff'.
  intros.

  Search (In _ (_ ++ _) -> _).

  edestruct in_app_or.
  +
    eassumption.
  +
    eauto.
  +
    eauto.
Defined.

Ltac do_firstn_skipn_len :=
  repeat
    match goal with
    | [H: context[firstn ?n ?ls],
          H': context[skipn ?n' ?ls] |- _] =>
      assert_new_proof_by (length ls = length (firstn n ls) + length (skipn n' ls)) ltac:(eapply firstn_skipn_len)
    end.

Ltac do_firstn_factt :=
  repeat
    match goal with
    | [H: length ?ls (*(firstn ?n ?ls)*) >= ?n |- _] =>
      assert_new_proof_by (length ls (*(firstn n ls)*) = n)
                          ltac:(try (eapply firstn_factt; apply H);
                                try lia)
    end.

(*
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
*)

Ltac nodup_inv :=
  repeat 
    match goal with
    | [H: NoDup (_::_) |- _] => invc H
    end.

(*
Ltac inv_in :=
  match goal with
  | [H: In _ [_] |- _] =>
    invc H
  end.
*)

Ltac inv_in :=
  repeat
  match goal with
  | [H: In _ (?C _) |- _] =>
    invc H
  end.





Ltac do_firstn_skipn :=
  repeat
    match goal with
    | H:context [ firstn ?n ?ls ], H':context [ skipn ?n ?ls ]
      |- _ =>
      assert_new_proof_by (ls = firstn n ls ++ (skipn n ls))
                          ltac:(try symmetry; eapply firstn_skipn)
    end.

Ltac do_nodup_firstn :=
  repeat
  match goal with
  |[H: NoDup ?ls,
       H': context [firstn ?n ?ls] |- _] =>
   assert_new_proof_by (NoDup (firstn n ls))
                       ltac:(eapply nodup_firstn; eauto)
  end.

Ltac do_nodup_skipn :=
  repeat
  match goal with
  |[H: NoDup ?ls,
       H': context [skipn ?n ?ls] |- _] =>
   assert_new_proof_by (NoDup (skipn n ls))
                       ltac:(eapply nodup_skipn; eauto)
  end.

Ltac do_nodup_contra :=
  try
  match goal with
  |[H: In ?x ?ls,
       H': In ?x ?ls',
           H'': NoDup (?ls ++ ?ls') |- _] =>
   exfalso; (eapply nodup_contra; [apply H | apply H' | apply H'']); tauto
  end.

Ltac do_nodup :=
  repeat (
      nodup_inv; inv_in;
      ff;
      nodup_inv; inv_in;
      unfold not in *; try intro;
      econstructor;
      try intro;
      inv_in;
      try (conclude_using ltac:(econstructor; eauto))).

Ltac nodup_list_firstn :=
  repeat
  match goal with
    [H: context[firstn _ ?l] |- _ ] =>
    assert_new_proof_by (NoDup l) do_nodup
  end.

Ltac nodup_list_skipn :=
  repeat
  match goal with
    [H: context[skipn _ ?l] |- _ ] =>
    assert_new_proof_by (NoDup l) do_nodup
  end.









(*
Lemma nodup_extra_app
  : forall ls ls' ls'' : list nat, NoDup (ls ++ ls') -> NoDup ls.
Proof.
Admitted.
 *)


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

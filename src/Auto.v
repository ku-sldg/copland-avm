(*
Automation scripts.  Some generic, but most specific to this development.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import GenStMonad StructTactics MonadVM MonadVMFacts Term.
Require Import Coq.Arith.Peano_dec Lia.

Ltac dunit :=
  match goal with
  | [H:unit |- _] => destruct H
  end.

Ltac annogo := vmsts; repeat dunit.

Ltac df :=
  repeat (
      cbn in *;
      unfold runSt in *;
      repeat break_let;
      repeat (monad_unfold; cbn in *; find_inversion);
      monad_unfold;
      repeat dunit;
      unfold snd in * ).

Ltac dosome :=
  repeat (
      match goal with
      | [H: match ?o with
            | Some _ => _
            | _ => _
            end
            =
            (Some _, _) |- _] =>
        destruct o; try solve_by_inversion
      end; df).

Ltac subst' :=
  match goal with
  | [H: ?A = _, H2: context[?A] |- _] => rewrite H in *; clear H
  | [H: ?A = _ |- context[?A]] => rewrite H in *; clear H
  end.

Ltac subst'' :=
  match goal with
  | [H:?A = _, H2: context [?A] |- _] => rewrite H in *
  | [H:?A = _ |- context [?A]] => rewrite H in *
  end.

Ltac fail_if_in_hyps H := 
  let t := type of H in 
  lazymatch goal with 
  | [G : t |- _ ] => fail "There is already a hypothesis of this proof"
  | [_ : _ |- _ ] => idtac
  end.

Ltac pose_new_proof H := 
  fail_if_in_hyps H;
  pose proof H.

Ltac fail_if_in_hyps_type t := 
  lazymatch goal with 
  | [G : t |- _ ] => fail "There is already a hypothesis of this type"
  | [_ : _ |- _ ] => idtac
  end.

Ltac assert_new_proof_by H tac := 
  fail_if_in_hyps_type H;
  assert H by tac.

Ltac assert_new_proof_as_by H tac n := 
  fail_if_in_hyps_type H;
  assert H as n by tac.

Ltac jkjk :=
  match goal with
  | [H: context[?X] |- ?X = _] => rewrite H
  end.

Ltac jkjk' :=
  match goal with
  | H: _ |- _ => rewrite H; reflexivity
  end.

Lemma hhh : forall t1 t2 a b c d r s,
    well_formed (abpar r (a,b) (c,d) s t1 t2) -> 
    (*range t1 = (a,b) ->
    range t2 = (c,d) -> *)
    PeanoNat.Nat.eqb a c = false.
Proof.
Admitted.


(*

Lemma hhh : forall t1 t2 a b c d r s,
    well_formed (abpar r s t1 t2) -> 
    range t1 = (a,b) ->
    range t2 = (c,d) ->
    PeanoNat.Nat.eqb a c = false.
Proof.
  intros.
  assert (fst (range t1) <> fst (range t2)).
  inv H.
  rewrite H0.
  rewrite H1.
  simpl.
  (*
  eapply afaf; eauto. *)
  subst''.
  subst''.
  simpl in *.
  lia.
  rewrite PeanoNat.Nat.eqb_neq in *.
  subst''.
  subst''.
  simpl in *.
  lia.
Defined.

Lemma faf : forall n,
    n > 0 -> 
    n <> n - 1.
Proof.
  intros.
  lia.
Defined.
 *)


Lemma hhhh : forall t1 t2 a b c d r s,
    well_formed (abpar r (a,b) (c,d) s t1 t2) ->
    (*range t1 = (a,b) ->
    range t2 = (c,d) -> *)
    PeanoNat.Nat.eqb c b (*(b - 1)*) = false.
Proof.
Admitted.

(*

Lemma hhhh : forall t1 t2 a b c d r s,
    well_formed (abpar r s t1 t2) ->
    range t1 = (a,b) ->
    range t2 = (c,d) ->
    PeanoNat.Nat.eqb c (b - 1) = false.
Proof.
  intros.
  inversion H.
  subst.
  assert (c = fst (range t2)).
  {
    jkjke.
  }

  assert (a = fst (range t1)).
  {
    jkjke.
  }

  assert (b = snd (range t1)).
  {
    jkjk.
    tauto.
  }

  assert (d = snd (range t2)).
  {
    jkjke.
  }
  
  rewrite H2.
  rewrite H4.
  rewrite H9.

  assert (fst (range t2) > 0).
  {
    lia.
  }
  
  assert ((fst (range t2)) <> (fst (range t2) - 1)).
  {
    eapply faf; eauto.
  }
  eapply PeanoNat.Nat.eqb_neq; eauto.
Defined.

*)


(*
Lemma ppp{A:Type} : forall x:(A*A),
    x = (fst x, snd x).
Proof.
  intros.
  destruct x.
  simpl.
  tauto.
Defined.

Lemma wf_term_greater : forall t a b,
    well_formed t ->
    range t = (a,b) ->
    b > a.
Proof.
  induction t; intros.
  -
    destruct a;
      try (simpl in *;
           inv H;
           simpl in *;
           lia).
  -
    simpl in *.
    subst.
    inv H.
    simpl in *.
    assert (snd (range t) > fst (range t)).
    eapply IHt.
    eauto.  
    apply ppp.
    lia.
  -
    inv H.
    assert (snd (range t1) > fst (range t1)).
    eapply IHt1.
    eauto.
    apply ppp.

    assert (snd (range t2) > fst (range t2)).
    eapply IHt2.
    eauto.
    apply ppp.

    simpl in *.
    subst.
    simpl in *.
    lia.
  -
    inv H.
    assert (snd (range t1) > fst (range t1)).
    eapply IHt1.
    eauto.
    apply ppp.

    assert (snd (range t2) > fst (range t2)).
    eapply IHt2.
    eauto.
    apply ppp.

    simpl in *.
    subst.

    simpl in *.
    lia.
  -
    inv H.
    assert (snd (range t1) > fst (range t1)).
    eapply IHt1.
    eauto.
    apply ppp.

    assert (snd (range t2) > fst (range t2)).
    eapply IHt2.
    eauto.
    apply ppp.

    simpl in *.
    subst.

    simpl in *.
    lia.
Defined.
 *)

Lemma hhhhh : forall t1 t2 a b c d r s,
    well_formed (abpar r (a,b) (c,d) s t1 t2) ->
    (*range t1 = (a,b) ->
    range t2 = (c,d) -> *)
    PeanoNat.Nat.eqb b d (* (b - 1) (d - 1) *) = false.
Proof.
Admitted.





(*
Lemma hhhhh : forall t1 t2 a b c d r s,
    well_formed (abpar r s t1 t2) ->
    range t1 = (a,b) ->
    range t2 = (c,d) ->
    PeanoNat.Nat.eqb (b - 1) (d - 1) = false.
Proof.
  intros.
  inversion H.
  subst.
  assert (c = fst (range t2)).
  {
    jkjke.
  }

  assert (a = fst (range t1)).
  {
    jkjke.
  }

  assert (b = snd (range t1)).
  {
    jkjk.
    tauto.
  }

  assert (d = snd (range t2)).
  {
    jkjke.
  }

  assert (b <> d).
  {
    assert (b = c).
    {
      lia.
    }
    
    assert (b > a).
    {
      eapply wf_term_greater.
      apply H6.
      eauto.
    }

    assert (d > c).
    {
      eapply wf_term_greater; eauto.
    }

    lia.
  }

  assert (b > 0).
  {
    lia.
  }

  assert (d > 0).
  {
    assert (d > c).
    {
      eapply wf_term_greater; eauto.
    }
    lia.
  }

  eapply PeanoNat.Nat.eqb_neq.
  lia.
Defined.
*)

Lemma abpar_store_non_overlap : forall t1 t2 a b c d r s,
    well_formed (abpar r (a,b) (c,d) s t1 t2) ->
    (*range t1 = (a,b) ->
    range t2 = (c,d) -> *)
    PeanoNat.Nat.eqb a c = false /\
    PeanoNat.Nat.eqb c b (* (b - 1) *) = false /\
    PeanoNat.Nat.eqb b d (* (b - 1) (d - 1) *) = false.
Proof.
  intros.
  repeat split.
  eapply hhh; eauto.
  eapply hhhh; eauto.
  eapply hhhhh; eauto.
Defined.

Ltac fail_no_match :=
  match goal with
  | [H: context [match _ with _ => _ end] |- _] => idtac
  | [ |- context [match _ with _ => _ end]] => idtac
  | _ => fail
  end.

Ltac fail_no_match_some :=
  match goal with
  | [H: context [match _ with | Some _ => _ | None => _ end] |- _] => idtac
  | [ |- context [match _ with | Some _ => _ | None => _ end] ] => idtac
  | _ => fail
  end.

Ltac htac'' :=
  (*let tac := eapply h''; eauto in *)
  match goal with
  | [H: well_formed (abpar _ (?a,?b) (?c,?d) _ ?t1 ?t2) (*,
        H2: range ?t1 = (?a,?b),
            H3: range ?t2 = (?c,?d) *) |- _] =>
    let W := fresh in
    let X := fresh in
    let Y := fresh in
    let Z := fresh in
    assert (PeanoNat.Nat.eqb a c = false /\
            PeanoNat.Nat.eqb c b (* (b - 1) *) = false /\
            PeanoNat.Nat.eqb b d (* (b - 1) (d - 1) *) = false) as W
        by (eapply abpar_store_non_overlap; [apply H (* | apply H2 | apply H3 *)]);
    destruct W as [X [Y Z]];
    try (rewrite X in *; clear X);
    try (rewrite Y in *; clear Y);
    try (rewrite Z in *; clear Z)
  end.

Ltac dohtac := fail_no_match_some;
               try htac'';
               try rewrite PeanoNat.Nat.eqb_refl in *;
               try rewrite PeanoNat.Nat.eqb_eq in *.

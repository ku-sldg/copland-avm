(* 
  Collection of general (structural) Ltac tactics for simplification and 
  rewriting proof contexts

  Author:  Adam Petz
*)

Require Export StructTactics.

Require Import List.
Import List.ListNotations.

Require Import Coq.Program.Tactics.

Require Import Ltac2.Ltac2.

(* "Do OR":  find a disjunction in hyps and destruct it *)
Ltac door :=
  match goal with
  | [H: _ \/ _  |- _] =>
    destruct H
  end; destruct_conjs.

(* Simplification hammer.  Used at beginning of many proofs in this 
   development.  Conservative simplification, break matches, 
   invert on resulting goals *)
Ltac ff :=
  timeout 5 (
  repeat (
    (* try cbn in *; *)
    try simpl in *;
    try break_match;
    repeat (find_rewrite; clean);
    repeat find_injection;
    simpl in *; subst; eauto;
    try congruence;
    try solve_by_inversion
  )).

Ltac ffa :=
  repeat (ff;
    repeat find_apply_hyp_hyp;
    ff).

Tactic Notation "ffa" "using" tactic2(tac) :=
  repeat (ff;
    repeat find_apply_hyp_hyp;
    tac;
    ff).

Ltac fwd_rw :=
  match goal with
    | [ H : _ = _ |- _ ] => erewrite H
    | [ H : forall _, _ = _ |- _ ] => erewrite H
    | [ H : forall _ _, _ = _ |- _ ] => erewrite H
  end.
Ltac rev_rw :=
  match goal with
    | [ H : _ = _ |- _ ] => erewrite <- H
    | [ H : forall _, _ = _ |- _ ] => erewrite <- H
    | [ H : forall _ _, _ = _ |- _ ] => erewrite <- H
  end.

Ltac rw' :=
  repeat (
    try fwd_rw; simpl in *;
    try rev_rw; simpl in *
  ).

Ltac rw :=
  timeout 5 rw'.

Tactic Notation "rw" "using" tactic2(tac) :=
  timeout 5 (repeat (
    try fwd_rw; simpl in *;
    try rev_rw; simpl in *;
    tac
  )).

Ltac fail_if_in_hyps_type t := 
  lazymatch goal with 
  | [G : t |- _ ] => fail "There is already a hypothesis of this type"
  | [_ : _ |- _ ] => idtac
  end.

Ltac fail_if_in_hyps H := 
  let t := type of H in
  fail_if_in_hyps_type t.

Ltac pose_new_proof H := 
  fail_if_in_hyps H;
  pose proof H.

Ltac assert_new_proof_by H tac := 
  fail_if_in_hyps_type H;
  assert H by tac.

(*  For every implication in proof context, try to apply each other arbitrary
    hyp, assuming the result type of the implication does not already exist
    in the context.  *)
Ltac find_apply_hyp_hyp' :=
  match goal with
  | [ H : _ -> _ , H' : _ |- _ ] =>
    (*let x := fresh in *)
    pose_new_proof (H H')
  end.

Ltac find_pose_new_lem_hyp lem :=
  match goal with
  | [ H : _ |- _ ] => pose_new_proof (lem H)
  end.


(* 
  Collection of general (structural) Ltac tactics for simplification and 
  rewriting proof contexts

  Author:  Adam Petz
*)

Require Import StructTactics.

Require Import List.
Import List.ListNotations.

Require Import Coq.Program.Tactics.

Require Import Ltac2.Ltac2.

(* rewrite (existentially) an arbitrary hypothesis and attempt eauto *)
Ltac jkjke :=
  match goal with
  | [H: _ |-  _ ] => erewrite H; eauto
  end.

(* rewrite <- (existentially) an arbitrary hypothesis and attempt eauto *)
Ltac jkjke' :=
  match goal with
  | [H: _ |-  _ ] => erewrite <- H in *; eauto
  end.

(* attempt to rerwite an arbitrary equality assumption whose LHS is mentioned
   in the proof goal *)
Ltac jkjk :=
  match goal with
  | [H: ?X = _ |- context[?X] ] => rewrite H
  end.

(* attempt to rerwite an arbitrary <- equality assumption whose LHS is  
   mentioned in the proof goal *)
Ltac jkjk' :=
  match goal with
  | [H: ?X = _ |- context[?X] ] => rewrite <- H
  end.

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
  repeat (
    (* try cbn in *; *)
    try simpl in *;
    try break_match;
    repeat (find_rewrite; clean);
    repeat find_injection;
    simpl in *; subst; eauto;
    try congruence;
    try solve_by_inversion
  ).

Ltac ffa :=
  repeat (ff;
    repeat find_apply_hyp_hyp;
    ff).

Tactic Notation "ffa" "using" tactic(tac) :=
  repeat (ff;
    repeat find_apply_hyp_hyp;
    tac;
    ff).

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


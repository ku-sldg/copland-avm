Require Import StructTactics.

Require Import List.
Import List.ListNotations.

Definition list_subset{A:Type} :=
  incl (A:=A).

Lemma pairsinv : forall (a a' b b':nat),
    a <> a' -> (a,b) <> (a',b').
Proof.
  intros.
  congruence.
Defined.

Ltac asdf :=
  match goal with
  | [H: _, H2: _ |- _] => apply H in H2
  end.

Ltac ff :=
  repeat (cbn in *;
          repeat break_match;
          repeat find_inversion;
          try solve_by_inversion).
(*
    repeat find_inversion ). *)

Ltac ff' :=
  repeat (cbn in *;
          repeat break_match; try solve_by_inversion;
          repeat find_inversion;
          unfold list_subset in *;
          unfold incl in * ).

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

Ltac find_apply_hyp_hyp' :=
  match goal with
  | [ H : _ -> _ , H' : _ |- _ ] =>
    (*let x := fresh in *)
    pose_new_proof (H H')
  end.

Ltac find_apply_lem_hyp lem :=
  match goal with
  | [ H : _ |- _ ] => apply lem in H
  end.

Ltac find_apply_lem_hyp_new lem :=
  match goal with
  | [ H : _ |- _ ] => pose_new_proof (lem H) (*apply lem in H *)
  end.

Ltac jkjk :=
  match goal with
  | [H: ?X = _ |-  context[?X] ] => rewrite H
  end.

Ltac jkjk' :=
  match goal with
  | [H: ?X = _ |-  context[?X] ] => rewrite <- H
  end.

(*
Ltac new_anno_eq :=
  match goal with
  | [H: anno ?t ?i ?ls ?b = Some (?n, ?a) (* (?n, (?ls', ?a))*),
        H': anno ?t ?i ?ls2 ?b' = Some (?m, ?a') (* (?m, (?ls2', ?a'))*) |- _] =>
    assert_new_proof_by (n = m) eauto
  end.
 *)


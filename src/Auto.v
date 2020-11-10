Require Import GenStMonad StructTactics MonadVM.
Require Import Coq.Arith.Peano_dec.

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

Ltac jkjk :=
  match goal with
  | [H: context[?X] |- ?X = _] => rewrite H
  end.

Ltac jkjk' :=
  match goal with
  | H: _ |- _ => rewrite H; reflexivity
  end.

Ltac dunit :=
  match goal with
  | [H:unit |- _] => destruct H
  end.

Ltac dohtac := (*try htac; *)
               try rewrite PeanoNat.Nat.eqb_refl in *;
               try rewrite PeanoNat.Nat.eqb_eq in *.


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

Ltac dooit :=
  repeat eexists;
  cbn;
  repeat break_let;
  simpl;
  repeat find_inversion;
  subst';
  df;
  reflexivity.

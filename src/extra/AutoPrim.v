Require Import StructTactics.

Require Import Coq.Program.Tactics.

Ltac dff :=
  repeat (
      cbn in *;
      (*unfold runSt in *; *)
      repeat break_let;
      repeat ((*monad_unfold;*) cbn in *; find_inversion);
      (*monad_unfold;
      repeat dunit; *)
      unfold snd in * ).

Ltac fff := repeat break_match; try solve_by_inversion; dff.

Ltac jkjke :=
  match goal with
  | [H: _ |-  _ ] => erewrite H; eauto
  end.

Ltac jkjke' :=
  match goal with
  | [H: _ |-  _ ] => erewrite <- H in *; eauto
  end.

Ltac door :=
  match goal with
  | [H: _ \/ _  |- _] =>
    destruct H
  end; destruct_conjs.

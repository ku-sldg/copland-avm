(*
  Automation scripts.  Some attempt to be generic, but most are specific to this development.

  Author:  Adam Petz, ampetz@ku.edu
*)

Require Import StructTactics Cvm_Monad.

Require Export Defs.


(* destruct unit-typed hyps *)
Ltac dunit :=
  match goal with
  | [H:unit |- _] => destruct H
  end.

(* destruct cvm_st hyps + unit-typed hyps *)
Ltac annogo := vmsts; repeat dunit.

(* Run a collection of conservative built-in simplifications and 
   custom unfolders.  *)
Ltac df :=
  repeat (
    simpl in *;
    repeat break_let;
    repeat (cvm_monad_unfold; simpl in *; find_inversion);
    cvm_monad_unfold;
    repeat dunit;
    unfold snd in * ).

(* Destruct specific matches on Option types *)
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

(* Slight (non-existential) variation of `jkjke` from Defs.v *)
Ltac jkjk_s :=
  match goal with
  | H: _ |- _ => rewrite H; reflexivity
  end.

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

Ltac dohtac := fail_no_match_some;
               try rewrite PeanoNat.Nat.eqb_refl in *;
               try rewrite PeanoNat.Nat.eqb_eq in *.

(*
Automation scripts.  Some generic, but most specific to this development.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import StructTactics Cvm_Monad Term_Defs Term.
Require Import Coq.Arith.Peano_dec Lia.

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
      cbn in *;
      unfold runErr in *;
      repeat break_let;
      repeat (monad_unfold; cbn in *; find_inversion);
      monad_unfold;
      repeat dunit;
      unfold snd in * ).

(* Common "first swipe" automation tactic throughout this development.  
   Breaks match statements if found, then either solves or simplifies.  *)
Ltac ff := repeat break_match; try solve_by_inversion; df.

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

(* Smarter rewriter *)
Ltac subst' :=
  match goal with
  | [H: ?A = _, H2: context[?A] |- _] => rewrite H in *; clear H
  | [H: ?A = _ |- context[?A]] => rewrite H in *; clear H
  end.

(* Same as subst', but does NOT clear hyps after rewriting *)
Ltac subst'' :=
  match goal with
  | [H:?A = _, H2: context [?A] |- _] => rewrite H in *
  | [H:?A = _ |- context [?A]] => rewrite H in *
  end.

Ltac assert_new_proof_as_by H tac n := 
  fail_if_in_hyps_type H;
  assert H as n by tac.

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
               (*try htac''; *)
               try rewrite PeanoNat.Nat.eqb_refl in *;
               try rewrite PeanoNat.Nat.eqb_eq in *.

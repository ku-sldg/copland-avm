Require Import StructTactics Auto VmSemantics StVM MonadVM GenStMonad.
Require Import Helpers_VmSemantics.
Require Import List.

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

Ltac tacc H :=
  (symmetry;
   erewrite <- pl_immut in *;
   rewrite H;
   eauto ).

Ltac ff := repeat break_match; try solve_by_inversion; df.

Ltac dosome_eq y :=
  match goal with
  | [H: match ?x with _ => _ end = (Some _, _)  |- _] =>
    destruct x eqn:y; try solve_by_inversion
  end.

Ltac do_pair :=
  match goal with
  | [H: (_,_) = (Some _,_) |- _] => invc H
  | [H: (Some _,_) = (_,_) |- _] => invc H
  end.

Ltac dosome_eqj :=
  let y := fresh in 
  match goal with
  | [H: match ?x with _ => _ end = (Some _, _)  |- _] =>
    destruct x eqn:y; try solve_by_inversion
  end.

Ltac dosome'' :=
  match goal with
  | [H: (_,_) = (Some _, _) |- _] => invc H
  end.

Ltac domap :=
  let n := fresh in
  match goal with
  | [H: match ?X with _ => _ end _ = (Some _, _) |- _] =>
    destruct X eqn:n; try solve_by_inversion
  end.


Ltac doit' := repeat dosome_eqj;
              repeat break_let;
              repeat do_pair;
              repeat break_let;
              repeat do_pair;
              repeat dosome''.

Ltac doit := repeat doit'.

(*
  Ltac map_get_subst :=
  match goal with
  | [H: map_get ?A ?B = _,
  H2: context[map_get ?A ?B] |- _] =>
  rewrite H in *; clear H
  end.
 *)

Ltac haaa :=
  let x:= fresh in
  match goal with
  | [H: context[match ?ee with | Some _ => _ | _ => _ end] |- _] =>
    destruct ee eqn:x;
    try solve_by_inversion
  end; df; eauto.

Ltac stt :=
  cbn in *;
  monad_unfold;
  try solve_by_inversion;
  repeat break_let;
  dosome;
  try haaa.

Ltac dosome_eq' y :=
  match goal with
  | H:match ?x with
      | _ => _
      end _ = (Some _, _) |- _ => destruct x eqn:y; try solve_by_inversion
  end.

Ltac dothat :=
  unfold StVM.st_ev, StVM.st_pl, StVM.st_trace, StVM.st_store in *;
  try unfold st_ev in *;
  try unfold st_pl in *;
  try unfold st_trace in *;
  try unfold st_store in *.

Ltac ff' :=
  repeat break_match; try solve_by_inversion.

Ltac do_inv_head :=
  let tac := (eapply app_inv_head; eauto) in
  repeat
    match goal with
    | [H: ?ls ++ ?xs = ?ls ++ ?ys |- _] => assert_new_proof_by (xs = ys) tac
    end.

Ltac doex := 
  unfold extractUev, extractSig, extractComp in *;
  ff';
  unfold ret in *; doit.

(* Misc automation tactics.  Some of these might be repeats or overlap. *)

Require Import StructTactics Auto (* Helpers_CvmSemantics *) Cvm_St Cvm_Monad ErrorStMonad_Coq Cvm_Impl.
Require Import List.

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
  unfold Cvm_St.st_ev, Cvm_St.st_pl, Cvm_St.st_trace in *;
  try unfold st_ev in *;
  try unfold st_pl in *;
  try unfold st_trace in * .

Ltac ff' :=
  repeat break_match; try solve_by_inversion.

Ltac do_inv_head :=
  let tac := (eapply app_inv_head; eauto) in
  repeat
    match goal with
    | [H: ?ls ++ ?xs = ?ls ++ ?ys |- _] => assert_new_proof_by (xs = ys) tac
    end.


(* Characterizing results of CVM execution. 
   TODO:  Need to revisit this to incoporate error results.
   TODO:  Perhaps make assumptions about input manifest fields and executability?

   Noted when CVM used just a State (no Error) Monad: 
      This may need revisiting if we consider more robust models of CVM failure. *)
Lemma always_some : forall t vm_st vm_st' op,
    build_cvm t vm_st = (op, vm_st') ->
    op = resultC tt (* Some tt *).
Proof.
  induction t; intros.
  -
    destruct a; (* asp *)
      try destruct a; (* asp params *)
      try (df; tauto).
  -
    repeat (df; try dohtac; df).
    tauto.
  -
    df.
    break_match; df; eauto.
  -
    df.

    repeat break_match;
      try (
          df; eauto).
  -
    df.
    try dohtac.
    df.
    simpl.

    break_match; ff; eauto.
Defined.

Ltac do_somett :=
  match goal with
  | [H: build_cvm ?t _ = (?o, _)
     |- _] =>
    assert_new_proof_by (o = resultC tt) ltac:(eapply always_some; [apply H])
  end.


Ltac clear_triv :=
  match goal with
  | [H: ?x = ?x |- _] => clear H
  end.

Ltac do_asome := repeat do_somett; repeat clear_triv.

Ltac dd :=
  repeat (
      df;
      annogo;
      dosome;
      do_asome;
      subst).

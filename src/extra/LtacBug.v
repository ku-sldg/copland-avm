Lemma temp{A:Type} : forall (a:A), a = a.
Proof.
  trivial.
Defined.

(*
Set Ltac Debug.
*)

Ltac temp_ltac :=
  match goal with
  | [H: ?a = _ |- _] => apply temp with (a:=a); eauto
  end.

Example temp_ex{A:Type} : forall (c:A), c = c -> c = c.
Proof.
  intros.
  Fail temp_ltac.
  (* Does this evaluate to: apply temp with (c:=c) ? *)
  (* Intent is as follows: *)
  apply temp with (a:=c).
Qed.

Ltac temp_ltac' :=
  match goal with
  | [H: ?b = _ |- _] => apply temp with (a:=b); eauto
  end.

Example temp_ex'{A:Type} : forall (c:A),  c = c -> c = c.
Proof.
  intros.
  temp_ltac'.
Qed.


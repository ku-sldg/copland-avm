Lemma temp{A:Type} : forall (a:A), a = a.
Proof.
  trivial.
Defined.

Set Ltac Debug.

Ltac temp_ltac :=
  match goal with
  | [H: ?a = _ |- _] => apply temp with (a:=a); eauto
  end.

Example temp_ex{A:Type} : forall (c:A), c = c -> c = c.
Proof.
  intros.
  Fail temp_ltac.
  apply temp with (c:=c).
  Check temp.
  eapply temp with (a0:=a).
​
Example temp_ex{A:Type} : forall (c:A),  c = c -> c = c.
Proof.

​
Ltac temp_ltac' :=
  match goal with
  | [H: ?b = _ |- _] => apply temp with (a:=b); eauto
  end.
​
Example temp_ex{A:Type} : forall (c:A),  c = c -> c = c.
Proof.
  intros.
  Fail temp_ltac.
  (* evaluates to:       apply temp with (c:=c); eauto *)
  (* should evaluate to: apply temp with (a:=c); eauto *)
  temp_ltac'.

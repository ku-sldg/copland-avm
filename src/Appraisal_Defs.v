Require Import Term_Defs Term StAM Maps.

Require Import StructTactics.

Require Import List.
Import ListNotations.


Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args tpl tid, evidenceEvent (umeas n p i args tpl tid)
(*| sev: forall n p, evidenceEvent (sign n p) *)
(*
| hev: forall n p, evidenceEvent (hash n p)*). 


Definition measEvent (t:AnnoTerm) (p:Plc) (e:Evidence) (ev:Ev) : Prop :=
  events t p e ev /\ evidenceEvent ev.

Inductive appEvent : Ev -> AM_St -> Ev -> Prop :=
| aeu : forall p p' i i' n n' m args tpl tid st,
    m = st_aspmap st ->
    bound_to m (tpl,i) i' ->
    appEvent (umeas n p i args tpl tid) st (umeas n' p' i' ([n] ++ args) tpl tid).
(*| asu : forall p q i' n n' m  args st,
    m = st_sigmap st ->
    bound_to m p i' ->
    appEvent (sign n p) st (umeas n' q i' ([n] ++ args)). *)

Ltac measEventFacts :=
  match goal with
  | [H: measEvent _ _ _ _ |- _] => invc H
  end.

Ltac evEventFacts :=
  match goal with
  | [H: evidenceEvent _ |- _] => invc H
  end.

Ltac invEvents :=
  match goal with
  | [H: events _ _ _ _  |- _] => invc H
  end.

Require Import List.
(* Generic result type.  Parameterized by the success type (A) 
    and the error type (E). *)
Inductive ResultT (A:Type) (E:Type) : Type := 
| errC : E -> ResultT A E
| resultC : A -> ResultT A E.

Arguments errC {A} {E} e.
Arguments resultC {A} {E} a.

Definition res_ret {A E : Type} (a : A) : ResultT A E := resultC a.

Definition res_bind {A B E : Type} (m : ResultT A E) (f : A -> ResultT B E) : ResultT B E :=
  match m with
  | resultC v => f v
  | errC e => errC e
  end.

Module ResultNotation.

Notation "x <- c1 ;; c2" := (@res_bind _ _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).

Notation "' pat <- c1 ;; c2" :=
    (@res_bind _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity).

End ResultNotation.

Import ResultNotation.

Fixpoint result_map {A B E : Type} (f : A -> ResultT B E) (l : list A) 
    : ResultT (list B) E :=
  match l with
  | nil => resultC nil
  | (cons h t) =>
      v <- f h;;
      vs <- result_map f t;;
      resultC (cons v vs)
  end.

Lemma result_map_spec : forall {X Y Z : Type} (l : list X) (f : X -> ResultT Y Z) x (res : list Y),
  In x l ->
  result_map f l = resultC res ->
  (exists fx', (f x) = resultC fx' /\
    In fx' res).
Proof.
  induction l; simpl in *; intuition; eauto;
  unfold res_ret, res_bind in *; simpl in *; subst; intuition; eauto.
  - destruct (f x); intuition; try congruence. 
    destruct (result_map f l); intuition; try congruence.
    inversion H0; subst;
    exists y; simpl in *; eauto.
  - destruct (f a) eqn:E1; intuition; try congruence. 
    destruct (result_map f l) eqn:E2; intuition; try congruence.
    pose proof (IHl _ _ _ H1 E2); eauto.
    inversion H0; subst;
    destruct H; intuition.
    exists x0; simpl in *; eauto.
Qed.

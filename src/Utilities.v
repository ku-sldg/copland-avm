(** Decidable equality with uninterpreted functions *)

Ltac equality := intuition congruence.

(** Propositional logic *)

Ltac propositional := intuition idtac.

(** Inversion with the other things inversion should do *)

Ltac inverts t := inversion t; subst; clear t.

(** Print the goal *)

Ltac print_goal := match goal with
                     |- ?g => idtac g
                   end.

(** Nifty encapsulation of [dependent destruction] from Chlipalla *)

Ltac dep_destruct E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
        end.

(** Not sure if this makes sense, but we'll keep it around as the dual of
 * the [destruct] version.
 *)

Ltac dep_induct E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent induction x;
      try match goal with
            | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
          end.

(* Some general tactics *)

Ltac right_dest_contr H := right; unfold not; intros H; destruct H; contradiction.
Ltac right_intro_inverts := right; unfold not; intros H'; inverts H'.
Ltac right_dest_inverts := right; unfold not; intros H; inverts H.
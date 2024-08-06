(*
General definition of an option monad + monadic notations.
Borrowed/tweaked from:  
https://github.com/uwplse/verdi/blob/master/core/StateMachineHandlerMonad.v

Author:  Adam Petz, ampetz@ku.edu
*)

(* Generalized Option Monad *)
Definition Opt (A : Type) : Type := (option A). (** S % type. *)

Definition opt_ret {A : Type} (a : A) : Opt A := (Some a).

Definition opt_bind {A B : Type} (m : Opt A) (f : A -> Opt B) : Opt B :=
    match m with
    | Some v => f v
    | _ => None
    end.

Definition opt_failm {A : Type} : Opt A := None.

Module OptNotation.

Notation "a >> b" := (opt_bind a (fun _ => b)) (at level 50).

Notation "x <- c1 ;; c2" := (@opt_bind _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).


Notation "' pat <- c1 ;; c2" :=
    (@opt_bind _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity).

End OptNotation.

Import OptNotation.

Definition opt_when {A} (b : bool) (m : Opt A) : Opt unit :=
  if b then m ;; opt_ret tt else opt_ret tt.


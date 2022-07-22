(*
General definition of an option monad + monadic notations.
Borrowed/tweaked from:  
https://github.com/uwplse/verdi/blob/master/core/StateMachineHandlerMonad.v

Author:  Adam Petz, ampetz@ku.edu
*)

(* Generalized Option Monad *)
Definition Opt (A : Type) : Type := (option A). (** S % type. *)

Definition ret {A : Type} (a : A) : Opt A := (Some a).

Definition bind {A B : Type} (m : Opt A) (f : A -> Opt B) : Opt B :=
    match m with
    | Some v => f v
    | _ => None
    end.

Definition failm {A : Type} : Opt A := None.

Definition runOpt {A} (h : Opt A) (default: A) : A :=
  match h with
    Some v => v
  | _ => default
  end.

Definition nop := ret tt.

Notation "a >> b" := (bind a (fun _ => b)) (at level 50).

Notation "x <- c1 ;; c2" := (@bind _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).


Notation "' pat <- c1 ;; c2" :=
    (@bind _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity).

Definition when {A} (b : bool) (m : Opt A) : Opt unit :=
  if b then m ;; ret tt else nop.


Definition fromSome{A:Type} (default:A) (opt:Opt A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.

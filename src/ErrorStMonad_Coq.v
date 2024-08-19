(*
General definition of a state monad with error + monadic notations, 
  borrowed/tweaked from:  https://github.com/uwplse/verdi/blob/master/core/StateMachineHandlerMonad.v

Primary Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs ResultT.
Export ResultT.

(* Generalized Error + State Monad *)
Definition Err(S A E: Type) : Type := S -> (ResultT A E) * S % type.

Definition err_ret {S A E : Type} (a : A) : Err S A E := fun s => (resultC a, s).

Definition err_bind {S A B E : Type} (m : Err S A E) (f : A -> Err S B E) : Err S B E :=
  fun s =>
    let '(a, s') := m s in
    match a with
    | resultC v =>
      let '(b, s'') := f v s' in
      (b, s'')
    | errC e => (errC e,s')
    end.

Definition err_failm {S A E : Type} (e:E) : Err S A E := fun s => (errC e, s).

Definition err_modify {S E} (f : S -> S) : Err S unit E := fun s => (resultC tt, f s).

Definition err_put {S E} (s : S) : Err S unit E := fun _ => (resultC tt, s).

Definition err_get {S E} : Err S S E := fun s => (resultC s, s).

Module ErrNotation.

Notation "a >> b" := (err_bind a (fun _ => b)) (at level 50).

Notation "x <- c1 ;; c2" := (@err_bind _ _ _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).

Notation "' pat <- c1 ;; c2" :=
    (@err_bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity).

End ErrNotation.

Import ErrNotation.

Definition err_gets {S} {A} {E} (f:S -> A) : Err S A E :=
  st <- err_get ;;
  err_ret (f st).

Ltac err_monad_unfold :=
  repeat unfold err_ret, 
    err_bind, 
    err_failm, 
    err_modify, 
    err_put, 
    err_get, 
    err_gets in *.
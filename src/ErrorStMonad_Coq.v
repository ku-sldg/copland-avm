(*
General definition of a state monad with error + monadic notations, 
  borrowed/tweaked from:  https://github.com/uwplse/verdi/blob/master/core/StateMachineHandlerMonad.v

Primary Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs ResultT.
Export ResultT.

(* Generalized Error + State + Config Monad *)
Definition Err(S C A E: Type) : Type := 
  (S * C) -> (ResultT A E) * (S * C)% type.

Definition err_ret {S C A E : Type} (a : A) : Err S C A E := 
  fun s => 
  (resultC a, s).

Definition err_bind {S C A B E : Type} (m : Err S C A E) (f : A -> Err S C B E) : Err S C B E :=
  fun s =>
    let '(a, s') := m s in
    match a with
    | resultC v => f v s'
    | errC e => (errC e,s')
    end.

Definition err_failm {S C A E : Type} (e:E) : Err S C A E := 
  fun s => (errC e, s).

Definition err_modify {S C E} (f : S -> S) : Err S C unit E := 
  fun s => 
    let '(s, c) := s in
    (resultC tt, (f s, c)).

Definition err_put_state {S C E} (s' : S) : Err S C unit E := 
  fun s => 
    let '(s, c) := s in
    (resultC tt, (s', c)).

Definition err_get_state {S C E} : Err S C S E := 
  fun s => 
    let '(s, c) := s in
    (resultC s, (s, c)).

Definition err_get_config {S C E} : Err S C C E := 
  fun s => 
    let '(s, c) := s in
    (resultC c, (s, c)).

Module ErrNotation.

Notation "a >> b" := (err_bind a (fun _ => b)) (at level 50).

Notation "x <- c1 ;; c2" := (@err_bind _ _ _ _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).

Notation "' pat <- c1 ;; c2" :=
    (@err_bind _ _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity).

End ErrNotation.

Import ErrNotation.

Ltac err_monad_unfold :=
  repeat unfold err_ret, 
    err_bind, 
    err_failm, 
    err_modify, 
    err_put_state,
    err_get_state, 
    err_get_config in *.
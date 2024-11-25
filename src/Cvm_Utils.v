Require Import ResultT Term_Defs_Core ErrorStringConstants.

Require Import String.

Require Import List.
Import ListNotations.

Fixpoint peel_n_rawev (n : nat) (ls : RawEv) : ResultT (RawEv * RawEv) string :=
  match n with
  | 0 => resultC ([], ls)
  | S n' =>
    match ls with
    | [] => errC errStr_peel_n_am
    | x :: ls' =>
      match peel_n_rawev n' ls' with
      | errC e => errC e
      | resultC (ls1, ls2) => resultC (x :: ls1, ls2)
      end
    end
  end.
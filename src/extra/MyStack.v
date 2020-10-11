(*
Simple, list-based stack implementation.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import List.
Import ListNotations.

Section GenStack.
  Variable t : Type.
  (*Context `{t : Type}.*)
  (*Variable default_stack_elem : t.*)

  Definition gen_stack := list t.
  Definition empty_stack : list t := [].
  Check empty_stack.

  Definition push_stack (v:t) (s:gen_stack) : (gen_stack) :=
    (v::s).

  Definition pop_stack (s:gen_stack) : option (t*gen_stack) :=
  match s with
  | e :: s' => Some (e,s')
  | _ => None (* TODO: will this be expressive enough? *)
  end.


End GenStack.

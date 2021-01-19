(*


Author:  Adam Petz, ampetz@ku.edu
*)

Require Export ExtLib.Structures.Monads.
Export MonadNotation.
Open Scope monad_scope.

Instance optionMonad : Monad option :=
  {
    ret T x :=
      Some x ;
    bind T U m f :=
      match m with
        None => None
      | Some x => f x
      end
  }.

Definition fromSome{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.
    

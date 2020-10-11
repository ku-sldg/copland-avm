(*


Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term.
Require Import Coq.ZArith.ZArith_base Coq.Strings.String Coq.Strings.Ascii.
Require Import ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.ReaderMonad ExtLib.Structures.Monads ExtLib.Data.Monads.IdentityMonad.

Require Import List.
Import ListNotations.

Import MonadNotation.
Local Open Scope monad_scope.

Record Cop_Env : Type := mkCop_Env
                           { nameServer : NS ;
                             me : Plc}.

(* ident is the identity monad, acting as a place-holder for the base monad.
   TODO:  eventually we need this to be IO (or something that models IO) *)
Definition COP := readerT Cop_Env (ident).

Definition runCOP {A:Type} (k:(COP A)) (env:Cop_Env) : A (* (A * AM_St)*) :=
  unIdent (runReaderT k env).

Definition empty_cop_env := (mkCop_Env [] 0).


Fixpoint foldM_COP {A B : Type} (f:A -> B -> COP A) (a:A) (bs:list B) : COP A :=
  match bs with
  | [] => ret a
  | (x::xs) => f a x >>= fun fax => foldM_COP f fax xs
  end.

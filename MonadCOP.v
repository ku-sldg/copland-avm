Require Import Term.
Require Import Coq.ZArith.ZArith_base Coq.Strings.String Coq.Strings.Ascii.
Require Import ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.ReaderMonad ExtLib.Structures.Monads ExtLib.Data.Monads.IdentityMonad.

Record Cop_Env : Type := mkCop_Env
                           { nameServer : NS ;
                             me : Plc}.

(* ident is the identity monad, acting as a place-holder for the base monad.
   TODO:  eventually we need this to be IO (or something that models IO) *)
Definition COP := readerT Cop_Env (ident).

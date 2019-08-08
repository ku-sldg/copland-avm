Require Import Maps Copland.
Require Import Coq.ZArith.ZArith_base Coq.Strings.String Coq.Strings.Ascii.
Require Import ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.ReaderMonad ExtLib.Structures.Monads ExtLib.Data.Monads.IdentityMonad.
Require Import List.

Import MonadNotation.
Import ListNotations.
Local Open Scope monad_scope.

Definition Policy := nat.
Definition BS := nat.

Record AM_Env : Type := mkAM_Env
                          { myPolicy : Policy}.

Record AM_St : Type := mkAM_St
                         { am_nonceMap : Map nat BS;
                           am_nonceId : nat}.

(* ident is the identity monad, acting as a place-holder for the base monad.
   TODO:  eventually we need this to be IO (or something that models IO) *)
Definition AM := readerT AM_Env (stateT AM_St ident).

Definition empty_state := (mkAM_St [] 0).
Definition init_env := (mkAM_Env 0).

Definition am_updateNonce (bs :BS) : AM nat :=
  let myPol := asks myPolicy in
  am_st <- get ;;
  let m := am_nonceMap am_st in
  let id := am_nonceId am_st in
  let newMap := map_set m id bs in
  let newId := id + 1 in
  put (mkAM_St newMap newId) ;;         
      ret id.

Definition runAM {A:Type} (k:(AM A)) (env:AM_Env) (st:AM_St) : ident (A * AM_St) :=
  runStateT (runReaderT k env) st.

Definition incNonce := runAM (am_updateNonce 42) init_env empty_state.
Compute (unIdent incNonce).




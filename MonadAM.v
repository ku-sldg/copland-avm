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
Definition AM := stateT AM_St (ident).
Context {State_m: MonadReader AM_Env AM}.

Check asks.

Definition empty_state := (mkAM_St [] 0).

Definition am_updateNonce (bs :BS) : AM nat :=
  (*myEnv <- ask ;;
  let myPol := asks myPolicy in *)
  am_st <- get ;;
        let m := am_nonceMap am_st in
        let id := am_nonceId am_st in
        let newMap := map_set m id bs in
        let newId := id + 1 in
        put (mkAM_St newMap newId) ;;         
            ret id.

Print evalState. Check state. Print state. Print evalState.

Definition GameValue := nat.
Definition GameState := AM_St.
Definition main : ident GameValue :=
  evalStateT (am_updateNonce 43) empty_state.

Compute (unIdent main).

(*
Example asdf : (unIdent main = 0).
Proof. simpl. unfold empty_state. unfold map_set. unfold unIdent. unfold runStateT. unfold ask.
  unfold main. simpl. unfold map_set. unfold empty_state.
*)




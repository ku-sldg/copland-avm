(*


Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Coq.ZArith.ZArith_base Coq.Strings.String Coq.Strings.Ascii.
Require Import ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.ReaderMonad ExtLib.Structures.Monads ExtLib.Data.Monads.IdentityMonad.
Require Import List.

Import MonadNotation.
Import ListNotations.
Local Open Scope monad_scope.

Record Env : Type := mk_Env
                          { envA : nat}.

Record St : Type := mk_St
                         { stB : nat}.

Definition M := readerT Env (stateT St ident).
(*Context {State_m: MonadReader Env M}.*)

Definition empty_state := (mk_St 0).
Definition init_env := (mk_Env 0).

Definition inc : M nat :=
  myEnvVal <- asks envA ;;
  myState <- get ;;
  let oldStVal := (stB myState) in
  put (mk_St (oldStVal + 1)) ;;
      ret oldStVal.

Check runReaderT.

Definition incVal :=
  evalStateT (runReaderT inc init_env) empty_state.

Definition incSt : ident St :=
  execStateT (runReaderT inc init_env) empty_state.

Compute (unIdent incVal).
Compute (unIdent incSt).

Definition inc_no_reader : M nat :=
  myState <- get ;;
  let oldStVal := (stB myState) in
  put (mk_St (oldStVal + 1)) ;;
  ret oldStVal.

Definition inc_no_reader_Val : ident nat :=
  evalStateT (inc_no_reader) empty_state.

Definition inc_no_reader_St : ident St :=
  execStateT (inc_no_reader) empty_state.

Compute (unIdent inc_no_reader_Val).
Compute (stB (unIdent inc_no_reader_St)).

Definition just_reader : M nat :=
  myEnvVal <- asks envA ;;
           ret 42.

Definition just_reader_Val : ident nat :=
  evalStateT (just_reader) empty_state.

Definition just_reader_St : ident St :=
  execStateT (just_reader) empty_state.

Compute (unIdent just_reader_Val).
Compute (stB (unIdent just_reader_St)).

Definition R := readerT Env (ident).
Context {asdf: MonadState St R}.

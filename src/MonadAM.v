(*


Author:  Adam Petz, ampetz@ku.edu
*)
Require Import Maps.
Require Import Coq.Arith.EqNat.
Check map_set.

Check map_set.


Require Import Term StVM StAM
        MonadVM GenStMonad ConcreteEvidence VmSemantics.
(*Require Import Coq.ZArith.ZArith_base Coq.Strings.String Coq.Strings.Ascii. *)
(* Require Import ExtLib.Data.Monads.StateMonad ExtLib.Data.Monads.ReaderMonad
ExtLib.Structures.Monads ExtLib.Data.Monads.IdentityMonad. *)
Require Import List.

(* Import MonadNotation. *)
Import ListNotations.
(* Local Open Scope monad_scope. *)

(*
Definition Policy := nat.

Record AM_Env : Type := mkAM_Env
                          { myPolicy : Policy}.
*)

(* ident is the identity monad, acting as a place-holder for the base monad.
   TODO:  eventually we need this to be IO (or something that models IO) *)
Definition AM := St AM_St.     (* readerT AM_Env (stateT AM_St ident). *)

Definition empty_am_st := (mkAM_St [] 0 []).
(*Definition init_env := (mkAM_Env 0). *)

Check Maps_Class.map_set.

Definition mm : MapC nat BS := [].
Compute (map_set mm 1 2).

Check (map_set mm 1 2).

Definition am_newNonce (bs :BS) : AM EvidenceC :=
  (*let myPol := asks myPolicy in *)
  am_st <- get ;;
  let mm := am_nonceMap am_st in
  let i := am_nonceId am_st in
  let newMap := map_set mm i bs in
  let newId := i + 1 in
  put (mkAM_St newMap newId []) ;;         
      ret (nnc i bs mtc).

Definition runAM {A:Type} (k:(AM A)) (* (env:AM_Env) *) (st:AM_St) : (option A) * AM_St :=
  runSt st k.

Definition incNonce := runAM (am_newNonce 42) empty_am_st.
Check incNonce.
Compute (incNonce).

Check annotated.

Definition am_run_t (t:Term) (e:EvidenceC) : AM EvidenceC :=
  let annt := annotated t in
  let start_st := mk_st e [] 0 [] in
  ret (st_ev (run_vm annt start_st)).

Definition t1 := (att 1 (lseq (asp (ASPC 44 [])) (asp SIG))).
Definition t2 := (lseq (asp (ASPC 44 [])) (asp SIG)).


Compute (am_run_t t2 mtc empty_am_st).

Definition am_proto_1 :=
  n2 <- am_newNonce 42 ;;
    n <- am_newNonce 43 ;;
    am_run_t t2 n.

Compute (runAM am_proto_1 empty_am_st).

Check fold_left.
Check cons.

Fixpoint nonces (e:EvidenceC) (l:list nat) : list nat :=
  match e with
  | nnc i _ e' => nonces e' ([i] ++ l)
  | _ => l
  end.


    






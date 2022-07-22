(*
Implementation of the Copland Virtual Machine (CVM).

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Cvm_Monad.

Require Import List.
Import ListNotations.

(** Monadic CVM implementation *)
(* TODO: rename this to something besides "copland_compile".  Is really 
   more of an interpreter.  The Term to Core_Term translation function 
   is closer to a Copland Compiler than this.  *)
Fixpoint copland_compile (t:Core_Term): CVM unit :=
  match t with
  | aspc a =>
      e <- do_prim a ;;
      put_ev e
  | attc q t' =>
    e <- get_ev ;;
    e' <- doRemote t' q e ;;
    put_ev e'
  | lseqc t1 t2 =>
      copland_compile t1 ;;
      copland_compile t2
  | bseqc t1 t2 =>
    split_ev ;;
    e <- get_ev ;;
    copland_compile t1 ;;
    e1r <- get_ev ;;
    put_ev e ;;
    copland_compile t2 ;;
    e2r <- get_ev ;;
    join_seq e1r e2r
  | bparc loc t1 t2 =>
    split_ev ;;
    e <- get_ev ;;
    start_par_thread loc t2 e ;;
    copland_compile t1 ;;
    e1r <- get_ev ;;
    e2r <- wait_par_thread loc t2 e ;;
    join_seq e1r e2r
  end.

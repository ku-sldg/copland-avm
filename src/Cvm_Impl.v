(*
  Implementation of the Copland Virtual Machine (CVM).
    Acts as the top-level interpreter of (core) Copland terms by dispatching to monadic helpers.
    Note:  No meaningful return type (unit).  The real work happens within the monadic state that 
    invokes services and bundles evidence.

  Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Cvm_Monad.

Require Import List.
Import ListNotations.

(** Monadic CVM implementation (top-level) *)
Fixpoint build_cvm (t:Core_Term) : CVM unit :=
  match t with
  | aspc a =>
      e <- do_prim a ;;
      put_ev e
  | attc q t' =>
    e <- get_ev ;;
    e' <- doRemote t' q e ;;
    put_ev e'
  | lseqc t1 t2 =>
      build_cvm t1 ;;
      build_cvm t2
  | bseqc t1 t2 =>
    split_ev ;;
    e <- get_ev ;;
    build_cvm t1 ;;
    e1r <- get_ev ;;
    put_ev e ;;
    build_cvm t2 ;;
    e2r <- get_ev ;;
    join_seq e1r e2r
  | bparc loc t1 t2 =>
    split_ev ;;
    e <- get_ev ;;
    start_par_thread loc t2 e ;;
    build_cvm t1 ;;
    e1r <- get_ev ;;
    e2r <- wait_par_thread loc t2 e ;;
    join_seq e1r e2r
  end.

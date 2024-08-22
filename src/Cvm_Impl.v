(*
  Implementation of the Copland Virtual Machine (CVM).
    Acts as the top-level interpreter of (core) Copland terms by dispatching to monadic helpers.
    Note:  No meaningful return type (unit).  The real work happens within the monadic state that 
    invokes services and bundles EvidenceT.

  Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Cvm_Monad ErrorStMonad_Coq.
Import ErrNotation.

(** Monadic CVM implementation (top-level) *)
Fixpoint build_cvm (t: Term) : CVM unit :=
  match t with
  | asp a =>
      e <- do_prim a ;;
      put_ev e
  | att q t' =>
    e <- get_ev ;;
    e' <- doRemote q e t' ;;
    put_ev e'
  | lseq t1 t2 =>
    build_cvm t1 ;;
    build_cvm t2

  | bseq s t1 t2 =>
    split_ev ;;
    e <- get_ev ;;
    (* put ev for t1 to work on *)
    put_ev (splitEv_l s e) ;;
    build_cvm t1 ;;
    e1r <- get_ev ;;

    (* put ev for t2 to work on *)
    put_ev (splitEv_r s e) ;;
    build_cvm t2 ;;
    e2r <- get_ev ;;

    join_seq e1r e2r

  | bpar s t1 t2 =>
    split_ev ;;
    e <- get_ev ;;
    (* We will make the LOC = event_id for start of thread *)
    (* start a parallel thread working on the evidence split for t2 *)
    loc <- start_par_thread t2 (splitEv_r s e) ;;

    (* put ev for t1 to work on *)
    put_ev (splitEv_l s e) ;;
    build_cvm t1 ;;
    e1r <- get_ev ;;

    e2r <- wait_par_thread loc (splitEv_r s e) t2 ;;
    join_seq e1r e2r
  end.

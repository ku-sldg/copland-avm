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
Fixpoint build_cvm (e : Evidence) (t: Term) : CVM Evidence :=
  match t with
  | asp a => do_prim e a 
  | att q t' => doRemote q e t'
  | lseq t1 t2 =>
    e1 <- build_cvm e t1 ;;
    build_cvm e1 t2

  | bseq s t1 t2 =>
    split_ev ;;
    e1r <- build_cvm (splitEv_l s e) t1 ;;
    e2r <- build_cvm (splitEv_r s e) t2 ;;
    join_seq e1r e2r

  | bpar s t1 t2 =>
    split_ev ;;
    (* We will make the LOC = event_id for start of thread *)
    (* start a parallel thread working on the evidence split for t2 *)
    loc <- start_par_thread (splitEv_r s e) t2 ;;
    e1r <- build_cvm (splitEv_l s e) t1 ;;
    e2r <- wait_par_thread loc (splitEv_r s e) t2 ;;
    join_seq e1r e2r
  end.

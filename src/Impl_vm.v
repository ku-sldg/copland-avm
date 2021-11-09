(*
Implementation of the Copland Compiler and Virtual Machine.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Term GenStMonad MonadVM.

Require Import List.
Import ListNotations.

Require Import Maps.

(** Monadic VM implementation *)

Fixpoint copland_compile (t:AnnoTermPar): CVM unit :=
  match t with
  | aasp_par (n,_) a =>
      e <- do_prim n a ;;
      put_ev e
  | aatt_par (reqi,rpyi) q t' =>
    e <- get_ev ;;
    e' <- doRemote t' q e reqi rpyi ;;
    put_ev e'
  | alseq_par _ t1 t2 =>
      copland_compile t1 ;;
      copland_compile t2
  | abseq_par (x,y) sp t1 t2 =>
    pr <- split_ev x sp ;;
    let '(e1,e2) := pr in
    put_ev e1 ;;
    copland_compile t1 ;;
    e1r <- get_ev ;;
    put_ev e2 ;;
    copland_compile t2 ;;
    e2r <- get_ev ;;
    join_seq y e1r e2r
  | abpar_par (x,y) loc sp t1 t2 =>
    pr <- split_ev x sp ;;
    let '(e1,e2) := pr in
    start_par_thread loc t2 e2 ;;
    put_ev e1 ;;
    copland_compile t1 ;;
    e1r <- get_ev ;;
    e2r <- wait_par_thread loc t2 e2 ;;
    join_par y e1r e2r
  end.

Definition run_cvm (t:AnnoTermPar) st : cvm_st :=
  execSt (copland_compile t) st.

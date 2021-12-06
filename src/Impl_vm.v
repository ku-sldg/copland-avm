(*
Implementation of the Copland Compiler and Virtual Machine.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs MonadVM.

Require Import List.
Import ListNotations.

(** Monadic VM implementation *)

Fixpoint copland_compile (t:AnnoTermPar): CVM unit :=
  match t with
  | aasp_par a =>
      e <- do_prim a ;;
      put_ev e
  | aatt_par q t' =>
    e <- get_ev ;;
    e' <- doRemote t' q e ;;
    put_ev e'
  | alseq_par t1 t2 =>
      copland_compile t1 ;;
      copland_compile t2
  | abseq_par sp t1 t2 =>
    pr <- split_ev sp ;;
    let '(e1,e2) := pr in
    put_ev e1 ;;
    copland_compile t1 ;;
    e1r <- get_ev ;;
    put_ev e2 ;;
    copland_compile t2 ;;
    e2r <- get_ev ;;
    join_seq e1r e2r
  | abpar_par loc sp t1 t2 =>
    pr <- split_ev sp ;;
    let '(e1,e2) := pr in
    start_par_thread loc t2 e2 ;;
    put_ev e1 ;;
    copland_compile t1 ;;
    e1r <- get_ev ;;
    e2r <- wait_par_thread loc t2 e2 ;;
    join_par e1r e2r
  end.

(*
Definition run_cvm (t:AnnoTermPar) st : cvm_st :=
  execSt (copland_compile t) st.

Definition run_cvm' (t:Term) st : cvm_st :=
  run_cvm (annotated_par t) st.
*)

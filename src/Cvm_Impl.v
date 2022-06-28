(*
Implementation of the Copland Compiler and Virtual Machine.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Anno_Term_Defs Cvm_Monad.

Require Import List.
Import ListNotations.

(** Monadic VM implementation *)

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
    (*
    pr <- split_ev sp ;;
    let '(e1,e2) := pr in
    put_ev e1 ;; *)
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
    (*
    pr <- split_ev sp ;;
    let '(e1,e2) := pr in *)
    start_par_thread loc t2 e ;;
    (* put_ev e1 ;; *)
    copland_compile t1 ;;
    e1r <- get_ev ;;
    e2r <- wait_par_thread loc t2 e ;;
    join_seq e1r e2r
  end.

(*
Definition run_cvm (t:AnnoTermPar) st : cvm_st :=
  execSt (copland_compile t) st.

Definition run_cvm' (t:Term) st : cvm_st :=
  run_cvm (annotated_par t) st.
*)

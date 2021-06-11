(*
Implementation of the Copland Compiler and Virtual Machine.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Term GenStMonad MonadVM.

Require Import List.
Import ListNotations.

Require Import Maps.

(** Monadic VM implementation *)

Fixpoint copland_compile (t:AnnoTerm): CVM unit :=
  match t with
  | aasp (n,_) a =>
      e <- do_prim n a ;;
      put_ev e
  | aatt (i,j) q t' =>
      sendReq t' q i ;;
      e' <- receiveResp t' q j ;;
      put_ev e'
  | alseq _ t1 t2 =>
      copland_compile t1 ;;
      copland_compile t2
  | abseq (x,y) sp t1 t2 =>
      e <- get_ev ;;
      p <- get_pl ;;
      pr <- split_ev x sp e p ;;
      let '(e2,et2) := pr in
      (*put_ev e1 ;; *)
      copland_compile t1 ;;
      e1r <- get_ev ;;
      e1rt <- get_evT ;;
      put_ev e2 ;;
      put_evT et2 ;;
      copland_compile t2 ;;
      e2r <- get_ev ;;
      e2rt <- get_evT ;;
      join_seq (Nat.pred y) p e1r e1rt e2r e2rt
  | abpar (x,y) sp t1 t2 =>
    e <- get_ev ;;
    p <- get_pl ;;
    pr <- split_ev x sp e p ;;
    let '(e2,et2) := pr in
    (*put_ev e1 ;; *)
    copland_compile t1 ;;
    e1r <- get_ev ;;
    e1rt <- get_evT ;;
    put_ev e2 ;;
    put_evT et2 ;;
    copland_compile t2 ;;
    e2r <- get_ev ;;
    e2rt <- get_evT ;;
    join_par (Nat.pred y) p e1r e1rt e2r e2rt


    (*
      e <- get_ev ;;
      p <- get_pl ;;
      pr <- split_ev x sp e p ;;
      let '(e1,e2) := pr in
      put_ev e1 ;;
      copland_compile t1 ;;
      e1r <- get_ev ;;   
      put_ev e2 ;;
      copland_compile t2 ;;
      e2r <- get_ev ;;
      join_par (Nat.pred y) p e1r e2r *)
  end.

Definition run_cvm (t:AnnoTerm) st : cvm_st :=
  execSt (copland_compile t) st.

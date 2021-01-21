(*
Implementation of the Copland Compiler and Virtual Machine.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Term GenStMonad MonadVM.

(** Monadic VM implementation *)

Fixpoint copland_compile (t:AnnoTerm): CVM unit :=
  match t with
  | aasp (n,_) _ a =>
      e <- do_prim n a ;;
      put_ev e
  | aatt (i,j) _ (req_loc,rpy_loc) q t' =>
      sendReq t' q i req_loc ;;
      doRemote t' q req_loc rpy_loc ;;
      e' <- receiveResp j rpy_loc q ;;
      put_ev e'
  | alseq r _ t1 t2 =>
      copland_compile t1 ;;
      copland_compile t2
  | abseq (x,y) _ (sp1,sp2) t1 t2 =>
      e <- get_ev ;;
      p <- get_pl ;;
      pr <- split_ev_seq x sp1 sp2 e p ;;
      let '(e1,e2) := pr in
      put_ev e1 ;;
      copland_compile t1 ;;
      e1r <- get_ev ;;
      put_ev e2 ;;
      copland_compile t2 ;;
      e2r <- get_ev ;;
      join_seq (Nat.pred y) p e1r e2r
  | abpar (x,y) _ (loc_e1,loc_e1') (loc_e2,loc_e2') (sp1,sp2) t1 t2 =>
      e <- get_ev ;;
      p <- get_pl ;;
      split_ev_par x sp1 sp2 loc_e1 loc_e2 t1 t2 e p ;;
      (*let '(loc_e1,loc_e2) := pr in*)
      (*let loc_e1 := fst (range t1) in *)

      (*
      let loc_e1' := snd (range t1)  - 1 in  (* TODO: different loc? *)
      (*let loc_e2 := fst (range t2) in *)
      let loc_e2' := snd (range t2) - 1 in   (* TODO: different loc? *)
       *)
      
      (*
      let loc_e1 := fst (range t1) in
      let loc_e1' := snd (range t1) - 1 in  (* TODO: different loc? *)
      let loc_e2 := fst (range t2) in
      let loc_e2':= snd (range t2) - 1 in   (* TODO: different loc? *)
       
      
      put_store_at loc_e1 e1 ;;
      put_store_at loc_e2 e2 ;;
       *)
      
      runParThreads t1 t2 p loc_e1 loc_e1' loc_e2 loc_e2'  ;;
      join_par (Nat.pred y) p loc_e1' loc_e2'
      (*
      e1r <- get_store_at loc_e1' ;;
      e2r <- get_store_at loc_e2' ;;
      join_par (Nat.pred y) p e1r e2r *)
  end.

Definition run_cvm (t:AnnoTerm) st : cvm_st :=
  execSt (copland_compile t) st.




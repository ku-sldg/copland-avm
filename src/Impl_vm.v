(*
Implementation of the Copland Compiler and Virtual Machine.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term_Defs Term GenStMonad MonadVM.

Require Import List.
Import ListNotations.

Require Import Maps.

(** Monadic VM implementation *)


(*
Fixpoint copland_compile (t:AnnoTerm): CVM (list (CVM unit)) :=
  ret [].
*)

  
Fixpoint copland_compile (t:AnnoTerm): CVM unit :=
  match t with
  | aasp (n,_) a =>
      e <- do_prim n a ;;
      put_ev e
  | aatt (i,j) q t' =>
      sendReq t' q i ;;
      (*doRemote t' q ;; *)
      e' <- receiveResp t' q j ;;
      put_ev e'
  | alseq _ t1 t2 =>
      copland_compile t1 ;;
      copland_compile t2
  | abseq (x,y) sp t1 t2 =>
      e <- get_ev ;;
      p <- get_pl ;;
      pr <- split_ev_seq x sp e p ;;
      let '(e1,e2) := pr in
      put_ev e1 ;;
      copland_compile t1 ;;
      e1r <- get_ev ;;
      put_ev e2 ;;
      copland_compile t2 ;;
      e2r <- get_ev ;;
      join_seq (Nat.pred y) p e1r e2r
  | abpar (x,y) sp t1 t2 =>
      e <- get_ev ;;
      p <- get_pl ;;
      pr <- split_ev_seq x sp e p ;;
      let '(e1,e2) := pr in
      put_ev e1 ;;
      copland_compile t1 ;;
      e1r <- get_ev ;;

      (*
      e2 <- get_store_at loc_e2 ;;
       *)
      
      put_ev e2 ;;
      copland_compile t2 ;;
      e2r <- get_ev ;;
      (*
      put_store_at loc_e2' e2r_store ;; *)

      (*
      runParThread t2 p loc_e2 loc_e2' *)


      
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


      (*
      runParThreads t1 t2 p loc_e1 loc_e1' loc_e2 loc_e2'  ;; *)
      join_par (Nat.pred y) p (*loc_e1'*) e1r e2r
      (*
      e1r <- get_store_at loc_e1' ;;
      e2r <- get_store_at loc_e2' ;;
      join_par (Nat.pred y) p e1r e2r *)
  end.

Definition setup := MapC Plc (CVM unit).

(*
Require Import OptMonad. *)

Definition add_at (s:setup) (q:Plc) (comp:CVM unit) : setup :=
  let old_comp := map_get s q in
  match old_comp with
  | Some m =>
      let new_comp := m ;; comp in
      map_set s q new_comp
  | _ => map_set s q comp
  end.

(*
Definition bookend (comp: CVM unit) (req_loc rpy_loc:Loc): CVM unit :=
  e <- get_store_at req_loc ;;
  put_ev e ;;
  comp ;;
  e' <- get_ev ;;
  put_store_at rpy_loc e'.

Fixpoint copland_compliment (t:AnnoTerm) (s:setup): setup :=
  match t with
  | aatt (i,j) _ (req_loc,rpy_loc) q t' =>
    let comp := copland_compile t' in (* TODO: annotate terms with the place they execute? *)
    add_at s q (bookend comp req_loc rpy_loc)
  | alseq r _ t1 t2 =>
    let s1 := copland_compliment t1 s in
    let s2 := copland_compliment t2 s1 in
    s2
  | _ => []
  end.



(*
Definition add_before (s:setup) (q:Plc) (comp:CVM unit) : setup :=
  let old_comp := map_get s q in
  match old_comp with
  | Some m =>
      let new_comp := comp ;; m in
      map_set s q new_comp
  | _ => map_set s q comp
  end.
*)
    

Definition orchestrate (t:AnnoTerm): ((CVM unit) * setup) :=
  let main_thread := copland_compile t in
  let servers := copland_compliment t map_empty in
  (main_thread, servers).
  

Record PlatformState : Type := mk_plat
                         {plat_pl:Plc ;
                          plat_trace:list Ev ;
                          plat_store:ev_store}.

Definition start (st:PlatformState) (places:(CVM unit) * setup) : PlatformState.
Admitted.

Definition run_it (me:Plc) (t:AnnoTerm) : PlatformState :=
  start (mk_plat me [] []) (orchestrate t).

Definition getLocs (t:Term) (m:MapC (Plc*Plc) (list Loc)): list Loc.
Admitted.

Definition fromSome{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.

Definition run_it_term (me:Plc) (t:Term) (m:MapC (Plc*Plc) (list Loc)) : PlatformState :=
  let annt := snd (anno' t 0 (getLocs t m)) in
  run_it me annt.

*)


Definition run_cvm (t:AnnoTerm) st : cvm_st :=
  execSt (copland_compile t) st.




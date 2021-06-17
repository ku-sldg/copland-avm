Require Import Term ConcreteEvidence (*GenStMonad MonadVM MonadAM*) .

(*
Require Import Impl_vm StAM. *)

Require Import List.
Import ListNotations.

Require Import OptMonad.

(*
Definition am_add_trace (tr':list Ev) : AM_St -> AM_St :=
  fun '{| am_nonceMap := nm;
        am_nonceId := ni;
        st_aspmap := amap;
        st_sigmap := smap;
        st_hshmap := hmap;
        am_st_trace := tr;
        checked := cs |} =>
    mkAM_St nm ni amap smap hmap (tr ++ tr') cs.

Definition am_add_tracem (tr:list Ev) : AM unit :=
  modify (am_add_trace tr).

Definition am_run_cvm (annt:AnnoTerm) (e:EvidenceC) (et:Evidence) : AM EvidenceC :=
  let start_st := (mk_st e et [] 0) in
  let end_st := (run_cvm annt start_st) in
  am_add_tracem (st_trace end_st) ;;
  ret (st_ev end_st).

Definition am_run_cvm_comp{A:Type} (comp:CVM A) : AM A :=
  let '(cvm_res, vmst') := (runSt comp empty_vmst) in
  match cvm_res with
  | Some v =>
    am_add_tracem (st_trace vmst') ;;
    ret v
  | _ => failm
  end.

Require Import Maps.

Definition am_get_hsh_gv (p:Plc) (i:ASP_ID) : AM BS :=
  m <- gets st_hshmap ;;
  let maybeId := map_get m (p,i) in
  match maybeId with
  | Some i' => ret i'
  | None => failm
  end.


Definition am_get_hsh_golden_val (p:Plc) (et:Evidence): AM BS :=
  (*
    m <- gets st_aspmap ;;
    let maybeId := map_get m (p,i) in
    match maybeId with
    | Some i' => ret i'
    | None => failm
    end.
   *)
  ret 0.

Definition am_check_hsh_eq (gv:BS) (actual:BS) : AM BS :=
  ret 1.
*)

Definition checkASP (i:ASP_ID) (args:list Arg) (tpl:Plc) (tid:Plc) (bs:BS) : BS.
Admitted.

Definition checkSig (e:EvidenceC) (p:Plc) (sig:BS) : BS.
Admitted.

Definition checkHash (e:Evidence) (p:Plc) (hash:BS) : BS.
Admitted.

Definition peelBitsVval (e:EvidenceC) : option (BS*EvidenceC) :=
  match e with
  | PairBitsV (BitsV bs) e' => Some (bs,e')
  | _ => None
  end.

(*
Definition peelBitsVhsh (e:EvidenceC) : option (list BSV*EvidenceC) :=
  match e with
  | PairBitsV (BitsV (bshsh ls)) e' => Some (ls,e')
  | _ => None
  end.
*)
    
Definition peelPairBitsV (e:EvidenceC) : option (EvidenceC*EvidenceC) :=
  match e with
  | PairBitsV e1 e2 => ret (e1,e2)
  | _ => None
  end.
    

    
Fixpoint build_app_comp_ev (e:EvidenceC) (et:Evidence): option EvidenceC :=
  match et with
  | mt => ret (BitsV  0)
              
  | uu i' args' tpl' tid' et' =>
    '(bs,e') <- peelBitsVval e ;;
    res <- (build_app_comp_ev e' et') ;;
    ret (PairBitsV (BitsV (checkASP i' args' tpl' tid' bs)) res)
  | gg pi et' =>
    '(bs,e') <- peelBitsVval e ;;
    res <- (build_app_comp_ev e' et') ;;
    ret (PairBitsV (BitsV (checkSig e' pi bs)) res)
  | hh pi et' =>
    (*'(bs,e') <- peelPairBitsV e ;; *)
   
    match e with
    | BitsV bs =>
       ret (BitsV (checkHash et' pi bs))
    | _ => None
    end
  | nn nid => ret (BitsV nid) (* TODO: do checkNonce *)
  | ss et1 et2 =>
    '(e1,e2) <- peelPairBitsV e ;;
      e1_res <- build_app_comp_ev e1 et1 ;;
      e2_res <- build_app_comp_ev e2 et2 ;;
      ret (PairBitsV e1_res e2_res)
  | pp et1 et2 =>
    '(e1,e2) <- peelPairBitsV e ;;
      e1_res <- build_app_comp_ev e1 et1 ;;
      e2_res <- build_app_comp_ev e2 et2 ;;
      ret (PairBitsV e1_res e2_res)
  end.

(*
  | (ggc pi bs e', gg pi' et') =>
      ggc pi'
          (checkSig e' pi bs)
          (build_app_comp_ev e' et')
  | (hhc pi bs, hh pi' et') =>
      hhc pi' (checkHash et' pi' bs)
  | (nnc nid bs e', nn nid' et') =>  
    nnc nid' 42 (build_app_comp_ev e' et')
  | (ssc e1 e2, ss e1t e2t) =>
      ssc (build_app_comp_ev e1 e1t)
          (build_app_comp_ev e2 e2t)

  | (ppc e1 e2, pp e1t e2t) =>
      ppc (build_app_comp_ev e1 e1t)
          (build_app_comp_ev e2 e2t)
        
  | _ => mtc
  end.
*)

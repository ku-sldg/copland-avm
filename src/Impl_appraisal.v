Require Import Term ConcreteEvidence GenStMonad MonadVM MonadAM.

Require Import Impl_vm StAM.

Require Import List.
Import ListNotations.

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
    
Fixpoint build_app_comp_ev (e:EvidenceC) (et:Evidence): AM (EvidenceC) :=
  match (e,et) with
  | (mtc,mt) => ret mtc
              
  | (uuc i args tpl tid bs e', uu i' args' tpl' tid' et') =>
    app_id <- am_get_app_asp tpl' i' ;;
    innerRes <- build_app_comp_ev e' et' ;;
    res <- am_run_cvm_comp (checkUSM 0 app_id args' tpl' tid' bs) ;;
    ret (uuc i' args' tpl' tid' res innerRes)

  | (ggc pi bs e', gg pi' et') =>
    app_id <- am_get_sig_asp pi' ;;
    innerRes <- build_app_comp_ev e' et' ;;
    am_run_cvm_comp (checkSig 0 app_id e' bs) ;;
    ret (ggc pi' bs innerRes)
        
  | (hhc pi bs, hh pi' et') =>
    gv <- am_get_hsh_golden_val pi' et' ;;
    am_run_cvm_comp (checkHSH et' gv) ;;
    (*innerRes <- build_app_comp_ev e' ;; 
    am_run_cvm_comp (checkSig 0 app_id e' bs) ;; *)
    res <- am_check_hsh_eq gv bs ;;
    ret (hhc pi' res)
                            
  | (nnc nid bs e', nn nid' et') =>
    innerRes <- build_app_comp_ev e' et' ;;
    check_res <- am_checkNonce nid bs ;;
    ret (nnc nid check_res innerRes)

  | (ssc e1 e2, ss e1t e2t) =>
    c <- build_app_comp_ev e1 e1t ;;
    d <- build_app_comp_ev e2 e2t ;;
    ret (ssc c d)

  | (ppc e1 e2, pp e1t e2t) =>
    c <- build_app_comp_ev e1 e1t ;;
    d <- build_app_comp_ev e2 e2t ;;
    ret (ppc c d)
  | _ => failm
  end.

Require Import Term ConcreteEvidence GenStMonad MonadVM MonadAM.

Require Import Impl_vm StAM.

Require Import List.
Import ListNotations.

Definition am_add_trace (tr':list Ev) : AM_St -> AM_St :=
  fun '{| am_nonceMap := nm;
        am_nonceId := ni;
        st_aspmap := amap;
        st_sigmap := smap;
        am_st_trace := tr;
        checked := cs |} =>
    mkAM_St nm ni amap smap (tr ++ tr') cs.

Definition am_add_tracem (tr:list Ev) : AM unit :=
  modify (am_add_trace tr).

Definition am_run_cvm (annt:AnnoTerm) (e:EvidenceC) : AM EvidenceC :=
  let start_st := (mk_st e [] 0) in
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
    
Fixpoint build_app_comp_ev (e:EvidenceC): AM (EvidenceC) :=
  match e with
  | mtc => ret mtc
              
  | uuc i args tpl tid bs e' =>
    app_id <- am_get_app_asp tpl i ;;
    innerRes <- build_app_comp_ev e' ;;
    res <- am_run_cvm_comp (checkUSM 0 app_id args tpl tid bs) ;;
    ret (uuc i args tpl tid res innerRes)

  | ggc pi bs e' =>
    app_id <- am_get_sig_asp pi ;;
    innerRes <- build_app_comp_ev e' ;;
    am_run_cvm_comp (checkSig 0 app_id e' bs) ;;
    ret (ggc pi bs innerRes)
                            
  | nnc nid bs e' =>
    innerRes <- build_app_comp_ev e' ;;
    check_res <- am_checkNonce nid bs ;;
    ret (nnc nid check_res innerRes)

  | ssc e1 e2 =>
    c <- build_app_comp_ev e1 ;;
    d <- build_app_comp_ev e2 ;;
    ret (ssc c d)

  | ppc e1 e2 =>
    c <- build_app_comp_ev e1 ;;
    d <- build_app_comp_ev e2 ;;
    ret (ppc c d)       
  end.

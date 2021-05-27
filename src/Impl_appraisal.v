Require Import Term ConcreteEvidence GenStMonad MonadVM MonadAM.

Require Import Impl_vm StAM.

Require Import List.
Import ListNotations.

(*
Definition fromSome{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.
 *)

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
  (*let annt := annotated t in *)
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
        (*
    let c :=
        (*innerRes <- d ;; *)
        res <- checkUSM 0 app_id args tpl tid bs ;;
        ret (uuc i args tpl tid res innerRes) in
    ret c *)

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
        (*
    let res :=
        cr <- c ;;
        put_ev mtc ;;
        put_pl 0 ;;
        dr <- d ;;
        ret (ssc cr dr) in
    ret res *)

  | ppc e1 e2 =>
    c <- build_app_comp_ev e1 ;;
    d <- build_app_comp_ev e2 ;;
    ret (ppc c d)
    (*
    let res :=
        cr <- c ;;
        put_ev mtc ;;
        put_pl 0 ;;
        dr <- d ;;
        ret (ppc cr dr) in
    ret res *)
        
  end.
    




(*

Fixpoint build_app_comp_ev (e:EvidenceC): AM (CVM EvidenceC) :=
  match e with
  | mtc => ret (ret mtc)
  | uuc i args tpl tid bs e' =>
    app_id <- am_get_app_asp tpl i ;;
    d <- build_app_comp_ev e' ;;
    let c :=
        innerRes <- d ;;
        res <- checkUSM 0 app_id args tpl tid bs ;;
        ret (uuc i args tpl tid res innerRes) in
    ret c
  | ggc pi bs e' =>
    app_id <- am_get_sig_asp pi ;;
    d <- build_app_comp_ev e' ;;
    let c :=
        innerRes <- d ;;
        res <- checkSig 0 app_id e' bs ;;
        ret (ggc pi bs innerRes) in
    ret c
                              
  | nnc nid bs e' =>
    d <- build_app_comp_ev e' ;;
    check_res <- am_checkNonce nid bs ;;
    let c :=
        innerRes <- d ;;
        ret (nnc nid check_res innerRes) in
    ret c

  | ssc e1 e2 =>
    c <- build_app_comp_ev e1 ;;
    d <- build_app_comp_ev e2 ;;
    let res :=
        cr <- c ;;
        put_ev mtc ;;
        put_pl 0 ;;
        dr <- d ;;
        ret (ssc cr dr) in
    ret res

  | ppc e1 e2 =>
    c <- build_app_comp_ev e1 ;;
    d <- build_app_comp_ev e2 ;;
    let res :=
        cr <- c ;;
        put_ev mtc ;;
        put_pl 0 ;;
        dr <- d ;;
        ret (ppc cr dr) in
    ret res


    (*    
  | ssc e1 e2 =>
    c <- build_app_comp_ev e1 ;;
    d <- build_app_comp_ev e2 ;;
    let e1r := fromSome mtc (evalSt c empty_vmst) in
    let e2r := fromSome mtc (evalSt d empty_vmst) in
    ret (ret (ssc e1r e2r))
  | ppc e1 e2 =>
    c <- build_app_comp_ev e1 ;;
    d <- build_app_comp_ev e2 ;;
    let e1r := fromSome mtc (evalSt c empty_vmst) in
    let e2r := fromSome mtc (evalSt d empty_vmst) in
    ret (ret (ppc e1r e2r))
     *)
        


        (*
  | ppc e1 e2 =>
    c <- build_app_comp_ev e1 ;;
    d <- build_app_comp_ev e2 ;;
    let e1r := st_ev (execSt c empty_vmst) in
    let e2r := st_ev (execSt d empty_vmst) in
    ret (ret (ppc e1r e2r))
*)
    


    (*
    c <- build_app_comp_ev e1 ;;
    d <- build_app_comp_ev e2 ;;
    let res :=
        cr <- c ;;
        put_ev mtc ;;
        put_pl 0 ;;
        dr <- d ;;
        ret (ssc cr dr) in
    ret res *)
  end.
*)



(*

Fixpoint build_app_comp_ev (e:Evidence) (et:EvidenceC): AM (CVM EvidenceC) :=
  match (e,et) with
  | (mt, mtc) => ret (ret mtc)
  | (uu i args pi et', uuc ic bs ec') =>
    app_id <- am_get_app_asp pi i ;;
    d <- build_app_comp_ev et' ec' ;;
    let c :=
        innerRes <- d ;;
        res <- checkUSM 0 app_id args bs ;;
        ret (uuc 0 res innerRes) in
    ret c
  | (gg pi et', ggc bs ec') =>
    app_id <- am_get_sig_asp pi ;;
    d <- build_app_comp_ev et' ec' ;;
    let c :=
        innerRes <- d ;;
        res <- checkSig 0 app_id ec' bs ;;
        ret (ggc bs innerRes) in
    ret c
                              
  | _ => failm
  end.
*)

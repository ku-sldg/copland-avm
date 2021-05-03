Require Import Term ConcreteEvidence GenStMonad MonadVM MonadAM.

Require Import List.
Import ListNotations.

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
  end.



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

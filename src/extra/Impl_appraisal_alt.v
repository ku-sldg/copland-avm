Require Import ConcreteEvidenceT. (* Term GenStMonad MonadVM MonadAM. *)

Require Import Appraisal_Defs.  (* Require Import Impl_vm StAM. *)

Require Import List.
Import ListNotations.

Fixpoint build_app_comp_evC (e:EvidenceTC) : EvidenceTC :=
  match e with
  | mtc => mtc
              
  | uuc params p bs e' =>
    uuc params p (checkASPF params bs)
        (build_app_comp_evC e')
  | ggc p bs e' =>
    ggc p (checkSigF e' p bs)
        (build_app_comp_evC e')
  | hhc p bs et =>
    hhc p (checkHashF et p bs)(*(fromSome 0 (checkHash et p bs))*) et
  | nnc nid bs =>
    nnc nid (checkNonceF nid bs)
  | ssc e1 e2 =>
    ssc (build_app_comp_evC e1) (build_app_comp_evC e2)
  | ppc e1 e2 =>
    ppc (build_app_comp_evC e1) (build_app_comp_evC e2)
  end.

(*
(* *** Extra AM Monad defs *** *)

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

Definition am_run_cvm (annt:AnnoTerm) (e:EvidenceTC) (et:EvidenceT) : AM EvidenceTC :=
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


Definition am_get_hsh_golden_val (p:Plc) (et:EvidenceT): AM BS :=
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

Require Import Term ConcreteEvidence (*Appraisal_Evidence*) (*GenStMonad MonadVM MonadAM*) .

(*
Require Import Impl_vm StAM. *)

Require Import Appraisal_Defs Appraisal_Evidence.

Require Import List.
Import ListNotations.

(*
Require Import OptMonad. *)

Require Import GenOptMonad.

(*

Definition checkASP (i:ASP_ID) (args:list Arg) (tpl:Plc) (tid:Plc) (bs:BS) : BS.
Admitted.

Definition checkSig (ls:EvBits) (p:Plc) (sig:BS) : BS.
Admitted.

Definition checkHash (e:Evidence) (p:Plc) (hash:BS) : BS.
Admitted.

Definition peel_bs (ls:EvBits) : option (BS * EvBits) :=
  match ls with
  | bs :: ls' => Some (bs, ls')
  | _ => None
  end.
*)

Fixpoint build_app_comp_evC (et:Evidence) (ls:RawEv) : AM EvidenceC :=
  match et with
  | mt => ret mtc
              
  | uu params p et' =>
    '(bs, ls') <- peel_bs ls ;;
    x <- build_app_comp_evC et' ls' ;;
    res <- checkASP params bs ;;
    ret (uuc params p res x)
    
  | gg p et' =>
    '(bs, ls') <- peel_bs ls ;;
    x <- build_app_comp_evC et' ls' ;;
    res <- checkSigBits ls' p bs ;;
    ret (ggc p res x)
         
  | hh p et =>
    '(bs, _) <- peel_bs ls ;;
    res <- checkHash et p bs ;;
    ret (hhc p res et)
  | nn nid =>
    '(bs, _) <- peel_bs ls ;;
    res <- checkNonce nid bs ;;
    ret (nnc nid res)

  | ss et1 et2 =>
    x <- build_app_comp_evC et1 (firstn (et_size et1) ls) ;;
    y <- build_app_comp_evC et2 (skipn (et_size et1) ls) ;;
    ret (ssc x y)
  | pp et1 et2 =>
    x <- build_app_comp_evC et1 (firstn (et_size et1) ls) ;;
    y <- build_app_comp_evC et2 (skipn (et_size et1) ls) ;;
    ret (ppc x y)
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

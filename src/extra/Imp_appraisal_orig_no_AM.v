Require Import Term ConcreteEvidenceT (*Appraisal_EvidenceT*) (*GenStMonad MonadVM MonadAM*) .

(*
Require Import Impl_vm StAM. *)

Require Import Appraisal_Defs_New Appraisal_EvidenceT.

Require Import List.
Import ListNotations.

(*
Require Import OptMonad. *)

Require Import OptMonad_Coq.

(*

Definition checkASP (i:ASP_ID) (args:list Arg) (tpl:Plc) (tid:Plc) (bs:BS) : BS.
Admitted.

Definition checkSig (ls:EvBits) (p:Plc) (sig:BS) : BS.
Admitted.

Definition checkHash (e:EvidenceT) (p:Plc) (hash:BS) : BS.
Admitted.


Definition peel_bs (ls:EvBits) : option (BS * EvBits) :=
  match ls with
  | bs :: ls' => Some (bs, ls')
  | _ => None
  end.
 *)



(*
Definition checkASP_fwd (p:Plc) (f:FWD) (params:ASP_PARAMS)
           (et:EvidenceT) (bs:BS) (ls:RawEv) : Opt EvidenceTC :=
  match f with
  | COMP => res <- checkHH params bs ;;
           ret (hhc p params res et)
  | ENCR => res <- checkEE params bs ;;
           ret (eec p params res et)
  | _ => res <- checkASP params bs ;;
        
        ret (ggc p params bs mtc)
  end.
 *)


Fixpoint build_app_comp_evC (et:EvidenceT) (ls:RawEv) (nonceGolden:BS) : Opt AppResultC :=
  match et with
  | mt_evt=> ret mtc_app
  | nonce_evt nid =>
    '(bs, _) <- peel_bs ls ;;
    res <- checkNonce nonceGolden bs ;;  (* TODO: proper nonce check *)
    ret (nnc_app nid res)
  | asp_evt p fwd params et' =>
    match fwd with
    | COMP => ret mtc_app (* TODO hash check *)
      (*
      v <- checkHH params bs et' ;;
      ret (hhc p params v et') *)
    | ENCR =>
      '(bs, ls') <- peel_bs ls ;;
      decrypted_ls <- decrypt_bs_to_rawev bs params ;;
      rest <- build_app_comp_evC et' decrypted_ls nonceGolden ;;
      ret (eec_app p params passed_bs rest)
    (* TODO: consider encoding success/failure  of decryption for bs param 
       (instead of default_bs)  *)
    | EXTD =>
      '(bs, ls') <- peel_bs ls ;;
      v <- checkGG params p bs ls' ;;
      rest <- build_app_comp_evC et' ls' nonceGolden ;;
      ret (ggc_app p params v rest)
    | KILL => ret mtc_app (* Do we ever reach this case? *)
    | KEEP => build_app_comp_evC et' ls nonceGolden  (* ret mtc_app *) (* Do we ever reach this case? *)
    end
  | split_evt et1 et2 => 
      x <- build_app_comp_evC et1 (firstn (et_size et1) ls) nonceGolden ;;
      y <- build_app_comp_evC et2 (skipn (et_size et1) ls) nonceGolden  ;;
      ret (ssc_app x y)
  end.

Definition run_gen_appraise (t:Term) (p:Plc) (et:EvidenceT) (nonceGolden:BS) (ls:RawEv) :=
  fromSome mtc_app (build_app_comp_evC (eval t p et) ls nonceGolden).

Definition run_gen_appraise_w_nonce (t:Term) (p:Plc) (nonceIn:BS) (ls:RawEv) :=
  run_gen_appraise t p (nonce_evt 0) nonceIn ls.











(*
Fixpoint build_app_comp_evC (et:EvidenceT) (ls:RawEv) : Opt EvidenceTC :=
  match et with
  | mt_evt=> ret mtc
              
  | asp_evt params p et' =>
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
  | nonce_evt nid =>
    '(bs, _) <- peel_bs ls ;;
    res <- checkNonce nid bs ;;
    ret (nnc nid res)

  | split_evt et1 et2 =>
    x <- build_app_comp_evC et1 (firstn (et_size et1) ls) ;;
    y <- build_app_comp_evC et2 (skipn (et_size et1) ls) ;;
    ret (ssc x y)
  | pp et1 et2 =>
    x <- build_app_comp_evC et1 (firstn (et_size et1) ls) ;;
    y <- build_app_comp_evC et2 (skipn (et_size et1) ls) ;;
    ret (ppc x y)
  end.
*)

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

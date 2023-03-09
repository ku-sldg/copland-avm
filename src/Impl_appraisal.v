Require Import Term ConcreteEvidence StMonad_Coq.

Require Import Example_Phrases_Demo.

Require Import Appraisal_Defs Appraisal_IO_Stubs AM_Monad AM_St.

Require Import IO_Stubs privPolicy Cvm_Run.

Require Import List.
Import ListNotations.



Definition peel_bs_am (ls:RawEv) : AM (BS * RawEv) :=
  match ls with
  | bs :: ls' => ret (bs, ls')
  | _ => failm
  end.

Fixpoint gen_appraise_AM (et:Evidence) (ls:RawEv) : AM AppResultC :=
  match et with
  | mt => ret mtc_app
  | nn nid =>
    v <- (peel_bs_am ls) ;;
    match v with
      (bs, _) =>
      res <- checkNonce' nid bs ;;
      ret (nnc_app nid res)
    end

  | uu p fwd params et' =>
    match fwd with
    | COMP => ret mtc_app (* TODO hash check *)
    | ENCR =>
      v <- peel_bs_am ls ;;
      match v with
        (bs, ls') => 
        decrypted_ls <- decrypt_bs_to_rawev' bs params ;;
        rest <- gen_appraise_AM et' decrypted_ls ;;
        ret (eec_app p params passed_bs rest)
      (* TODO: consider encoding success/failure  of decryption for bs param 
         (instead of default_bs)  *)
      end

    | EXTD =>
      v <- peel_bs_am ls ;;
      match v with
        (bs, ls') => 
        v <- check_asp_EXTD' params p bs ls' ;;
        rest <- gen_appraise_AM et' ls' ;;
        ret (ggc_app p params v rest)
      end
    | KILL => ret mtc_app (* Do we ever reach this case? *)
    | KEEP => gen_appraise_AM et' ls (* Do we ever reach this case? *)
    end
  | ss et1 et2 => 
      x <- gen_appraise_AM et1 (firstn (et_size et1) ls) ;;
      y <- gen_appraise_AM et2 (skipn (et_size et1) ls) ;;
      ret (ssc_app x y)
    end.


Definition fromSome{A:Type} (default:A) (opt:option A): A :=
  match opt with
  | Some x => x
  | _ => default
  end.

Definition gen_appraise_am_comp (t:Term) (p:Plc) (et:Evidence) (ls:RawEv) : AM AppResultC :=
  gen_appraise_AM (eval t p et) ls.


Definition run_am_app_comp{A:Type} (am_comp:AM A) (default_A:A) : A :=
  let optRes := evalSt am_comp empty_amst in (* TODO:  use input nonce mapping here? *)
  fromSome default_A optRes.

Definition run_gen_appraise_am (t:Term) (p:Plc) (et:Evidence) (ls:RawEv) : AppResultC := 
  let am_appr_comp := gen_appraise_AM (eval t p et) ls in
  (run_am_app_comp am_appr_comp mtc_app).

Definition am_sendReq_nonce (t:Term) (pFrom:Plc) (pTo:Plc) : AM AppResultC :=
  let nonce_bits := gen_nonce_bits in
  nid <- am_newNonce nonce_bits ;;
  let resev := am_sendReq t pFrom pTo (evc [] mt) [nonce_bits] in
  let expected_et := eval t pTo (nn nid) in
  gen_appraise_AM expected_et resev.

Definition run_am_sendReq_nonce (t:Term) (pFrom:Plc) (pTo:Plc) : AppResultC :=
  let am_comp := am_sendReq_nonce t pFrom pTo in
  (run_am_app_comp am_comp mtc_app).  (* TODO:  use input nonce mapping here?? *)

Definition am_sendReq_nonce_auth (t:Term) (pFrom:Plc) (pTo:Plc) : AM AppResultC :=
  let nonce_bits := gen_nonce_bits in
  nid <- am_newNonce nonce_bits ;;
  let auth_phrase := (* kim_meas *) ssl_sig in
  let auth_rawev := run_cvm_rawEv auth_phrase pFrom [] in
  let auth_et := eval auth_phrase pFrom mt in
  let resev := am_sendReq t pFrom pTo (evc auth_rawev auth_et) [nonce_bits]  in
  let expected_et := eval t pTo (nn nid) in
  gen_appraise_AM expected_et resev.


Definition am_sendReq_auth (t:Term) (pFrom:Plc) (pTo:Plc) (initEv:RawEv) : AM RawEv :=
  let auth_phrase := (* kim_meas *) ssl_sig in
  let auth_rawev := run_cvm_rawEv auth_phrase pFrom [] in
  let et := eval auth_phrase pFrom mt in
  let resev := am_sendReq t pFrom pTo (evc auth_rawev et) initEv in
  ret resev.
    
Definition run_am_sendReq_nonce_auth (t:Term) (pFrom:Plc) (pTo:Plc) : AppResultC :=
  let am_comp := am_sendReq_nonce_auth t pFrom pTo in
  (run_am_app_comp am_comp mtc_app).

Definition am_check_auth_tok (t:Term) (fromPl:Plc) (authTok:ReqAuthTok) : AM AppResultC :=
  match authTok with
  | evc auth_ev auth_et => 
    appres <-
    (match (requester_bound t fromPl authTok) with
     | false => failm
     | true => gen_appraise_AM auth_et auth_ev
     end) ;;
    ret appres
  end.

Definition am_serve_auth_tok_req (t:Term) (fromPl:Plc) (myPl:Plc) (authTok:ReqAuthTok) (init_ev:RawEv): AM RawEv :=
  match authTok with
  | evc auth_ev auth_et => 
    v <- am_check_auth_tok t fromPl authTok ;;
    match (andb (requester_bound t fromPl authTok) (appraise_auth_tok v)) with
    | true =>
      match (privPolicy fromPl t) with
      | true => ret (run_cvm_rawEv t myPl init_ev)
      | false => failm
      end
        
    | false => failm
    end
  end.

Definition run_am_serve_auth_tok_req (t:Term) (fromPl:Plc) (myPl:Plc) (authTok:ReqAuthTok) (init_ev:RawEv) : RawEv :=
  run_am_app_comp (am_serve_auth_tok_req t fromPl myPl authTok init_ev) [].
  













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



(*
Definition checkASP_fwd (p:Plc) (f:FWD) (params:ASP_PARAMS)
           (et:Evidence) (bs:BS) (ls:RawEv) : Opt EvidenceC :=
  match f with
  | COMP => res <- checkHH params bs ;;
           ret (hhc p params res et)
  | ENCR => res <- checkEE params bs ;;
           ret (eec p params res et)
  | _ => res <- checkASP params bs ;;
        
        ret (ggc p params bs mtc)
  end.
 *)


(*

Fixpoint build_app_comp_evC (et:Evidence) (ls:RawEv) (nonceGolden:BS) : Opt AppResultC :=
  match et with
  | mt => ret mtc_app
  | nn nid =>
    '(bs, _) <- peel_bs ls ;;
    res <- checkNonce nonceGolden bs ;;  (* TODO: proper nonce check *)
    ret (nnc_app nid res)
  | uu p fwd params et' =>
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
  | ss et1 et2 => 
      x <- build_app_comp_evC et1 (firstn (et_size et1) ls) nonceGolden ;;
      y <- build_app_comp_evC et2 (skipn (et_size et1) ls) nonceGolden  ;;
      ret (ssc_app x y)
  end.

Definition run_gen_appraise (t:Term) (p:Plc) (et:Evidence) (nonceGolden:BS) (ls:RawEv) :=
  fromSome mtc_app (build_app_comp_evC (eval t p et) ls nonceGolden).

Definition run_gen_appraise_w_nonce (t:Term) (p:Plc) (nonceIn:BS) (ls:RawEv) :=
  run_gen_appraise t p (nn 0) nonceIn ls.

*)









(*
Fixpoint build_app_comp_evC (et:Evidence) (ls:RawEv) : Opt EvidenceC :=
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

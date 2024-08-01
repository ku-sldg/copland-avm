(* Appraisal primitive implementations:  evidence unbundling, nonce generation, appraisal ASP dispatch.  *)

Require Import String Term_Defs EqClass Maps.

Require Import Appraisal_IO_Stubs ErrorStMonad_Coq AM_Monad ErrorStringConstants Attestation_Session.


Axiom decrypt_prim_runtime : forall bs params pk e,
  decrypt_bs_to_rawev_prim bs params pk = errC e -> e = (Runtime errStr_decryption_prim).

Definition check_et_size (et:Evidence) (ls:RawEv) : ResultT unit DispatcherErrors := 
  match (eqb (et_size et) (List.length ls)) with 
  | true => resultC tt 
  | false => errC (Runtime errStr_et_size)
  end.

Definition decrypt_bs_to_rawev (bs:BS) (params:ASP_PARAMS) (ac:Session_Config) : ResultT RawEv DispatcherErrors :=
match params with
| asp_paramsC _ _ p _ => 
    match (map_get (pubkey_map ac) p) with 
    | Some pubkey => decrypt_bs_to_rawev_prim bs params pubkey 
    | None => errC Unavailable
    end
end.

Import ErrNotation.

Definition decrypt_bs_to_rawev' (bs:BS) (params:ASP_PARAMS) (et:Evidence) : AM RawEv :=
  ac <- get_AM_config ;;
  match (decrypt_bs_to_rawev bs params ac) with 
  | resultC r => 
    match (check_et_size et r) with
    | resultC tt => err_ret r
    | errC e => am_failm (am_dispatch_error e) 
    end
  | errC e => am_failm (am_dispatch_error e) 
  end.

Definition checkNonce' (nid:nat) (nonceCandidate:BS) : AM BS :=
  nonceGolden <- am_getNonce nid ;;
  err_ret (checkNonce nonceGolden nonceCandidate).

Definition check_asp_EXTD (params:ASP_PARAMS) (ls:RawEv) (ac : Session_Config) : ResultT RawEv DispatcherErrors :=
  ac.(aspCb) params ls.

Definition check_asp_EXTD' (params:ASP_PARAMS) (p:Plc) (sig:RawEv) (ls:RawEv) : AM RawEv :=
  let '(asp_paramsC att_id args targ targid) := params in
  ac <- get_AM_config ;;
  match (map_get (ASP_to_APPR_ASP_Map ac) att_id) with
  | Some appr_asp => 
    match (check_asp_EXTD (asp_paramsC appr_asp args targ targid) (app sig ls) ac) with
    | resultC r => err_ret r
    | errC e => am_failm (am_dispatch_error e) 
    end
  | None => am_failm (am_dispatch_error (Runtime "We made it to appraisal without a translation for our attestation ASP"%string)) 
  end.



Require Import Term_Defs_Core Term_Defs Manifest AM_St EqClass. (* OptMonad_Coq. *)

Require Import Appraisal_IO_Stubs ErrorStMonad_Coq AM_Monad AM_St Manifest_Admits ErrorStringConstants.

(*
Definition checkASP (params:ASP_PARAMS) (bs:BS) : Opt BS :=
  Some (checkASP' params bs).
*)

(*
Definition checkHH (params:ASP_PARAMS) (bs:BS) (e:Evidence) : Opt BS :=
  Some (checkHH' params bs e).
*)

(*
Definition checkEE (params:ASP_PARAMS) (bs:BS) : Opt BS := 
Some (checkEE' params bs).
*)

(*
Definition decrypt_bs_to_rawev_prim (bs:BS) (params:ASP_PARAMS) (pk:PublicKey) : ResultT RawEv DispatcherErrors.
Admitted.
*)

Axiom decrypt_prim_runtime : forall bs params pk e,
  decrypt_bs_to_rawev_prim bs params pk = errC e -> e = (Runtime errStr_decryption_prim).

Definition check_et_size (et:Evidence) (ls:RawEv) : ResultT unit DispatcherErrors := 
  match (eqb (et_size et) (length ls)) with 
  | true => resultC tt 
  | false => errC (Runtime errStr_et_size)
  end.

Definition decrypt_bs_to_rawev (bs:BS) (params:ASP_PARAMS) (ac:AM_Config) : ResultT RawEv DispatcherErrors :=
match params with
| asp_paramsC _ _ p _ => 
    match (ac.(pubKeyCb) p) with 
    | resultC pubkey => decrypt_bs_to_rawev_prim bs params pubkey 
    | errC e => errC e
    end
end.

Definition decrypt_bs_to_rawev' (bs:BS) (params:ASP_PARAMS) (et:Evidence) : AM RawEv :=
  (* ac <- get_amConfig ;; *)
  st <- (@get AM_St AM_Error) ;;
  let ac := (amConfig st) in
  match (decrypt_bs_to_rawev bs params ac) with 
  | resultC r => 
    match (check_et_size et r) with
    | resultC tt => ret r
    | errC e => am_failm (am_dispatch_error e) 
    end
  | errC e => am_failm (am_dispatch_error e) 
  end.

Definition check_asp_EXTD (params:ASP_PARAMS) (p:Plc) (sig:BS) (ls:RawEv) (ac : AM_Config) : ResultT BS DispatcherErrors :=
  ac.(app_aspCb) params p sig ls.

Definition check_asp_EXTD' (params:ASP_PARAMS) (p:Plc) (sig:BS) (ls:RawEv) : AM BS :=
  (* ac <- get_amConfig ;; *)
  st <- (@get AM_St AM_Error) ;;
  let ac := (amConfig st) in
  match (check_asp_EXTD params p sig ls ac) with
  | resultC r => ret r
  | errC e => am_failm (am_dispatch_error e)
  end.

Definition checkNonce' (nid:nat) (nonceCandidate:BS) : AM BS :=
  nonceGolden <- am_getNonce nid ;;
  ret (checkNonce nonceGolden nonceCandidate).

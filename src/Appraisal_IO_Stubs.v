Require Import Term_Defs_Core Term_Defs.

Require Import (*AM_Monad *) Manifest_Admits ErrorStMonad_Coq Cvm_St AM_St.

Require Import ErrorStringConstants.



(*
Definition checkASP' (params:ASP_PARAMS) (bs:BS) : BS.
Admitted.
*)

(*
Definition checkHH' (params:ASP_PARAMS) (bs:BS) (e:Evidence) : BS.
Admitted.
*)

(*
Definition checkEE' (params:ASP_PARAMS) (bs:BS) : BS.
Admitted.
 *)

Definition gen_nonce_bits : BS.
Admitted.

Definition decrypt_bs_to_rawev_prim (bs:BS) (params:ASP_PARAMS) (pk:PublicKey) : ResultT RawEv DispatcherErrors.
Admitted.


(*
Definition decrypt_bs_to_rawev (bs:BS) (params:ASP_PARAMS) : RawEv.
Admitted.

Definition check_asp_EXTD (params:ASP_PARAMS) (p:Plc) (sig:BS) (ls:RawEv) : BS.
Admitted.
*)

Definition checkNonce (nonceGolden:BS) (nonceCandidate:BS) : BS.
Admitted.

Definition print_string (s:StringT) : unit. 
Admitted.

Definition print_am_error (err:AM_Error) (b:bool): bool := 
    if(b)
    then 
    (
    match err with 
    | am_error s => 
        if(b)
        then 
        (let v:= print_string s in b)
        else 
        (negb b)
    | am_dispatch_error e => 
        if(b)
        then
        (let v:= print_string errStr_dispatch_error in b) 
        else 
        (negb b)
    | cvm_error e => 
        if(b) 
        then 
        (let v := print_string errStr_cvm_error in b) 
        else 
        (negb b)
    end)
    else (negb b).


(*
Inductive AM_Error : Type := 
| cvm_error : CVM_Error -> AM_Error
| am_error : StringT -> AM_Error
| am_dispatch_error : DispatcherErrors -> AM_Error.
*)

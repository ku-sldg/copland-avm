(* Admitted definitions of external IO operations required by Appraisal.    *)

Require Import ResultT Term_Defs_Core Term_Defs.

Require Import Manifest_Admits ErrorStMonad_Coq Cvm_St AM_St.

Require Import StringT ErrorStringConstants.


Definition gen_nonce_bits : BS.
Admitted.

Definition decrypt_bs_to_rawev_prim (bs:BS) (params:ASP_PARAMS) (pk:PublicKey) : ResultT RawEv DispatcherErrors.
Admitted.

Definition checkNonce (nonceGolden:BS) (nonceCandidate:BS) : BS.
Admitted.

Definition print_string (s:StringT) : unit. 
Admitted.

(* The boolean parameter here is a hack to force evaluation in 
    extracted code (strict evaluation may optimize the "side-effect-only" print away).
    TODO:  Look for a more principled way to do this.    *)
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

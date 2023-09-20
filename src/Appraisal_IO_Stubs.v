Require Import Term_Defs_Core Term_Defs.

Require Import AM_Monad Manifest_Admits ErrorStMonad_Coq Cvm_St.


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

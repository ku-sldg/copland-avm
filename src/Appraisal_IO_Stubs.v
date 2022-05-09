Require Import Term_Defs OptMonad_Coq.

Definition checkASP (params:ASP_PARAMS) (bs:BS) : Opt BS.
Admitted.

Definition checkSigBits (ls:RawEv) (p:Plc) (sig:BS) : Opt BS.
Admitted.

Definition checkNonce (nid:nat) (val:BS) : Opt BS.
Admitted.

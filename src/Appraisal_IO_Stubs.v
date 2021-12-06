Require Import Term_Defs GenOptMonad.

Definition checkASP (params:ASP_PARAMS) (bs:BS) : AM BS.
Admitted.

Definition checkSigBits (ls:RawEv) (p:Plc) (sig:BS) : AM BS.
Admitted.

Definition checkNonce (nid:nat) (val:BS) : AM BS.
Admitted.

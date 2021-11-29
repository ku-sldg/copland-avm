Require Import Term_Defs ConcreteEvidence GenStMonad IO_Type.

Definition encodeEvRaw(e:RawEv): BS.
Admitted.

Definition do_asp (params :ASP_PARAMS) (e:RawEv) (mpl:Plc) (x:Event_ID) : BS.
Admitted.

Definition do_asp' (params :ASP_PARAMS) (e:RawEv) (mpl:Plc) (x:Event_ID) : IO BS :=
  ret (do_asp params e mpl x).

Definition do_sig (bs:BS) (p:Plc) (sigTag:Event_ID) : BS.
Admitted.

Definition do_sig' (bs:BS) (p:Plc) (sigTag:Event_ID) : IO BS :=
  ret (do_sig bs p sigTag).

Definition do_hash (bs:BS) (p:Plc) : BS.
Admitted.

Definition do_hash' (bs:BS) (p:Plc) : IO BS :=
  ret (do_hash bs p).

Definition do_start_par_thread (loc:Loc) (t:Term) (e:RawEv) : IO unit :=
  ret tt.

Definition parallel_vm_thread (l:Loc) (t:Term) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition do_wait_par_thread (loc:Loc) (t:Term) (p:Plc) (e:EvC) : IO EvC :=
  ret (parallel_vm_thread loc t p e).


Definition doRemote_session (t:Term) (pTo:Plc) (e:EvC) : EvC.
Admitted.

Definition doRemote_session' (t:Term) (pTo:Plc) (e:EvC) : IO EvC :=
  ret (doRemote_session t pTo e).

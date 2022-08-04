(** Abstract definitions of IO Stub signatures.  The functions with names that 
    have a tick at the end (i.e. do_asp') should be instantiated to concrete 
    IO functions in the executable language upon extraction.

    The non-ticked functions (i.e. do_asp) only live in Coq, and largely 
    represent raw evidence values.  We leave these  abstract (Admitted) in Coq 
    because they are either too low-level to reason about, or require external 
    IO capabilities not modeled first-class in our spec.  These abstract 
    evidence values support specification of correctness properties for 
    Appraisal (see usage of do_asp in appEvent_EvidenceC of Appraisal_Defs.v).
 *)

Require Import Term_Defs ConcreteEvidence StMonad_Coq IO_Type.

Definition encodeEvRaw(e:RawEv): BS.
Admitted.

Definition do_asp (params :ASP_PARAMS) (e:RawEv) (mpl:Plc) (x:Event_ID) : BS.
Admitted.

Definition doRemote_session (t:Term) (pTo:Plc) (e:EvC) : EvC.
Admitted.







Definition do_asp' (params :ASP_PARAMS) (e:RawEv) (mpl:Plc) (x:Event_ID) : IO BS :=
  ret (do_asp params e mpl x).

Definition doRemote_session' (t:Term) (pTo:Plc) (e:EvC) : IO EvC :=
  ret (doRemote_session t pTo e).

Definition do_start_par_thread (loc:Loc) (t:Core_Term) (e:RawEv) : IO unit :=
  ret tt.

Definition parallel_vm_thread (l:Loc) (t:Core_Term) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition do_wait_par_thread (loc:Loc) (t:Core_Term) (p:Plc) (e:EvC) : IO EvC :=
  ret (parallel_vm_thread loc t p e).




(*
Definition do_sig (bs:BS) (p:Plc) (sigTag:Event_ID) : BS.
Admitted.

Definition do_sig' (bs:BS) (p:Plc) (sigTag:Event_ID) : IO BS :=
  ret (do_sig bs p sigTag).

Definition do_hash (bs:BS) (p:Plc) : BS.
Admitted.

Definition do_hash' (bs:BS) (p:Plc) : IO BS :=
  ret (do_hash bs p).
*)

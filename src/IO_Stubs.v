(** Abstract definitions of IO Stub signatures.  The functions with monadic 
    return types (i.e. do_asp') can be replaced by concrete monadic functions
    in the target language upon extraction.  Alternatively,
    if the target language does not have built-in monadic support, one can
    instantiate the non-monadic versions of the stubs instead (i.e. do_asp).

    The non-monadic stubs (i.e. do_asp) remain abstract (Admitted) in Coq 
    because they are either too low-level to reason about, or require external 
    IO capabilities not modeled first-class in our spec.  The abstract binary
    and evidence value results support specification of correctness properties 
    for Appraisal (see usage of do_asp in appEvent_EvidenceC of 
    Appraisal_Defs.v).        
 *)

Require Import Term_Defs ConcreteEvidence StMonad_Coq IO_Type Manifest_Admits.

(** * Stub to encode a sequence of BS values to a single BS value.
      Real implmenetation will depend on the instantition of BS *)
Definition encodeEvRaw(e:RawEv): BS.
Admitted.

(** * Stub for invoking external ASP procedures.  
      Extracted code should not need to use the Plc or Event_ID parameters 
      (those can be erased upon extraction). *)
Definition do_asp (params :ASP_PARAMS) (e:RawEv) (mpl:Plc) (x:Event_ID) : BS.
Admitted.

(** * Stub for completing a remote communication session with an external AM. *)
Definition doRemote_session (t:Term) (pTo:Plc) (e:EvC) : EvC.
Admitted.

(** * Stub to simulate evidence collected by a parallel CVM instance *)
Definition parallel_vm_thread (l:Loc) (t:Core_Term) (p:Plc) (e:EvC) : EvC.
Admitted.


(** * Stub for a top-level request from a remote client AM  *)
Definition am_sendReq (t:Term) (u : UUID) (authTok:ReqAuthTok) (e:RawEv) : RawEv.
Admitted.

Definition do_asp' (params :ASP_PARAMS) (e:RawEv) (mpl:Plc) (x:Event_ID) : IO BS :=
  ret (do_asp params e mpl x).

Definition doRemote_session' (t:Term) (pTo:Plc) (e:EvC) : IO EvC :=
  ret (doRemote_session t pTo e).

Definition do_start_par_thread (loc:Loc) (t:Core_Term) (e:RawEv) : IO unit :=
  ret tt.

Definition do_wait_par_thread (loc:Loc) (t:Core_Term) (p:Plc) (e:EvC) : IO EvC :=
  ret (parallel_vm_thread loc t p e).

Definition requester_bound (t:Term) (fromPl:Plc) (authTok:ReqAuthTok) : bool.
Admitted.

Definition appraise_auth_tok (res:AppResultC) : bool.
Admitted.

Definition print_auth_tok (tok:ReqAuthTok) : unit.
Admitted.

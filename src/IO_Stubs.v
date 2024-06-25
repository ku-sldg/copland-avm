(** Abstract definitions of IO Stub signatures.  Functions with monadic 
    return types (i.e. do_start_par_thread) should be replaced by concrete monadic 
    functions in the target language upon extraction.  Alternatively,
    if the target language does not have built-in monadic support, one can
    instantiate a non-monadic version of the stub instead.

    The non-monadic stubs (i.e. doRemote_uuid) remain abstract (Admitted) in Coq 
    because they are either too low-level to reason about, or require external 
    IO capabilities not modeled first-class in our spec.  The abstract binary
    and evidence value results support specification of correctness properties 
    for Appraisal.        
 *)

Require Import Term_Defs ConcreteEvidence ErrorStMonad_Coq 
  Manifest Manifest_Set Manifest_Admits Cvm_St StringT.


Require Import List.
Import ListNotations.

(** * Stub to encode a sequence of BS values to a single BS value.
      Real implmenetation will depend on the instantition of BS *)
Definition encodeEvRaw(e:RawEv): BS.
Admitted.

(** * Stub for invoking/dispatching externally-configured ASP procedures. *)
Definition invoke_asp_uuid (uuid:UUID) (ps:ASP_PARAMS) (ev:RawEv) : ResultT BS CallBackErrors.
Admitted.

(** * Stub for dispatching protocol terms to remote AMs. *)
Definition doRemote_uuid (t:Term) (uuid:UUID) (ev:RawEv) : ResultT RawEv CallBackErrors.
Admitted.

(** * Stub to simulate evidence collected by a parallel CVM instance *)
Definition parallel_vm_thread (l:Loc) (t:Core_Term) (p:Plc) (e:EvC) : EvC.
Admitted.

(** * Stub for a top-level request from a remote client AM  *)
Definition am_sendReq (t:Term) (p : Plc) (authTok:ReqAuthTok) (e:RawEv) : RawEv.
Admitted.

Definition am_sendReq'_app (uuid:UUID) (t:Term) (p:Plc) (e:Evidence) (ev:RawEv): AppResultC.
Admitted.

Definition am_sendReq_app (t:Term) (p:Plc) (e:Evidence) (ev:RawEv): AppResultC.
Admitted.

Definition requester_bound (t:Term) (fromPl:Plc) (authTok:ReqAuthTok) : bool.
Admitted.

Definition appraise_auth_tok (res:AppResultC) : bool.
Admitted.

Definition is_local_appraisal (res:AM_Library) : bool.
Admitted.

Definition print_auth_tok (tok:ReqAuthTok) : unit.
Admitted.

Definition pretty_print_manifest (m:Manifest) : StringT.
Admitted.

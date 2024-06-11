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
  Manifest Manifest_Admits Cvm_St StringT CvmJson_Interfaces.

Require Import List.
Import ListNotations.

(** * Stub to encode a sequence of BS values to a single BS value.
      Real implmenetation will depend on the instantition of BS *)
Definition encodeEvRaw(e:RawEv): BS.
Admitted.

Definition make_JSON_Request (uuid : UUID) (js : Json) : Json. Admitted.

(** * Stub for invoking external ASP procedures.  
      Extracted code should not need to use the Plc or Event_ID parameters 
      (those can be erased upon extraction). *)
Definition do_asp (params :ASP_PARAMS) (e:RawEv) (mpl:Plc) (x:Event_ID) (ac : AM_Config) : ResultT BS DispatcherErrors :=
  ac.(aspCb) params mpl (encodeEvRaw e) e.

(*
(** * Stub for completing a remote communication session with an external AM. *)
Definition doRemote_session (t:Term) (pTo:Plc) (e:EvC) : EvC.
Admitted.
*)

Definition doRemote_uuid (t:Term) (uuid:UUID) (ev:RawEv) : ResultT RawEv CallBackErrors.
Admitted.

Definition do_remote (t:Term) (pTo:Plc) (e:EvC) (ac: AM_Config) : ResultT RawEv DispatcherErrors := 
  let remote_uuid_res : ResultT UUID DispatcherErrors := ac.(plcCb) pTo in
    match remote_uuid_res with 
    | resultC uuid => 
        match doRemote_uuid t uuid (get_bits e) with
        | resultC v => resultC v
        | errC (messageLift msg) => errC (Runtime msg)
        end
    | errC e => errC e
    end.

(** * Stub to simulate evidence collected by a parallel CVM instance *)
Definition parallel_vm_thread (l:Loc) (t:Core_Term) (p:Plc) (e:EvC) : EvC.
Admitted.

Definition do_start_par_thread (loc:Loc) (t:Core_Term) (e:RawEv) : CVM unit :=
  ret tt.

Definition do_wait_par_thread (loc:Loc) (t:Core_Term) (p:Plc) (e:EvC) : CVM EvC :=
  ret (parallel_vm_thread loc t p e).

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

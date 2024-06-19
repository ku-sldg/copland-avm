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
  Manifest Manifest_Admits Cvm_St StringT JSON.

Require Import List.
Import ListNotations.

Definition make_JSON_Network_Request (uuid : UUID) (js : JSON) : JSON. Admitted.

Definition make_JSON_FS_Location_Request (fsl : FS_Location) (js : JSON) : JSON. Admitted.

(** * Stub to simulate evidence collected by a parallel CVM instance *)
Definition parallel_vm_thread (l:Loc) (t:Core_Term) (p:Plc) (e:EvC) : EvC.  Admitted.

Definition do_start_par_thread (loc:Loc) (t:Core_Term) (e:RawEv) : CVM unit :=
  ret tt.

Definition do_wait_par_thread (loc:Loc) (t:Core_Term) (p:Plc) (e:EvC) : CVM EvC :=
  ret (parallel_vm_thread loc t p e).

Definition requester_bound (t:Term) (fromPl:Plc) (authTok:ReqAuthTok) : bool.  Admitted.

Definition appraise_auth_tok (res:AppResultC) : bool.  Admitted.

Definition is_local_appraisal (res:AM_Library) : bool.  Admitted.

Definition print_auth_tok (tok:ReqAuthTok) : unit.  Admitted.

Definition pretty_print_manifest (m:Manifest) : StringT.  Admitted.

(* Top-level definitions for running CVM monad computations.  *)

Require Import Term_Defs Anno_Term_Defs Cvm_Impl Cvm_St ErrorStMonad_Coq String
  ErrorStringConstants Attestation_Session.

Require Import List.
Import ListNotations.

Definition run_core_cvm (t:Core_Term) (st : cvm_st) : ResultT cvm_st CVM_Error :=
  let '(res, st') := ((build_cvm t) st) in
  match res with
  | resultC _ => resultC st'
  | errC e => errC e
  end.

Definition run_cvm (t:Term) st : ResultT cvm_st CVM_Error :=
  run_core_cvm (copland_compile t) st.

Definition run_cvm_w_config (t:Term) (e:RawEv) (ac : Session_Config) 
    : ResultT cvm_st CVM_Error :=
  run_cvm t (mk_st (evc e mt) [] 0 ac).

Definition run_cvm_rawEv (t:Term) (e:RawEv) (ac : Session_Config) 
    : ResultT RawEv string :=
  match (run_cvm_w_config t e ac) with
  | resultC st => resultC (get_bits (st_ev st))
  | errC e => 
      match e with
      | at_error_dynamic _ _ _ => errC errStr_run_cvm_at_error_dynamic
      | at_error_static _ _ _ => errC errStr_run_cvm_at_error_static
      | dispatch_error Unavailable => errC errStr_dispatch_error
      | dispatch_error (Runtime s) => errC s
      end
  end.

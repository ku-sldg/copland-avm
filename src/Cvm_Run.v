(* Top-level definitions for running CVM monad computations.  *)

Require Import Term_Defs Cvm_Impl Cvm_St ErrorStMonad_Coq String
  ErrorStringConstants Attestation_Session.

Require Import List.
Import ListNotations.

Definition run_cvm (e : Evidence) (t:Term) st sc : ResultT cvm_st CVM_Error :=
  let '(res, st', sc') := ((build_cvm e t) st sc) in
  match res with
  | resultC _ => resultC st'
  | errC e => errC e
  end.

Definition run_cvm (ac : Session_Config) (e: Evidence) (t : Term) 
    : ResultT Evidence string :=
  let init_st := (mk_st e [] 0) in
  match (run_cvm e t init_st ac) with
  | resultC st => resultC (st_ev st)
  | errC e => 
      match e with
      | at_error_dynamic _ _ _ => errC errStr_run_cvm_at_error_dynamic
      | at_error_static _ _ _ => errC errStr_run_cvm_at_error_static
      | dispatch_error Unavailable => errC errStr_dispatch_error
      | dispatch_error (Runtime s) => errC s
      end
  end.

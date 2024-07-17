(*  Configuring and invoking custom CakeML code extraction.  *)

Require Extraction.

Require Import Term_Defs Term_Defs_Core Cvm_Run IO_Stubs AM_Monad Cvm_Monad.
(* Require Import CopParser. *)

Require Import Manifest_Generator Manifest_Compiler.

Require Import AM_Helpers Server_AM Client_AM.

Require Import Manifest_Generator_Union Manifest_JSON Flexible_Mechanisms.

Require Import List.
Import ListNotations.

Require Import ExtrCakeMLNativeString.

Extraction Language CakeML. (* OCaml. *) 

Extraction Implicit parallel_vm_thread [2 3 4].
Extraction Implicit do_wait_par_thread [2 3 4].

Extract Constant sig_params => "( undefined () )".
Extract Constant hsh_params => "( undefined () )".
(* Extract Constant + => "add". *)
(* Extract Constant Nat.add => "(+)". *)

(*
Extract Constant get_ev => "bind get (fn st => ret (st_ev st)) : cvm_st -> coq_EvC".
(* "st <- (@get cvm_st CVM_Error) ;; ret (st_ev st)". *)
*)

Separate Extraction 
    flexible_mechanisms flexible_mechanisms_evidence
    run_cvm manifest_compiler 
    Jsonifiable_AM_Library Jsonifiable_Manifest
		handle_AM_request end_to_end_mangen_final
    run_demo_client_AM
    Jsonifiable_Evidence_Plc_list Jsonifiable_Term_Plc_list.

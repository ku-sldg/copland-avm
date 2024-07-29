(*  Configuring and invoking custom CakeML code extraction.  *)

Require Extraction.

Require Import Term_Defs Term_Defs_Core Cvm_Run IO_Stubs AM_Monad Cvm_Monad.
(* Require Import CopParser. *)

Require Import Manifest_Generator Session_Config_Compiler.

Require Import AM_Helpers Server_AM Client_AM.

Require Import Manifest_Generator_Union Manifest_JSON Flexible_Mechanisms.

Require Import List.
Import ListNotations.

Require Import Concrete_Extractables.

Require Import ExtrCakeMLNativeString.

Extraction Language CakeML. (* OCaml. *) 

Extraction Implicit parallel_vm_thread [2 3 4].
Extraction Implicit do_wait_par_thread [2 3 4].

Extract Constant sig_params => "( undefined () )".
Extract Constant hsh_params => "( undefined () )".
(* Extract Constant + => "add". *)
(* Extract Constant Nat.add => "(+)". *)

Separate Extraction 
    flexible_mechanisms flexible_mechanisms_evidence
    run_cvm session_config_compiler 
		handle_AM_request end_to_end_mangen_final
    run_demo_client_AM concrete_Jsonifiable_Manifest
    concrete_Jsonifiable_ASP_Compat_MapT
    concrete_Jsonifiable_Attestation_Session
    Jsonifiable_Evidence_Plc_list Jsonifiable_Term_Plc_list.

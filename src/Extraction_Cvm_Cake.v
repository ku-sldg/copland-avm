(*  Configuring and invoking custom CakeML code extraction.  *)

Require Extraction.

Require Import Term_Defs Term_Defs_Core IO_Stubs AM_Monad Cvm_Monad Cvm_Impl.
(* Require Import CopParser. *)

Require Import Manifest_Generator Session_Config_Compiler.

Require Import AM_Helpers Server_AM.

Require Import Manifest_Generator_Union Manifest_JSON Flexible_Mechanisms.

Require Import CACL_Demo.

Require Import List.
Import ListNotations.

Require Import Concrete_Extractables.

Require Import ExtrCakeMLNativeString.

Extraction Language CakeML. (* OCaml. *) 

Extraction Implicit parallel_vm_thread [2 3 4].
Extraction Implicit do_wait_par_thread [2 3 4].

Extract Constant sig_params => "( undefined () )".
Extract Constant hsh_params => "( undefined () )".
Extract Inlined Constant Nat.eqb => "(op=)".
(* Extract Constant + => "add". *)
(* Extract Constant Nat.add => "(+)". *)

Separate Extraction 
    full_flexible_mechanisms
    build_cvm session_config_compiler 
		handle_AM_request end_to_end_mangen
    concrete_Jsonifiable_Manifest
    concrete_Jsonifiable_ASP_Compat_MapT
    concrete_Jsonifiable_Attestation_Session
    concrete_Jsonifiable_Term
    concrete_Jsonifiable_EvidenceT
    concrete_Jsonifiable_GlobalContext
    Jsonifiable_Term_Plc_list
    Jsonifiable_Evidence_Plc_list
    test_cacl_compute_json.

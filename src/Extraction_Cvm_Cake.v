(*  Configuring and invoking custom CakeML code extraction.  *)

Require Extraction.

Require Import Term_Defs Term_Defs_Core Cvm_Run IO_Stubs AM_Monad Cvm_Monad.
(* Require Import CopParser. *)

Require Import Example_Phrases Example_Phrases_Demo.

Require Import Example_Phrases_Pre Example_Phrases_Pre_Admits.

Require Import Manifest_Generator Manifest_Compiler.

Require Import AM_Helpers Server_AM Client_AM.

Require Import Manifest_Generator_Union Manifest_JSON.


Require Import List.
Import ListNotations.

Require Import ExtrCakeMLNativeString.

Extraction Language CakeML. (* OCaml. *) 

(* TODO: At some point this might be a good approach to take
Extract Constant string_to_ID_Type => "fun x => x".
Extract Constant string_to_ID_Type => "fun x => x". *)

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

Definition term_list : list Term := 
	[cert_style; cert_cache_p1; cert_cache_p0; 
	 par_mut_p0; par_mut_p1; layered_bg_strong; 
	 example_phrase_p2_appraise].

Separate Extraction 
		term_list ssl_sig_parameterized kim_meas cm_meas
		run_cvm manifest_compiler  empty_am_result 
    Jsonifiable_AM_Library Jsonifiable_Manifest
		handle_AM_request end_to_end_mangen_final
    Jsonifiable_Evidence_Plc_list Jsonifiable_Term_Plc_list.

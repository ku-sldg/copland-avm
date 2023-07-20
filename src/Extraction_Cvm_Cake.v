Require Extraction.

Require Import Term_Defs Term_Defs_Core Cvm_Run IO_Stubs AM_Monad.
Require Import CopParser.
Require Import CvmJson.

Require Import Example_Phrases Example_Phrases_Demo.

Require Import privPolicy (*Manifest*) Manifest_Generator Manifest_Compiler.

Require Import Client_AM Server_AM.

Extraction Language CakeML. (* OCaml. *) 

(*
Unset Extraction Optimize.
*)

Extract Inductive nat => "nat" ["O" "S"].
Extract Inductive bool => "bool" ["True" "False"].
Extract Inductive option => "option" ["Some" "None"].

Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
(*Extract Inductive prod => "( * )" [ "" ]. *)

Extraction Implicit do_asp [3 4].
Extraction Implicit do_asp' [3 4].
Extraction Implicit parallel_vm_thread [2 3 4].
Extraction Implicit do_wait_par_thread [2 3 4].


Extract Constant sig_params => "( undefined () )".
Extract Constant hsh_params => "( undefined () )".
(* Extract Constant + => "add". *)
(* Extract Constant Nat.add => "(+)". *)

Separate Extraction run_cvm manifest_compiler am_sendReq_dispatch 
		    run_am_app_comp am_serve_auth_tok_req am_client_auth_tok_req 
		    cert_style cert_style_test cert_style_trimmed ssl_sig_parameterized kim_meas
		    cert_cache_p1 cert_cache_p0 cert_cache_p0_trimmed
		    par_mut_p0 par_mut_p1 layered_bg_strong
		    (* demo_man_gen_run *) man_gen_run_attify empty_am_result
			run_cvm_json_full.

(* man_gen_res environment_to_manifest_list *)

(* 
Separate Extraction demo_phrase demo_phrase2 demo_phrase3 client_data_phrase ssl_sig CoplandM.Manifest.Manifest CoplandM.Manifest.manifest_compiler Evidence AppResultC. *)

(*
Separate Extraction CopParser.parsePhrase.
*)

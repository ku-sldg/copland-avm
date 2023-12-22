Require Extraction.

Require Import Term_Defs Term_Defs_Core. (* Cvm_Run IO_Stubs (* AM_Monad *) Cvm_Monad. *)
(* Require Import CopParser. *)

(* Require Import Example_Phrases Example_Phrases_Demo. 

Require Import Example_Phrases_Pre Example_Phrases_Pre_Admits.
*)

Require Import Manifest_Generator. (* Manifest_Compiler. *)

(* Require Import Server_AM Client_AM_Local AM_Helpers.

Require Import Manifest_Generator_Union.
*)


Require Import List.
Import ListNotations.

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

(*
Extraction Implicit do_asp [3 4].
Extraction Implicit do_asp' [3 4]. 
*)
(*
Extraction Implicit parallel_vm_thread [2 3 4].
Extraction Implicit do_wait_par_thread [2 3 4].
*)

(*
Extract Constant sig_params => "( undefined () )".
Extract Constant hsh_params => "( undefined () )".
*)


(* Extract Constant + => "add". *)
(* Extract Constant Nat.add => "(+)". *)

(*
Extract Constant get_ev => "bind get (fn st => ret (st_ev st)) : cvm_st -> coq_EvC".
(* "st <- (@get cvm_st CVM_Error) ;; ret (st_ev st)". *)

*)

(*
Definition term_list : list Term := 
	[cert_style; cert_cache_p1; cert_cache_p0; 
	 par_mut_p0; par_mut_p1; layered_bg_strong; 
	 example_phrase; example_phrase_p2_appraise; 
	 inline_auth_phrase].
*)

Separate Extraction manifest_generator.
		(* term_list ssl_sig_parameterized kim_meas cm_meas
		run_cvm manifest_compiler  
        empty_am_result run_am_app_comp run_am_app_comp_init 
		handle_AM_request am_client_gen_local 
		lib_omits_manifest manifest_none_omitted 
		end_to_end_mangen_final. *)

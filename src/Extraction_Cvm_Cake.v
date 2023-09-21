Require Extraction.

Require Import Term_Defs Term_Defs_Core Cvm_Run IO_Stubs AM_Monad Cvm_Monad.
(* Require Import CopParser. *)

Require Import Example_Phrases Example_Phrases_Demo.

Require Import privPolicy Manifest_Generator Manifest_Compiler.

Require Import Client_AM Server_AM Client_AM_Local.


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

(*
  bind get (fn st =>
    let val ac = let val Coq_mkAM_St _ _ amConfig = st in amConfig end in
    (case decrypt_bs_to_rawev bs params ac of
       Coq_errC e => failm (Coq_dispatch_error e)
     | Coq_resultC r =>
       (case check_et_size et r of
          Coq_errC e => failm (Coq_dispatch_error e)
        | Coq_resultC _ => ret r)) end)
		*)

Definition term_list : list Term := 
	[cert_style; cert_style_test; cert_style_trimmed; cert_cache_p1; cert_cache_p0; cert_cache_p0_trimmed].

Separate Extraction run_cvm manifest_compiler  
		    run_am_app_comp 
			handle_AM_request am_client_auth am_client_gen 
			term_list ssl_sig_parameterized kim_meas
		    par_mut_p0 par_mut_p1 layered_bg_strong
		    man_gen_run_attify empty_am_result
        am_client_gen_local
        run_am_app_comp.

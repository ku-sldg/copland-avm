Require Extraction.

Require Import Term_Defs Cvm_Run IO_Stubs Example_Phrases_Demo.
Require Import CopParser.

Require Import privPolicy Manifest.

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

Separate Extraction demo_phrase demo_phrase2 demo_phrase3 client_data_phrase ssl_sig CoplandM.Manifest.Manifest CoplandM.Manifest.manifest_compiler.

(*
Separate Extraction CopParser.parsePhrase.
*)

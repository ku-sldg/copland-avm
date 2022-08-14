Require Extraction.

Require Import (*Impl_VM*) Term_Defs Cvm_Run IO_Stubs Example_Phrases_Demo. (*Cvm_Monad IO_Type Term_Defs Anno_Term_Defs.*) (*Example_Phrases. *)

(*
Require Import Impl_appraisal. *)

Extraction Language CakeML.

(*
Extraction Language Haskell.

Require Import ExtrHaskellBasic.


Require Import ExtrHaskellNatNum. 
Extract Inductive nat =>
"Prelude.Int"
  ["0" "Prelude.succ"]
  "(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".
Extract Constant Term_Defs.ASP_ID => "Prelude.Int".
Extract Constant Term_Defs.TARG_ID => "Prelude.Int".
Extract Constant Term_Defs.Arg => "Prelude.String".
*)

(*Extract Constant IO_Type.IO "a" => "IO a". *)

Extract Inductive nat => "nat" ["O" "S"].
Extract Inductive bool => "bool" ["True" "False"].
Extract Inductive option => "option" ["Some" "None"].

Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
(*Extract Inductive prod => "( * )" [ "" ]. *)

Extraction Implicit do_asp [3 4].
Extraction Implicit do_asp' [3 4].
(*
Extraction Implicit do_sig [2 3].
Extraction Implicit do_sig' [2 3].
Extraction Implicit do_hash [2].
Extraction Implicit do_hash' [2].
*)
Extraction Implicit parallel_vm_thread [2 3 4].
Extraction Implicit do_wait_par_thread [2 3 4].


Extract Constant sig_params => "( undefined () )".
Extract Constant hsh_params => "( undefined () )".

(*
Definition my_extracted (t:Term) (st:cvm_st) (et:Evidence) (ls:RawEv) :=
  let res := run_cvm' t st in
  let res' := build_app_comp_evC et ls in
  let res'' := eval t 0 mt in
  (res, res', res'').
*)


(*
Separate Extraction run_cvm' build_app_comp_evC eval cert_style_simple_sig cert_style cert_cache_p1 cert_cache_p0 bg_check par_mut_p0 par_mut_p1 layered_bg_weak layered_bg_strong test_par_nested anno_par_list top_level_thread_count.
*)

Extract Constant Nat.add => "(+)".

Separate Extraction run_cvm_rawEv run_cvm_fresh demo_phrase.



(* my_extracted. *)

(*
Separate Extraction run_cvm'.
Separate Extraction build_app_comp_evC.
*)


(*
Extraction anno_par.
Extraction annotated_par.
*)


























(*
Extraction Library Term_Defs.
 *)

(*
Recursive Extraction build_app_comp_evC.
*)
















(*
Extract Constant Term_Defs.BS => "B.ByteString".
*)

(*Extract Constant Impl_VM.run_cvm => "Prelude.undefined". *)
(*
Extract Constant GenStMonad.ret => "return".
Extract Constant GenStMonad.bind => "(>>=)".
 *)


(*
Extraction Implicit event_id_span [1].
Extraction Implicit add_trace [1 2].
Extraction Implicit add_tracem [1].
Extraction Implicit inc_remote_event_ids [1].
*)


(*Extraction Implicit wait_par_thread [2 3]. *)

(*
Unset Extraction SafeImplicits.
*)


(*
Extraction Implicit add_tracem [1].
Extraction Implicit tag_ASP [1 2].
Unset Extraction SafeImplicits.
*)

(*

Extract Inductive list => "[]" ["[]" "(:)"].
Extract Inductive prod => "(,)" ["(,)"].
Print option.
Extract Inductive option => "Maybe" ["Just" "Nothing"].

(*
Extract Inlined Constant nat => "Int".
*)

Extract Inductive nat => "Int" ["0" "succ"] "".
*)


(*
Recursive Extraction Term_Defs.AnnoTermPar.
Recursive Extraction Term_Defs.EvC.

(*Recursive Extraction copland_compile. *)
Recursive Extraction run_cvm.
 *)

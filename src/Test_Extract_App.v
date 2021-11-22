Require Extraction.

Require Import Impl_VM Impl_appraisal_alt IO_Stubs MonadVM.

(*
Extraction Language CakeML.
 *)

Extraction Language Haskell.

Require Import ExtrHaskellBasic.

Require Import ExtrHaskellNatNum.
Extract Inductive nat => "Prelude.Int" ["0" "succ"]
"(\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

(*
Extraction Implicit event_id_span [1].
Extraction Implicit add_trace [1 2].
Extraction Implicit add_tracem [1].
Extraction Implicit inc_remote_event_ids [1].
*)

Extraction Implicit do_asp [2 3].
Extraction Implicit do_sig [2 3].
Extraction Implicit do_hash [2].
Extraction Implicit parallel_vm_thread [2 3 4].
Extraction Implicit do_wait_par_thread [2 3 4].
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





(*Recursive Extraction copland_compile. *)
Recursive Extraction run_cvm.

(*
Recursive Extraction build_app_comp_evC.
*)


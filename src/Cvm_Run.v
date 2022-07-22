(* Top-level definitions for running CVM monad computations.  *)

Require Import Term_Defs Anno_Term_Defs Cvm_Impl Cvm_St StMonad_Coq.

Definition run_cvm (t:Core_Term) st : cvm_st :=
  execSt (copland_compile t) st.

Definition run_cvm' (t:Term) st : cvm_st :=
  run_cvm (term_to_core_term t) st.

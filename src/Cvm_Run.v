(* Top-level definitions for running CVM monad computations.  *)

Require Import Term_Defs Anno_Term_Defs Cvm_Impl Cvm_St StMonad_Coq.

Definition run_cvm (t:Core_Term) st : cvm_st :=
  execSt (build_cvm t) st.

Definition run_cvm' (t:Term) st : cvm_st :=
  run_cvm (copland_compile t) st.

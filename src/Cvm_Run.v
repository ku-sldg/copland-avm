Require Import Term_Defs Anno_Term_Defs Cvm_Impl Cvm_St StMonad_Coq.

Definition run_cvm (t:AnnoTermPar) st : cvm_st :=
  execSt (copland_compile t) st.

Definition run_cvm' (t:Term) st : cvm_st :=
  run_cvm (annotated_par t) st.

Require Import Term_Defs Impl_VM StVM GenStMonad.

Definition run_cvm (t:AnnoTermPar) st : cvm_st :=
  execSt (copland_compile t) st.

Definition run_cvm' (t:Term) st : cvm_st :=
  run_cvm (annotated_par t) st.

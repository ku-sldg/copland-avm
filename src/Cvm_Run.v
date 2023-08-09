(* Top-level definitions for running CVM monad computations.  *)

Require Import Term_Defs Anno_Term_Defs Cvm_Impl Cvm_St ErrorStMonad_Coq.

Require Import List.
Import ListNotations.

Definition run_cvm (t:Core_Term) st : cvm_st :=
  execErr (build_cvm t (st.(st_AM_config))) st.

Definition run_cvm' (t:Term) st : cvm_st :=
  run_cvm (copland_compile t) st.

Definition run_cvm_fresh (t:Term) : cvm_st :=
  run_cvm' t empty_vmst.

Definition run_cvm_w_config (t:Term) (p:Plc) (e:RawEv) (ac : AM_Config) : cvm_st :=
  run_cvm' t (mk_st (evc e mt) [] p 0 ac).

Definition run_cvm_rawEv (t:Term) (p:Plc) (e:RawEv) (ac : AM_Config) : RawEv :=
  get_bits (st_ev (run_cvm_w_config t p e ac)).

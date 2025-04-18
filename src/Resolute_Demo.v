Require Import Term_Defs Demo_Terms.

Require Import String.

Require Import List.
Import ListNotations.


Open Scope string_scope.
(* Plcs *)
Definition micro_demo_plc : Plc := "micro_demo_Plc".

(* TARG IDs *)
Definition micro_demo_targ : TARG_ID := "micro_demo_targ".
Definition aadl_dir_targ : TARG_ID := "aadl_dir_targ".
Definition microkit_dir_targ : TARG_ID := "microkit_dir_targ".
Definition micro_hash_comp_targ : TARG_ID := "micro_hash_composite_targ".

(* Env vars *)
Definition am_root_env_var   : string := "AM_ROOT".
Definition hashdir_env_var : string := "INSPECTA_ROOT".

(* ASP_ARGS stuff *)
Definition path_micro_dir_1_golden : string :=
  "/tests/DemoFiles/goldenFiles/micro_dir_1_golden.txt".

Definition path_micro_dir_1 : string := 
    "/micro-examples/microkit/aadl_port_types/data/base_type/aadl/".

Definition path_micro_dir_2 : string := 
  "/micro-examples/microkit/aadl_port_types/data/base_type/hamr/microkit/".

  (*
Definition path_micro_dir_1_golden : string :=
  "/tests/DemoFiles/goldenFiles/micro_dir_1_golden.txt".
  *)
Definition path_micro_dir_2_golden : string :=
  "/tests/DemoFiles/goldenFiles/micro_dir_2_golden.txt".

Definition path_micro_composite_golden : string := 
  "/tests/DemoFiles/goldenFiles/micro_composite.txt".

Close Scope string_scope.

Definition provision_micro_dir_1 : Term := 
    (provision_targ_asp 
      micro_demo_plc 
      micro_demo_targ 
      am_root_env_var
      path_micro_dir_1_golden).


Definition provision_micro_dir_2 : Term := 
    (provision_targ_asp 
      micro_demo_plc 
      micro_demo_targ
      am_root_env_var
      path_micro_dir_2_golden).

Definition provision_micro_hash_composite : Term := 
      (provision_targ_asp 
      micro_demo_plc 
      micro_demo_targ
        am_root_env_var
        path_micro_composite_golden).

Definition hash_micro_dir_1 : Term := 
    (hash_dir_asp 
    micro_demo_plc  
        aadl_dir_targ 
        hashdir_env_var
        am_root_env_var
        [path_micro_dir_1]
        path_micro_dir_1_golden).
    
    Definition hash_micro_dir_2 : Term := 
    (hash_dir_asp 
    micro_demo_plc 
        microkit_dir_targ 
        hashdir_env_var
        am_root_env_var
        [path_micro_dir_2]
        path_micro_dir_2_golden).
    
    Definition hash_micro_evidence : Term := 
    (hash_evidence_asp 
    micro_demo_plc  
        micro_hash_comp_targ 
        am_root_env_var
        path_micro_composite_golden).
          


Open Scope cop_ent_scope.

Definition meas_micro : Term := 
    <{
      (hash_micro_dir_1 +<+ 
       hash_micro_dir_2) -> 
       hash_micro_evidence
    }>.

Definition appr_term : Term := (asp APPR).

Definition micro_appTerm : Term :=
<{
    ( meas_micro ) ->
    appr_term
}>.

Definition micro_appTerm_provision : Term :=
  <{
    (hash_micro_dir_1 -> provision_micro_dir_1) +<+
    (hash_micro_dir_2 -> provision_micro_dir_2) +<+
    (meas_micro -> provision_micro_hash_composite)
  }>.

Definition micro_appTerm_provision_dir_1 : Term :=
  <{
    (hash_micro_dir_1 -> provision_micro_dir_1)
  }>.

Definition micro_appTerm_provision_dir_2 : Term :=
  <{
    (hash_micro_dir_2 -> provision_micro_dir_2)
  }>.

Definition micro_appTerm_provision_composite : Term :=
  <{
  (meas_micro -> provision_micro_hash_composite)
  }>.
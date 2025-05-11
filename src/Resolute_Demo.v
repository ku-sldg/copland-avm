Require Import Term_Defs Demo_Terms JSON.

Require Import String.

Require Import List.
Import ListNotations.


Open Scope string_scope.
(* Plcs *)
Definition micro_demo_plc : Plc := "micro_demo_Plc".
Definition coq_demo_plc : Plc := "coq_demo_Plc".

(* TARG IDs *)
Definition micro_demo_targ : TARG_ID := "micro_demo_targ".
Definition aadl_dir_targ : TARG_ID := "aadl_dir_targ".
Definition microkit_dir_targ : TARG_ID := "microkit_dir_targ".
Definition micro_hash_comp_targ : TARG_ID := "micro_hash_composite_targ".

Definition run_coq_theorem_targ : TARG_ID := "run_coq_theorem_targ".
Definition run_coq_theorem_test_targ : TARG_ID := "run_coq_theorem_test_targ".
Definition coq_env_dir_targ : TARG_ID := "coq_env_dir_targ".

(* Env vars *)
Definition am_root_env_var   : string := "AM_ROOT".
Definition hashdir_env_var : string := "INSPECTA_ROOT".
Definition theorem_env_var : string := "THEOREM_ENV_ROOT".

(* ASP_ARGS stuff *)

Definition path_micro_dir_1 : string := 
    "/micro-examples/microkit/aadl_port_types/data/base_type/aadl/".
Definition path_micro_dir_1_golden : string :=
  "/tests/DemoFiles/goldenFiles/micro_dir_1_golden.txt".

Definition path_micro_dir_2 : string := 
  "/micro-examples/microkit/aadl_port_types/data/base_type/hamr/microkit/".
Definition path_micro_dir_2_golden : string :=
  "/tests/DemoFiles/goldenFiles/micro_dir_2_golden.txt".

Definition path_micro_composite_golden : string := 
  "/tests/DemoFiles/goldenFiles/micro_composite.txt".

Definition theorems_path : string := 
  "/Users/adampetz/Documents/Fall_2024/my_theorems/".

Definition theorems_env_path : string := 
  "/my_theorems_env/".

Definition theorems_env_dir_golden : string := 
  "/tests/DemoFiles/goldenFiles/theorems_env_dir_golden.txt".

Definition coqc_exe_path := "/Users/adampetz/Documents/Fall_2024/my_theorems_env/coqc".
Definition coqc_R : string := "-R".
Definition coqc_Module : string := "ImportantModule".

Definition path_asp_coq_golden : string := 
  "/tests/DemoFiles/goldenFiles/theorem_output_golden.txt".
Definition path_asp_coq_test_golden : string :=
  "/tests/DemoFiles/goldenFiles/theorem_test_output_golden.txt".

Definition provision_asp_coq_args : ASP_ARGS :=
    (JSON_Object [
        ("env_var_golden", (JSON_String am_root_env_var));
        ("filepath_golden", (JSON_String path_asp_coq_golden))]).

Definition provision_asp_coq_test_args : ASP_ARGS :=
  (JSON_Object [
      ("env_var_golden", (JSON_String am_root_env_var));
      ("filepath_golden", (JSON_String path_asp_coq_test_golden))]).

Definition provision_coq_env_dir_args : ASP_ARGS :=
  (JSON_Object [
      ("env_var_golden", (JSON_String am_root_env_var));
      ("filepath_golden", (JSON_String theorems_env_dir_golden))]).

Definition provision_micro_dir_1_args : ASP_ARGS :=
  (JSON_Object [
      ("env_var_golden", (JSON_String am_root_env_var));
      ("filepath_golden", (JSON_String path_micro_dir_1_golden))]).

Definition provision_micro_dir_2_args : ASP_ARGS :=
  (JSON_Object [
      ("env_var_golden", (JSON_String am_root_env_var));
      ("filepath_golden", (JSON_String path_micro_dir_2_golden))]).

Definition provision_micro_hash_composite_args : ASP_ARGS :=
  (JSON_Object [
      ("env_var_golden", (JSON_String am_root_env_var));
      ("filepath_golden", (JSON_String path_micro_composite_golden))]).

Definition hash_coq_env_dir_args : ASP_ARGS := 
  (JSON_Object [("env_var", (JSON_String theorem_env_var)); 
                ("env_var_golden", (JSON_String am_root_env_var));
                ("paths", (JSON_Array (map JSON_String [theorems_env_path])));
                ("filepath_golden", (JSON_String theorems_env_dir_golden));
                ("recursive", (JSON_Boolean true));
                ("omit_file_suffixes",  
                  (JSON_Array 
                    (map JSON_String [".glob"; ".vo"; ".vok"; ".vos"; ".aux"])))]).

Definition hash_micro_dir_1_args : ASP_ARGS := 
  (JSON_Object [("env_var", (JSON_String hashdir_env_var)); 
                ("env_var_golden", (JSON_String am_root_env_var));
                ("paths", (JSON_Array (map JSON_String [path_micro_dir_1])));
                ("filepath_golden", (JSON_String path_micro_dir_1_golden));
                ("recursive", (JSON_Boolean false));
                ("omit_file_suffixes", (JSON_Array []))]).

Definition hash_micro_dir_2_args : ASP_ARGS := 
  (JSON_Object [("env_var", (JSON_String hashdir_env_var)); 
                ("env_var_golden", (JSON_String am_root_env_var));
                ("paths", (JSON_Array (map JSON_String [path_micro_dir_2])));
                ("filepath_golden", (JSON_String path_micro_dir_2_golden));
                ("recursive", (JSON_Boolean false));
                ("omit_file_suffixes", (JSON_Array []))]).

Definition hash_micro_evidence_args : ASP_ARGS :=
  (JSON_Object [
      ("env_var_golden", (JSON_String am_root_env_var));
      ("filepath_golden", (JSON_String path_micro_composite_golden))]).

Definition run_command_asp_coq_args : ASP_ARGS :=
  (JSON_Object [
      ("exe_path", (JSON_String coqc_exe_path));
      ("exe_args", (JSON_Array 
                    (map JSON_String 
                      [coqc_R; 
                      theorems_path; 
                      coqc_Module; 
                      "/Users/adampetz/Documents/Fall_2024/my_theorems/ImportantTheorem.v"])));
      ("env_var_golden", (JSON_String  am_root_env_var));
      ("filepath_golden", (JSON_String path_asp_coq_golden))]).

Definition run_command_asp_coq_test_args : ASP_ARGS :=
  (JSON_Object [
      ("exe_path", (JSON_String coqc_exe_path));
      ("exe_args", (JSON_Array 
                    (map JSON_String 
                      [coqc_R; 
                      theorems_path; 
                      coqc_Module; 
                      "/Users/adampetz/Documents/Fall_2024/my_theorems_env/ImportantTheoremTest.v"])));
      ("env_var_golden", (JSON_String  am_root_env_var));
      ("filepath_golden", (JSON_String path_asp_coq_test_golden))]).

Close Scope string_scope.

Definition provision_asp_coq : Term := 
    (provision_targ_asp 
      coq_demo_plc 
      run_coq_theorem_targ 
      provision_asp_coq_args).

Definition provision_asp_coq_test : Term := 
  (provision_targ_asp 
    coq_demo_plc 
    run_coq_theorem_test_targ 
    provision_asp_coq_test_args).

Definition provision_coq_env_dir : Term := 
  (provision_targ_asp 
   coq_demo_plc 
   run_coq_theorem_test_targ
   provision_coq_env_dir_args).

Definition provision_micro_dir_1 : Term := 
    (provision_targ_asp 
      micro_demo_plc 
      micro_demo_targ 
      provision_micro_dir_1_args).

Definition provision_micro_dir_2 : Term := 
    (provision_targ_asp 
      micro_demo_plc 
      micro_demo_targ
      provision_micro_dir_2_args).

Definition provision_micro_hash_composite : Term := 
    (provision_targ_asp 
      micro_demo_plc 
      micro_demo_targ
      provision_micro_hash_composite_args).

Definition hash_coq_env_dir : Term := 
  (hash_dir_asp 
   coq_demo_plc 
   coq_env_dir_targ
   hash_coq_env_dir_args).

Definition hash_micro_dir_1 : Term := 
    (hash_dir_asp 
      micro_demo_plc  
      aadl_dir_targ 
      hash_micro_dir_1_args).
    
Definition hash_micro_dir_2 : Term := 
    (hash_dir_asp 
      micro_demo_plc 
      microkit_dir_targ 
      hash_micro_dir_2_args).
    
Definition hash_micro_evidence : Term := 
    (hash_evidence_asp 
      micro_demo_plc  
      micro_hash_comp_targ 
      hash_micro_evidence_args).

Definition run_command_asp_coq : Term := 
  (run_command_asp 
    coq_demo_plc  
    run_coq_theorem_targ 
    run_command_asp_coq_args).

Definition run_command_asp_coq_test : Term := 
  (run_command_asp 
    coq_demo_plc  
    run_coq_theorem_test_targ
    run_command_asp_coq_test_args).
          
Open Scope cop_ent_scope.

Definition appr_term : Term := (asp APPR).

Definition meas_theorem : Term := 
    <{
      hash_coq_env_dir +<+
      run_command_asp_coq +<+ 
      run_command_asp_coq_test
    }>.

Definition meas_theorem_appr : Term := 
  <{
    (meas_theorem) -> 
    appr_term
  }>.

Definition meas_micro : Term := 
    <{
      (hash_micro_dir_1 +<+ 
       hash_micro_dir_2) -> 
       hash_micro_evidence
    }>.

Definition micro_appTerm : Term :=
<{
    ( meas_micro ) ->
    appr_term
}>.

Definition coq_appTerm_provision : Term := 
<{
  (hash_coq_env_dir -> provision_coq_env_dir) +<+
  (run_command_asp_coq -> provision_asp_coq) +<+ 
  (run_command_asp_coq_test -> provision_asp_coq_test)
}>.

Definition micro_appTerm_provision : Term :=
  <{
    (hash_micro_dir_1 -> provision_micro_dir_1) +<+
    (hash_micro_dir_2 -> provision_micro_dir_2) +<+
    (meas_micro -> provision_micro_hash_composite)
  }>.


Definition coq_env_provision_dir : Term :=
  <{
    (hash_coq_env_dir -> provision_coq_env_dir)
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
Close Scope cop_ent_scope.


Open Scope string_scope.
Definition resolute_terms_map := 
  [
    ("micro", micro_appTerm);
    ("micro_provision", micro_appTerm_provision);
    ("micro_provision_dir_1", micro_appTerm_provision_dir_1);
    ("micro_provision_dir_2", micro_appTerm_provision_dir_2);
    ("micro_provision_composite", micro_appTerm_provision_composite);
    ("run_coq_thm", run_command_asp_coq);
    ("run_coq_test", run_command_asp_coq_test);
    ("run_coq_all", meas_theorem);
    ("run_coq_all_appr", meas_theorem_appr);
    ("run_coq_all_appr_provision", coq_appTerm_provision);
    ("coq_env_dir_provision", coq_env_provision_dir)
  ].
Close Scope string_scope.
Require Import Term_Defs Maps ID_Type EqClass.

Require Import Manifest_Set JSON ErrorStringConstants.

Require Import Flexible_Mechanisms_Vars.

Require Import Demo_Terms.

Require Import Cvm_Utils CACL_Demo_Args.

Require Import List.
Import ListNotations.


Open Scope string_scope.

(* CDS demo vars *)

(* Plc IDs *)
Definition cds_config_dir_plc : Plc := "cds_config_dir_plc".
Definition cds_query_kim_plc : Plc := "cds_query_kim_plc".

(* TARG IDs *)
Definition kim_evidence_targ : TARG_ID := "kernal_module_targ".
Definition selinux_policy_targ : TARG_ID := "selinux_policy_targ".
Definition ssl_sig_targ : TARG_ID := "ssl_sig_targ".
Definition tpm_sig_targ : TARG_ID := "tpm_sig_targ".

Definition in_targ  : TARG_ID := "in_targ".
Definition out_targ : TARG_ID := "out_targ".

Definition cds_exe_dir_targ : TARG_ID := "cds_exe_dir_targ".
Definition cds_exe_1_targ : TARG_ID := "cds_exe_1_targ".
Definition cds_exe_2_targ : TARG_ID := "cds_exe_2_targ".
Definition cds_exe_3_targ : TARG_ID := "cds_exe_3_targ".
Definition tmp_1_targ : TARG_ID := "tmp_1_targ".
Definition tmp_2_targ : TARG_ID := "tmp_2_targ".
Definition tmp_3_targ : TARG_ID := "tmp_3_targ".

Definition cds_flags_dir_targ : TARG_ID := "cds_flags_dir_targ".
Definition cds_flags_1_targ : TARG_ID := "cds_flags_1_targ".
Definition cds_flags_2_targ : TARG_ID := "cds_flags_2_targ".
Definition cds_flags_3_targ : TARG_ID := "cds_flags_3_targ".

Definition cds_controller_dir_targ : TARG_ID := "cds_controller_dir_targ".
Definition cds_controller_exe_targ : TARG_ID := "cds_controller_exe_targ".

Definition cds_config_1_targ : TARG_ID := "cds_rewrite_config_targ".
Definition cds_config_2_targ : TARG_ID := "cds_filter_config_2_targ".
Definition cds_config_3_targ : TARG_ID := "cds_config_3_targ".
Definition cds_img_1_targ : TARG_ID := "cds_rewrite_img_targ".
Definition cds_img_2_targ : TARG_ID := "cds_filter_img_targ".
Definition cds_img_3_targ : TARG_ID := "cds_img_3_targ".

(* ASP IDs *)
Definition query_kim : ASP_ID := "invary_get_measurement".
Definition query_kim_stub : ASP_ID := "invary_get_measurement_stub".
Definition appr_gather_file_contents : ASP_ID := "readfile_appr".
Definition appr_hash_file_contents : ASP_ID := "hashfile_appr".
Definition appr_hash_evidence : ASP_ID := "hashevidence_appr".

Definition appr_cds : ASP_ID := "cds_appr".
Definition appr_query_kim : ASP_ID := "invary_get_measurement_appr".
Definition appr_query_kim_stub : ASP_ID := "invary_get_measurement_stub_appr".
Definition ssl_sig : ASP_ID := "ssl_sig".
Definition ssl_sig_appr : ASP_ID := "ssl_sig_appr".
Definition tpm_sig : ASP_ID := "sig_tpm".
Definition tpm_sig_appr : ASP_ID := "sig_tpm_appr".

Definition selinux_pol_dump : ASP_ID := "selinux_pol_dump".
Definition selinux_pol_dump_appr : ASP_ID := "hashfile_appr".

Definition r_ssl_sig : ASP_ID := "sig".
Definition r_ssl_sig_appr : ASP_ID := "sig_appr".

Definition selinux_hash_asp (targPlc:Plc) (targId:TARG_ID) 
    (env_var_golden:string) (path_golden:string) : Term := 
    (asp (ASPC (asp_paramsC 
                    selinux_pol_dump
                    (JSON_Object [
                        ("env_var_golden", (JSON_String env_var_golden));
                        ("filepath_golden", (JSON_String path_golden))])
                    targPlc 
                    targId ))).


Close Scope string_scope.


Open Scope cop_ent_scope.

Definition demo_root_env_var : string := "DEMO_ROOT".
Definition am_root_env_var   : string := "AM_ROOT".

Definition path_targ1 : string := 
    "/cds_config/rewrite_one_config.json".

Definition path_targ1_golden : string := 
    "/tests/DemoFiles/goldenFiles/rewrite_one_config.json".

Definition path_targ2 : string := 
    "/cds_config/filter_one_config.json".
    
Definition path_targ2_golden : string := 
    "/tests/DemoFiles/goldenFiles/filter_one_config.json".

Definition path_targ3 : string := 
    "/tests/DemoFiles/targFiles/targFile3.txt".

Definition path_targ3_golden : string := 
    "/tests/DemoFiles/goldenFiles/targFile3.txt".

Definition path_exe_targ1 : string := 
    "/installed_dir/bin/rewrite_one".

Definition path_exe_targ1_golden : string := 
    "/tests/DemoFiles/goldenFiles/rewrite_one".

Definition path_exe_targ2 : string := 
    "/installed_dir/bin/filter_one".
    
Definition path_exe_targ2_golden : string := 
    "/tests/DemoFiles/goldenFiles/filter_one".

Definition selinux_policy_path_golden : string := 
    "/tests/DemoFiles/goldenFiles/demo_pipeline_golden.cil".

Definition gather_config_1 : Term := 
    (gather_targ_asp 
        cds_config_dir_plc 
        cds_config_1_targ 
        demo_root_env_var (* env_var *)
        am_root_env_var   (* env_var_golden *)
        path_targ1 
        path_targ1_golden).

Definition gather_config_2 : Term := 
    (gather_targ_asp 
        cds_config_dir_plc 
        cds_config_2_targ 
        demo_root_env_var (* env_var *)
        am_root_env_var   (* env_var_golden *)
        path_targ2 path_targ2_golden).

Definition gather_config_3 : Term := 
    (gather_targ_asp 
        cds_config_dir_plc 
        cds_config_3_targ 
        demo_root_env_var (* env_var *)
        am_root_env_var   (* env_var_golden *)
        path_targ3 
        path_targ3_golden).

Definition hash_cds_img_1 : Term := 
    (hash_targ_asp 
        cds_config_dir_plc 
        cds_img_1_targ 
        demo_root_env_var (* env_var *)
        am_root_env_var   (* env_var_golden *)
        path_exe_targ1 
        path_exe_targ1_golden).

Definition hash_cds_img_2 : Term := 
    (hash_targ_asp 
        cds_config_dir_plc 
        cds_img_2_targ
        demo_root_env_var (* env_var *)
        am_root_env_var   (* env_var_golden *)
        path_exe_targ2 
        path_exe_targ2_golden).

Definition selinux_hash_pol : Term := 
    (selinux_hash_asp 
        cds_config_dir_plc 
        selinux_policy_targ 
        am_root_env_var
        selinux_policy_path_golden).

Definition provision_config_1 : Term := 
    (provision_targ_asp 
        cds_config_dir_plc
        cds_config_1_targ 
        am_root_env_var
        path_targ1_golden).

Definition provision_config_2 : Term := 
    (provision_targ_asp 
        cds_config_dir_plc 
        cds_config_2_targ 
        am_root_env_var
        path_targ2_golden).

Definition provision_config_3 : Term := 
    (provision_targ_asp 
        cds_config_dir_plc 
        cds_config_3_targ 
        am_root_env_var
        path_targ3_golden).

Definition provision_img_1 : Term := 
    (provision_targ_asp 
        cds_config_dir_plc 
        cds_img_1_targ 
        am_root_env_var
        path_exe_targ1_golden).

Definition provision_img_2 : Term := 
    (provision_targ_asp 
        cds_config_dir_plc 
        cds_img_2_targ 
        am_root_env_var
        path_exe_targ2_golden).

Definition meas_cds_phrase : Term :=
<{
    gather_config_1 ->
    gather_config_2 ->
    gather_config_3 ->
    hash_cds_img_1 ->
    hash_cds_img_2
}>.

Definition query_kim_args : ASP_ARGS := 
    JSON_Object 
        [(query_kim_dynamic_arg, (JSON_String query_kim_dynamic_arg_val));
         (query_kim_env_var_arg, (JSON_String am_root_env_var));
         (query_kim_appraisal_dir_arg, (JSON_String query_kim_appraisal_dir_arg_val))].

Definition query_kim_asp : Term := 
    (asp (ASPC (asp_paramsC 
                    query_kim 
                    query_kim_args 
                    cds_query_kim_plc 
                    kim_evidence_targ))).

Definition ssl_sig_asp : Term := 
    (asp (ASPC (asp_paramsC 
                    ssl_sig 
                    (JSON_Object []) 
                    cds_query_kim_plc 
                    ssl_sig_targ))).

Definition r_ssl_sig_asp : Term := 
        (asp (ASPC (asp_paramsC 
                        r_ssl_sig 
                        (JSON_Object []) 
                        cds_query_kim_plc 
                        ssl_sig_targ))).

Definition query_kim_asp_stub : Term := 
        (asp (ASPC (asp_paramsC 
                        query_kim_stub 
                        (JSON_Object []) 
                        cds_query_kim_plc 
                        kim_evidence_targ))).

Definition appr_cds_asp : Term := 
    (asp (ASPC (asp_paramsC 
                    appr_cds 
                    (JSON_Object []) 
                    P1 sys_targ))).

Definition sig_asp : Term := asp SIG.

Definition r_tpm_sig_asp : Term := 
        (asp (ASPC (asp_paramsC 
                        tpm_sig 
                        (JSON_Object [("tpm_folder"%string, JSON_String "$AM_TPM_DIR")]) 
                        cds_query_kim_plc 
                        tpm_sig_targ))).

Definition appr_term : Term := (asp APPR).


Definition meas_cds : Term := 
<{
  (selinux_hash_pol +<+
   hash_cds_img_1 +<+
   hash_cds_img_2 +<+
   gather_config_1 +<+ 
   gather_config_2 )
}>.

Definition cds_ssl : Term :=
<{
    (query_kim_asp +<+ meas_cds) ->
    r_ssl_sig_asp ->
    appr_term
}>. 
    
Definition cds_tpm : Term :=
<{
    (query_kim_asp +<+ meas_cds) ->
    r_tpm_sig_asp ->
    appr_term
}>. 

Definition simple_sig : Term := 
lseq 
(
  lseq
(asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
r_ssl_sig_asp) 
appr_term.

Definition example_appTerm : Term :=
<{
    ( meas_cds ) ->
    appr_term
}>.

Definition meas_cds_local : Term := 
<{
  (gather_config_1 +<+ 
   gather_config_2 )
}>.

Definition cds_local : Term :=
<{
    (query_kim_asp +<+
     meas_cds_local) ->
    r_ssl_sig_asp ->
    appr_term
}>. 

Definition example_appTerm_provision : Term :=
<{
    (gather_config_1 -> provision_config_1) +<+
    (gather_config_2 -> provision_config_2) +<+
    (hash_cds_img_1   -> provision_img_1) +<+
    (hash_cds_img_2   -> provision_img_2)
}>.

Close Scope cop_ent_scope.



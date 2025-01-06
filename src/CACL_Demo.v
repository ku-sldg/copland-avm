Require Import Term_Defs Maps ID_Type EqClass.

Require Import Manifest_Set JSON ErrorStringConstants.

Require Import Flexible_Mechanisms_Vars.

Require Import CACL_Defs CACL_Typeclasses CACL_Generator.

Require Import Cvm_Utils RawEvJudgement_Admits CACL_Demo_Args.

Require Import List.
Import ListNotations.


Open Scope string_scope.

(* CDS demo vars *)

(* Plc IDs *)
Definition cds_config_dir_plc : Plc := "cds_config_dir_plc".
Definition cds_query_kim_plc : Plc := "cds_query_kim_plc".

(* TARG IDs *)
Definition kim_evidence_targ : TARG_ID := "kim_evidence_targ".
Definition ssl_sig_targ : TARG_ID := "ssl_sig_targ".

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

Definition cds_config_1_targ : TARG_ID := "cds_config_1_targ".
Definition cds_config_2_targ : TARG_ID := "cds_config_2_targ".
Definition cds_config_3_targ : TARG_ID := "cds_config_3_targ".
Definition cds_img_1_targ : TARG_ID := "cds_img_1_targ".
Definition cds_img_2_targ : TARG_ID := "cds_img_2_targ".
Definition cds_img_3_targ : TARG_ID := "cds_img_3_targ".

(* ASP IDs *)
Definition query_kim_id : ASP_ID := "r_invary_get_measurement_id". (* "query_kim_id" *)
Definition query_kim_stub_id : ASP_ID := "r_invary_get_measurement_stub_id".
Definition hash_file_contents_id : ASP_ID := "r_hashfile_id".
Definition hash_dir_contents_id : ASP_ID := "r_hashdir_id".
Definition hash_evidence_id : ASP_ID := "r_hashevidence_id".
Definition gather_file_contents_id : ASP_ID := "r_readfile_id". (* "gather_file_contents_id" *)
Definition appr_gather_file_contents_id : ASP_ID := "appraise_r_readfile_id".
Definition appr_hash_file_contents_id : ASP_ID := "appraise_r_hashfile_id".
Definition appr_hash_evidence_id : ASP_ID := "appraise_r_hashevidence_id".
Definition provision_id : ASP_ID := "r_provision_id".
Definition appr_cds_id : ASP_ID := "appr_cds_id".
Definition appr_query_kim_id : ASP_ID := "appraise_r_invary_get_measurement_id".
Definition appr_query_kim_stub_id : ASP_ID := "appraise_r_invary_get_measurement_stub_id".
Definition ssl_sig_id : ASP_ID := "ssl_sig_id".
Definition ssl_sig_appr_id : ASP_ID := "ssl_sig_appr_id".
Definition tpm_sig_id : ASP_ID := "r_sig_tpm".
Definition tpm_sig_appr_id : ASP_ID := "appraise_r_sig_tpm".

Definition r_ssl_sig_id : ASP_ID := "r_sig".
Definition r_ssl_sig_appr_id : ASP_ID := "appraise_r_sig".

Definition gather_targ_asp (targPlc:Plc) (targId:TARG_ID) (path:string) (appr_path:string) : Term := 
    (asp (ASPC (* ALL (EXTD 1)  *)
               (asp_paramsC 
                    gather_file_contents_id 
                    [("filepath", path); 
                     ("filepath-golden", appr_path)] 
                    targPlc 
                    targId ))).

Definition hash_targ_asp (targPlc:Plc) (targId:TARG_ID) (path:string) (appr_path:string) : Term := 
    (asp (ASPC (* ALL (EXTD 1) *)
                (asp_paramsC 
                    hash_file_contents_id 
                    [("filepath", path); 
                     ("filepath-golden", appr_path)]
                    targPlc 
                    targId ))).

Definition hash_dir_asp (targPlc:Plc) (targId:TARG_ID) (args:ASP_ARGS) : Term := 
    (asp (ASPC (* ALL (EXTD 1) *)
                (asp_paramsC 
                    hash_dir_contents_id 
                    args
                    targPlc 
                    targId ))).

Definition provision_targ_asp (targPlc:Plc) (targId:TARG_ID) (path:string) : Term := 
    (asp (ASPC (* ALL (EXTD 1)  *)
                (asp_paramsC 
                    provision_id 
                    [("filepath", path)] 
                    targPlc 
                    targId ))).

Definition provision_dir_asp (targPlc:Plc) (targId:TARG_ID) (args:ASP_ARGS) : Term := 
    (asp (ASPC (* ALL (EXTD 1)  *)
                (asp_paramsC 
                    provision_id 
                    args 
                    targPlc 
                    targId ))).

Definition hash_evidence_asp (targPlc:Plc) (targId:TARG_ID) (appr_path:string) : Term := 
    (asp (ASPC (* ALL (EXTD 1) *)
                (asp_paramsC 
                    hash_evidence_id 
                    [ ("filepath-golden", appr_path)] 
                    targPlc 
                    targId ))).


Close Scope string_scope.


Open Scope cop_ent_scope.

Definition path_targ1 : string := 
    "/LayeredAttestation/src/demo_layered_attestation/cds_config/rewrite_one_config.json".

Definition path_targ1_golden : string := 
    "/am-cakeml/tests/DemoFiles/goldenFiles/rewrite_one_config.json".


Definition path_micro_targ1 : string := 
    "/INSPECTA-models/micro-examples/microkit/aadl_port_types/data/base_type/aadl/data_1_prod_2_cons.aadl".
    (* "/LayeredAttestation/src/demo_layered_attestation/cds_config/rewrite_one_config.json". *)
    
Definition path_micro_targ1_golden : string := 
    "/am-cakeml/tests/DemoFiles/goldenFiles/data_1_prod_2_cons.aadl".

Definition path_micro_targ2 : string := 
    "/INSPECTA-models/micro-examples/microkit/aadl_port_types/data/base_type/hamr/microkit/microkit.system".
       (* "/LayeredAttestation/src/demo_layered_attestation/cds_config/filter_one_config.json". *)
        
Definition path_micro_targ2_golden : string := 
        "/am-cakeml/tests/DemoFiles/goldenFiles/microkit.system".

Definition path_micro_composite_golden : string := 
        "/am-cakeml/tests/DemoFiles/goldenFiles/micro_composite.txt".

Definition path_targ2 : string := 
    "/LayeredAttestation/src/demo_layered_attestation/cds_config/filter_one_config.json".
    
Definition path_targ2_golden : string := 
    "/am-cakeml/tests/DemoFiles/goldenFiles/filter_one_config.json".

Definition path_targ3 : string := 
    "/tests/DemoFiles/targFiles/targFile3.txt".

Definition path_targ3_golden : string := 
    "/tests/DemoFiles/goldenFiles/targFile3.txt".

Definition path_exe_targ1 : string := 
    "/tests/DemoFiles/targFiles/targExe1.exe".

Definition path_exe_targ1_golden : string := 
    "/tests/DemoFiles/goldenFiles/targExe1.exe".

Definition gather_config_1 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_1_targ path_targ1 path_targ1_golden).

Definition gather_config_2 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_2_targ path_targ2 path_targ2_golden).

Definition gather_config_3 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_3_targ path_targ3 path_targ3_golden).

Definition hash_cds_img_1 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_1_targ 
     path_exe_targ1 path_exe_targ1_golden).

Definition hash_cds_img_2 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_2_targ
     path_exe_targ1 path_exe_targ1_golden).

Definition hash_cds_img_3 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_3_targ
     path_exe_targ1 path_exe_targ1_golden).

Definition hash_controller_img : Term := 
    (hash_targ_asp cds_controller_dir_targ cds_controller_exe_targ
    path_exe_targ1 path_exe_targ1_golden).


Definition provision_config_1 : Term := 
    (provision_targ_asp cds_config_dir_plc cds_config_1_targ path_targ1_golden).

Definition provision_config_2 : Term := 
    (provision_targ_asp cds_config_dir_plc cds_config_2_targ path_targ2_golden).

Definition provision_config_3 : Term := 
(provision_targ_asp cds_config_dir_plc cds_config_3_targ path_targ3_golden).

Definition provision_img_1 : Term := 
    (provision_targ_asp cds_config_dir_plc cds_img_1_targ path_exe_targ1_golden).

Definition meas_cds_phrase : Term :=
<{
    gather_config_1
    ->
    gather_config_2
    ->
    gather_config_3
    ->
    hash_controller_img 
    ->
    hash_cds_img_1
    ->
    hash_cds_img_2
    ->
    hash_cds_img_3
}>.

Definition query_kim_args : ASP_ARGS := 
    [(query_kim_dynammic_arg_id, query_kim_dynammic_arg_val);
     (query_kim_appraisal_dir_arg_id, query_kim_appraisal_dir_arg_val)].

Definition query_kim_asp : Term := 
    (asp (ASPC (asp_paramsC query_kim_id query_kim_args cds_query_kim_plc kim_evidence_targ))).

Definition ssl_sig_asp : Term := 
    (asp (ASPC (asp_paramsC ssl_sig_id [] cds_query_kim_plc ssl_sig_targ))).

Definition r_ssl_sig_asp : Term := 
        (asp (ASPC (asp_paramsC r_ssl_sig_id [] cds_query_kim_plc ssl_sig_targ))).

Definition query_kim_asp_stub : Term := 
        (asp (ASPC (asp_paramsC query_kim_stub_id [] cds_query_kim_plc kim_evidence_targ))).

Definition appr_cds_asp : Term := 
    (asp (ASPC (asp_paramsC appr_cds_id [] P1 sys_targ))).

Definition sig_asp : Term := asp SIG.

Definition r_tpm_sig_asp : Term := 
        (asp (ASPC (asp_paramsC tpm_sig_id [] cds_query_kim_plc ssl_sig_targ))).

Definition cds_demo_phrase : Term := 
<{
  @ P1 
  [
    (
    query_kim_asp ->
    meas_cds_phrase
     ) ->
    sig_asp
  ] -> 
  @ P3 [ appr_cds_asp ]
}>.

Close Scope cop_ent_scope.


Definition cds_demo_arch_policy : CACL_Policy := 
    [
    (cds_exe_1_targ, [(in_targ, CACL_Read)]);

    (cds_exe_2_targ, [(tmp_1_targ, CACL_Read)]);
    (cds_exe_3_targ, [(tmp_2_targ, CACL_Read)]);
    (out_targ, [(tmp_3_targ, CACL_Read)]);
    (cds_exe_1_targ, [(tmp_1_targ, CACL_Write)]);
    (cds_exe_2_targ, [(tmp_2_targ, CACL_Write)]);
    (cds_exe_3_targ, [(tmp_3_targ, CACL_Write)]);

    (cds_exe_1_targ, [(cds_config_1_targ, CACL_Read)]);
    (cds_exe_2_targ, [(cds_config_2_targ, CACL_Read)]);
    (cds_exe_3_targ, [(cds_config_3_targ, CACL_Read)]);

    (cds_controller_exe_targ, [(cds_exe_dir_targ, CACL_Write)]);
    (cds_controller_exe_targ, [(cds_exe_dir_targ, CACL_Invoke)]);

    (cds_controller_exe_targ, [(cds_flags_dir_targ, CACL_Read)]);
    (cds_controller_exe_targ, [(cds_flags_dir_targ, CACL_Write)]);

    (cds_exe_1_targ, [(cds_flags_1_targ, CACL_Write)]);
    (cds_exe_2_targ, [(cds_flags_2_targ, CACL_Write)]);
    (cds_exe_3_targ, [(cds_flags_3_targ, CACL_Write)])
    ].


Definition test_cacl_compute := 
    CACL_policy_union 
        cds_demo_arch_policy
        (CACL_policy_generator cds_demo_phrase P0).





Require Import Term_Defs Maps ID_Type EqClass.

Require Import Manifest_Set JSON ErrorStringConstants.

Require Import Flexible_Mechanisms_Vars.

Require Import CACL_Defs CACL_Typeclasses CACL_Generator.

Require Import Cvm_Utils RawEvJudgement_Admits.

Require Import List.
Import ListNotations.


Open Scope string_scope.

(* CDS demo vars *)

(* Plc IDs *)
Definition cds_config_dir_plc : Plc := "cds_config_dir_plc".

(* TARG IDs *)
Definition kim_evidence_targ : TARG_ID := "kim_evidence_targ".

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
Definition query_kim_id : ASP_ID := "query_kim_id".
Definition hash_file_contents_id : ASP_ID := "r_hashfile_id".
Definition gather_file_contents_id : ASP_ID := "r_readfile_id". (* "gather_file_contents_id" *)
Definition appr_gather_file_contents_id : ASP_ID := "appraise_r_readfile_id".
Definition appr_hash_file_contents_id : ASP_ID := "appraise_r_hashfile_id".
Definition provision_id : ASP_ID := "r_provision_id".
Definition appr_cds_id : ASP_ID := "appr_cds_id".

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


Definition provision_targ_asp (targPlc:Plc) (targId:TARG_ID) (path:string) : Term := 
    (asp (ASPC (* ALL (EXTD 1)  *)
                (asp_paramsC 
                    provision_id 
                    [("filepath", path)] 
                    targPlc 
                    targId ))).


Close Scope string_scope.


Open Scope cop_ent_scope.

Definition path_targ1 : string := 
    "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/targFiles/targFile1.txt".

Definition path_targ2 : string := 
    "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/targFiles/targFile2.txt".

Definition path_targ3 : string := 
    "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/targFiles/targFile3.txt".

Definition path_targ1_golden : string := 
    "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/goldenFiles/targFile1.txt".

Definition path_targ2_golden : string := 
    "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/goldenFiles/targFile2.txt".

Definition path_targ3_golden : string := 
    "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/goldenFiles/targFile3.txt".

Definition path_exe_targ1 : string := 
    "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/targFiles/targExe1.exe".

Definition path_exe_targ1_golden : string := 
    "/Users/adampetz/Documents/Spring_2023/am-cakeml/tests/DemoFiles/goldenFiles/targExe1.exe".

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

Definition query_kim_asp : Term := 
    (asp (ASPC (asp_paramsC query_kim_id [] P1 kim_evidence_targ))).

Definition appr_cds_asp : Term := 
    (asp (ASPC (asp_paramsC appr_cds_id [] P1 sys_targ))).

Definition sig_asp : Term := asp SIG.

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





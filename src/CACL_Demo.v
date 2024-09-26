Require Import Term_Defs Maps ID_Type EqClass.

Require Import Manifest_Set JSON JSON_Core.

Require Import Flexible_Mechanisms_Vars.

Require Import CACL.

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
Definition hash_file_contents_id : ASP_ID := "hash_file_contents_id".
Definition gather_file_contents_id : ASP_ID := "gather_file_contents_id".
Definition appr_cds_id : ASP_ID := "appr_cds_id".

Close Scope string_scope.




Definition gather_targ_asp (targPlc:Plc) (targId:TARG_ID) : Term := 
    (asp (ASPC (* ALL (EXTD 1)  *)
               (asp_paramsC 
                    gather_file_contents_id 
                    [] 
                    targPlc 
                    targId ))).

Definition hash_targ_asp (targPlc:Plc) (targId:TARG_ID) : Term := 
    (asp (ASPC (* ALL (EXTD 1) *)
                (asp_paramsC 
                    hash_file_contents_id 
                    [] 
                    targPlc 
                    targId ))).


Open Scope cop_ent_scope.

Definition gather_config_1 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_1_targ).

Definition gather_config_2 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_2_targ).

Definition gather_config_3 : Term := 
    (gather_targ_asp cds_config_dir_plc cds_config_3_targ).

Definition hash_cds_img_1 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_1_targ).

Definition hash_cds_img_2 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_2_targ).

Definition hash_cds_img_3 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_3_targ).

Definition hash_controller_img : Term := 
    (hash_targ_asp cds_controller_dir_targ cds_controller_exe_targ).

Definition meas_cds_phrase : Term :=
<{
    gather_config_1
    +<+
    gather_config_2
    +<+
    gather_config_3
    +<+
    hash_controller_img 
    +<+
    hash_cds_img_1
    +<+
    hash_cds_img_2
    +<+
    hash_cds_img_3
}>.

Definition query_kim_asp : Term := 
    (asp (ASPC (* ALL (EXTD 1) *) (asp_paramsC query_kim_id [] P1 kim_evidence_targ))).

Definition appr_cds_asp : Term := 
    (asp (ASPC (* ALL (EXTD 1) *) (asp_paramsC appr_cds_id [] P1 sys_targ))).

Definition sig_asp : Term := asp SIG.

Definition cds_demo_phrase : Term := 
<{
  @ P1 
  [
    (
    query_kim_asp +<+
    meas_cds_phrase
     ) ->
    sig_asp
  ] -> 
  @ P3 [ appr_cds_asp ]
}>.


Print cds_demo_phrase.

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


(*
Definition example_cacl_policy : CACL_Policy := 
    [(P1, [(attest_id, CACL_Invoke)]);
        (P2, [(appraise_id, CACL_Invoke);
            (certificate_id, CACL_Invoke)]);
        (attest_id, [(sys_targ, CACL_Read)])
        ].
*)
(* (CACL_policy_union example_cacl_policy example_cacl_policy). *)


Definition test_cacl_compute := 
    CACL_policy_union 
        cds_demo_arch_policy
        (CACL_policy_generator cds_demo_phrase P0).


(*
Definition test_cacl_compute_json : JSON := to_JSON test_cacl_compute.
*)
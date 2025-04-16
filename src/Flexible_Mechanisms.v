Require Import Term_Defs Flexible_Mechanisms_Vars JSON_Type CACL_Demo.
Require Import List String.
Import ListNotations.

(* Flexible Mechanisms *)
Definition certificate_style : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
      (att P2 (
        lseq 
          (asp (ASPC (asp_paramsC appraise (JSON_Object []) P2 sys_targ)))
          (asp (ASPC (asp_paramsC certificate (JSON_Object []) P2 sys_targ)))
      ))
  ).

Definition background_check : Term :=
  lseq
    (att P1 (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ))))
    (att P2 (asp (ASPC (asp_paramsC appraise (JSON_Object []) P2 sys_targ)))).

Definition parallel_mutual_1 : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
      (att P2 (asp (ASPC (asp_paramsC appraise (JSON_Object []) P2 sys_targ))))
  ).

Definition layered_background_check : Term :=
  att P1
    (bpar (ALL, ALL)
      (lseq
        (att P1 (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ))))
        (lseq 
          (asp (ASPC (asp_paramsC attest (JSON_Object []) P3 sys_targ)))
          (asp (ASPC (asp_paramsC attest (JSON_Object []) P4 sys_targ)))
        )
      )
      (bpar (ALL, ALL)
        (att P3 (asp (ASPC (asp_paramsC attest (JSON_Object []) P3 sys_targ))))
        (lseq
          (att P4 (asp (ASPC (asp_paramsC attest (JSON_Object []) P4 sys_targ))))
          (att P2 (
            (lseq
              (asp (ASPC (asp_paramsC appraise (JSON_Object []) P2 sys_targ)))
              (asp (ASPC sig_params))
            )
          )
          )
        )
      )
    ).

Definition filehash_auth_phrase : Term := 
  att P1 
    (lseq 
      (asp (ASPC (asp_paramsC hashfile (JSON_Object []) P1 sys_targ)))
      (asp SIG) 
    ).

Definition split_phrase : Term :=
  att P1 ( 
    bseq (ALL, ALL)
      (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
      (asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
    ).

Definition large_output_asp_test : Term :=
  asp (ASPC (asp_paramsC large_output (JSON_Object []) P1 sys_targ)).

Open Scope cop_ent_scope.

Definition appr_term : Term := (asp APPR).

(*
Definition example_appTerm : Term :=
<{
    (gather_config_1 (* +<+
      query_kim_asp *)
    (*
    gather_config_2 +<+
    gather_config_3 *) )
     (* gather_config_2  *)
     (* query_kim_asp) *)
    
    (* +<+
    gather_config_2 +<+
    gather_config_3 +<+ 
    hash_cds_img_1) *) ->
    appr_term
}>.
*)

(*
Definition example_appTerm' : Term := 
  (asp (ASPC (asp_paramsC attest2 [] P1 sys_targ))).
*)

Definition meas_cds : Term := 
<{
  (selinux_hash_pol +<+
   hash_cds_img_1 +<+
   hash_cds_img_2 +<+
   gather_config_1 +<+ 
   gather_config_2 )
}>.

(*
Definition hash_micro_config_1 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_1_targ 
    path_micro_targ1 path_micro_targ1_golden).

Definition hash_micro_config_2 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_2_targ 
    path_micro_targ2 path_micro_targ2_golden).
    *)

Definition hashdir_env_var : string := "INSPECTA_ROOT".

Definition path_micro_dir_1 : string := 
    "/micro-examples/microkit/aadl_port_types/data/base_type/aadl/".

Definition path_micro_dir_2 : string := 
  "/micro-examples/microkit/aadl_port_types/data/base_type/hamr/microkit/".

Definition path_micro_dir_1_golden : string :=
  "/tests/DemoFiles/goldenFiles/micro_dir_1_golden.txt".
Definition path_micro_dir_2_golden : string :=
  "/tests/DemoFiles/goldenFiles/micro_dir_2_golden.txt".

Definition hash_micro_dir_1 : Term := 
  (hash_dir_asp 
    cds_config_dir_plc 
    aadl_dir_targ 
    hashdir_env_var
    [path_micro_dir_1]
    path_micro_dir_1_golden).

Definition hash_micro_dir_2 : Term := 
  (hash_dir_asp 
    cds_config_dir_plc 
    microkit_dir_targ 
    hashdir_env_var
    [path_micro_dir_2]
    path_micro_dir_2_golden).

Definition hash_micro_evidence : Term := 
  (hash_evidence_asp 
    cds_config_dir_plc 
    micro_hash_comp_targ 
    path_micro_composite_golden).

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

Definition example_appTerm : Term :=
<{
    ( meas_cds ) ->
    appr_term
}>.

Definition cds_ssl : Term :=
<{
    (query_kim_asp +<+
     meas_cds) ->
    r_ssl_sig_asp ->
    appr_term
}>. 

Definition cds_tpm : Term :=
<{
    (query_kim_asp +<+
     meas_cds) ->
    r_tpm_sig_asp ->
    appr_term
}>. 

Definition provision_micro_dir_1 : Term := 
    (provision_targ_asp 
      cds_config_dir_plc 
      cds_config_1_targ 
      path_micro_dir_1_golden).

Definition provision_micro_dir_2 : Term := 
    (provision_targ_asp 
      cds_config_dir_plc 
      cds_config_1_targ 
      path_micro_dir_2_golden).

Definition provision_micro_hash_composite : Term := 
      (provision_targ_asp 
        cds_config_dir_plc 
        cds_config_1_targ
        path_micro_composite_golden).

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

Definition example_appTerm_provision : Term :=
<{
    (gather_config_1 -> provision_config_1) +<+
    (gather_config_2 -> provision_config_2) +<+
    (hash_cds_img_1   -> provision_img_1) +<+
    (hash_cds_img_2   -> provision_img_2)
}>.

Definition simple_sig : Term := 
lseq 
(
  lseq
(asp (ASPC (asp_paramsC attest (JSON_Object []) P1 sys_targ)))
r_ssl_sig_asp) 
appr_term.


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



Close Scope cop_ent_scope.


Open Scope string_scope.
Definition flexible_mechanisms_map := 
  [("cert", certificate_style); 
   ("cert_appr", lseq certificate_style (asp APPR)); 
   ("bg", background_check); 
   ("split", split_phrase);
   ("split_appr", lseq split_phrase (asp APPR));
   ("parmut", parallel_mutual_1); 
   ("layered_bg", layered_background_check); 
   ("filehash", filehash_auth_phrase);
   ("large_output", large_output_asp_test);
   ("cds_simple", example_appTerm);
   ("cds_ssl", cds_ssl);
   ("cds_local", cds_local);
   ("cds_tpm", cds_tpm);
   ("cds_provision", example_appTerm_provision);
   ("simple_sig", simple_sig);
   ("micro", micro_appTerm);
   ("micro_provision", micro_appTerm_provision);
   ("micro_provision_dir_1", micro_appTerm_provision_dir_1);
   ("micro_provision_dir_2", micro_appTerm_provision_dir_2);
   ("micro_provision_composite", micro_appTerm_provision_composite)
    ].
   

Definition add_EvidenceT_flexible_mechanisms := 
  fun G =>
  Maps.map_map (fun t => (t, eval G P0 (nonce_evt 0) t)) flexible_mechanisms_map.

Definition full_flexible_mechanisms :=
  add_EvidenceT_flexible_mechanisms.
Close Scope string_scope.

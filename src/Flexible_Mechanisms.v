Require Import Term_Defs Flexible_Mechanisms_Vars CACL_Demo.
Require Import List String. 
Import ListNotations.

(* Flexible Mechanisms *)
Definition certificate_style : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest_id [] P1 sys_targ)))
      (att P2 (
        lseq 
          (asp (ASPC (asp_paramsC appraise_id [] P2 sys_targ)))
          (asp (ASPC (asp_paramsC certificate_id [] P2 sys_targ)))
      ))
  ).

Definition background_check : Term :=
  lseq
    (att P1 (asp (ASPC (asp_paramsC attest_id [] P1 sys_targ))))
    (att P2 (asp (ASPC (asp_paramsC appraise_id [] P2 sys_targ)))).

Definition parallel_mutual_1 : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest_id [] P1 sys_targ)))
      (att P2 (asp (ASPC (asp_paramsC appraise_id [] P2 sys_targ))))
  ).

Definition parallel_mutual_2 : Term :=
  att P0 (
    lseq 
      (asp (ASPC (asp_paramsC attest_id [] P0 sys_targ)))
      (att P2 (asp (ASPC (asp_paramsC appraise_id [] P2 sys_targ))))
  ).

Definition layered_background_check : Term :=
  att P1
    (bpar (ALL, ALL)
      (lseq
        (att P1 (asp (ASPC (asp_paramsC attest_id [] P1 sys_targ))))
        (lseq 
          (asp (ASPC (asp_paramsC attest_id [] P3 att_targ)))
          (asp (ASPC (asp_paramsC attest_id [] P4 att_targ)))
        )
      )
      (bpar (ALL, ALL)
        (att P3 (asp (ASPC (asp_paramsC attest_id [] P3 sys_targ))))
        (lseq
          (att P4 (asp (ASPC (asp_paramsC attest_id [] P4 sys_targ))))
          (att P2 (
            (lseq
              (asp (ASPC (asp_paramsC appraise_id [] P2 it_targ)))
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
      (asp (ASPC (asp_paramsC hashfile_id [] P1 hashfile_targ)))
      (asp SIG) 
    ).

Definition split_phrase : Term :=
  att P1 ( 
    bseq (ALL, ALL)
      (asp (ASPC (asp_paramsC attest1_id [] P1 sys_targ)))
      (asp (ASPC (asp_paramsC attest2_id [] P1 sys_targ)))
    ).

Definition large_output_asp_test : Term :=
  asp (ASPC (asp_paramsC large_output_id [] P1 sys_targ)).

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
  (asp (ASPC (asp_paramsC attest2_id [] P1 sys_targ))).
*)

Definition meas_cds : Term := 
<{
  (gather_config_1 +<+ 
  gather_config_2 (* +<+
  gather_config_3 *) )
}>.

Definition hash_micro_config_1 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_1_targ 
    path_micro_targ1 path_micro_targ1_golden).

Definition hash_micro_config_2 : Term := 
    (hash_targ_asp cds_config_dir_plc cds_img_2_targ 
    path_micro_targ2 path_micro_targ2_golden).


Definition hash_micro_evidence : Term := 
  (hash_evidence_asp cds_config_dir_plc cds_img_3_targ 
    path_micro_composite_golden).

Definition meas_micro : Term := 
<{
  (hash_micro_config_1 +<+ 
   hash_micro_config_2) -> 
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
    (meas_cds +<+ 
     query_kim_asp) ->
    r_ssl_sig_asp ->
    appr_term
}>. 

Definition cds_tpm : Term :=
<{
    (meas_cds +<+ 
     query_kim_asp) ->
    r_tpm_sig_asp ->
    appr_term
}>. 

(*
Definition example_appTerm_stub : Term :=
<{
    (gather_config_1 +<+
     query_kim_asp_stub ) ->
     r_ssl_sig_asp ->
    appr_term
}>.
*)

Definition provision_micro_hash_1 : Term := 
    (provision_targ_asp cds_config_dir_plc cds_config_1_targ path_micro_targ1_golden).

Definition provision_micro_hash_2 : Term := 
    (provision_targ_asp cds_config_dir_plc cds_config_1_targ path_micro_targ2_golden).

Definition provision_micro_hash_composite : Term := 
      (provision_targ_asp cds_config_dir_plc cds_config_1_targ    path_micro_composite_golden).

Definition micro_appTerm_provision : Term :=
  <{
    (hash_micro_config_1 -> provision_micro_hash_1) +<+ 
    (hash_micro_config_2 -> provision_micro_hash_2) +<+ 
    (meas_micro -> provision_micro_hash_composite)
  }>.

Definition example_appTerm_provision : Term :=
<{
    (gather_config_1 -> provision_config_1) +<+
    (gather_config_2 -> provision_config_2)
}>.

Definition simple_sig : Term := 
lseq 
(
  lseq
(asp (ASPC (asp_paramsC attest_id [] P1 sys_targ)))
r_ssl_sig_asp) 
appr_term.




Close Scope cop_ent_scope.


Open Scope string_scope.
Definition flexible_mechanisms_map := 
  [("cert", certificate_style); 
   ("cert_appr", lseq certificate_style (asp APPR)); 
   ("bg", background_check); 
   ("split", split_phrase);
   ("split_appr", lseq split_phrase (asp APPR));
   ("parmut", parallel_mutual_1); 
   ("parmut2", parallel_mutual_2); 
   ("layered_bg", layered_background_check); 
   ("filehash", filehash_auth_phrase);
   ("large_output", large_output_asp_test);
   ("cds_simple", example_appTerm);
   (*
   ("cds_stub", example_appTerm_stub); *)
   ("cds_ssl", cds_ssl);
   ("cds_tpm", cds_tpm);
   ("cds_provision", example_appTerm_provision);
   ("simple_sig", simple_sig);
   ("micro", micro_appTerm);
   ("micro_provision", micro_appTerm_provision)
   
   (* ;
   ("cds", cds_demo_phrase);
   ("cds_appr", lseq cds_demo_phrase (asp APPR)) *) ].
   

Definition add_EvidenceT_flexible_mechanisms := 
  fun G =>
  Maps.map_map (fun t => (t, eval G P0 (nonce_evt 0) t)) flexible_mechanisms_map.

Definition full_flexible_mechanisms :=
  add_EvidenceT_flexible_mechanisms.
Close Scope string_scope.

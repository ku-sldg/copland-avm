Require Import Term_Defs Flexible_Mechanisms_Vars JSON_Type CACL_Demo.
Require Import List String.

Import ListNotations.

Open Scope string_scope.

Definition micro_args_model : ASP_ARGS := 
  (JSON_Object [("filepath_golden", (JSON_String "/am-cakeml/tests/DemoFiles/goldenFiles/aadl_composite.txt")); 

  ("paths", JSON_Array [(JSON_String "/INSPECTA-models/micro-examples/microkit/aadl_port_types/data/base_type/aadl/")]);
  ("env_var", JSON_String "DEMO_ROOT")
  ]).

Definition micro_args_system : ASP_ARGS := 
    (JSON_Object [("filepath_golden", (JSON_String "/am-cakeml/tests/DemoFiles/goldenFiles/microkit_composite.txt")); 
  
    ("paths", JSON_Array [(JSON_String "/INSPECTA-models/micro-examples/microkit/aadl_port_types/data/base_type/hamr/microkit/")]);
    ("env_var", JSON_String "DEMO_ROOT")
    ]).

  Definition micro_args_composite : ASP_ARGS := 
    (JSON_Object [("filepath_golden", (JSON_String "/am-cakeml/tests/DemoFiles/goldenFiles/micro_composite.txt")); 

    ("paths", JSON_Array []);
    ("env_var", JSON_String "DEMO_ROOT")
    ]).

Definition micro_args_union : ASP_ARGS := 
  (JSON_Object [("filepath_golden", (JSON_String "/am-cakeml/tests/DemoFiles/goldenFiles/micro_union_composite.txt")); 

  ("paths", JSON_Array [
    (JSON_String "/INSPECTA-models/micro-examples/microkit/aadl_port_types/data/base_type/aadl/");
    (JSON_String "/INSPECTA-models/micro-examples/microkit/aadl_port_types/data/base_type/hamr/microkit/")]
  );
  ("env_var", JSON_String "DEMO_ROOT")
  ]).

    (*
Definition micro_args_system : ASP_ARGS := 
  (JSON_Object [("filepath_golden", (JSON_String "/am-cakeml/tests/DemoFiles/goldenFiles/microkit_composite.txt"))]).
  *)

Close Scope string_scope.

(* Flexible Mechanisms *)
Definition certificate_style : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest_id (micro_args_system) P1 sys_targ)))
      (att P2 (
        lseq 
          (asp (ASPC (asp_paramsC appraise_id (micro_args_system) P2 sys_targ)))
          (asp (ASPC (asp_paramsC certificate_id (micro_args_system) P2 sys_targ)))
      ))
  ).

Definition background_check : Term :=
  lseq
    (att P1 (asp (ASPC (asp_paramsC attest_id (micro_args_system) P1 sys_targ))))
    (att P2 (asp (ASPC (asp_paramsC appraise_id (micro_args_system) P2 sys_targ)))).

Definition parallel_mutual_1 : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest_id (micro_args_system) P1 sys_targ)))
      (att P2 (asp (ASPC (asp_paramsC appraise_id (micro_args_system) P2 sys_targ))))
  ).

Definition parallel_mutual_2 : Term :=
  att P0 (
    lseq 
      (asp (ASPC (asp_paramsC attest_id (micro_args_system) P0 sys_targ)))
      (att P2 (asp (ASPC (asp_paramsC appraise_id (micro_args_system) P2 sys_targ))))
  ).

Definition layered_background_check : Term :=
  att P1
    (bpar (ALL, ALL)
      (lseq
        (att P1 (asp (ASPC (asp_paramsC attest_id (micro_args_system) P1 sys_targ))))
        (lseq 
          (asp (ASPC (asp_paramsC attest_id (micro_args_system) P3 att_targ)))
          (asp (ASPC (asp_paramsC attest_id (micro_args_system) P4 att_targ)))
        )
      )
      (bpar (ALL, ALL)
        (att P3 (asp (ASPC (asp_paramsC attest_id (micro_args_system) P3 sys_targ))))
        (lseq
          (att P4 (asp (ASPC (asp_paramsC attest_id (micro_args_system) P4 sys_targ))))
          (att P2 (
            (lseq
              (asp (ASPC (asp_paramsC appraise_id (micro_args_system) P2 it_targ)))
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
      (asp (ASPC (asp_paramsC hashfile_id (micro_args_system) P1 hashfile_targ)))
      (asp SIG) 
    ).

Definition split_phrase : Term :=
  att P1 ( 
    bseq (ALL, ALL)
      (asp (ASPC (asp_paramsC attest1_id (micro_args_system) P1 sys_targ)))
      (asp (ASPC (asp_paramsC attest2_id (micro_args_system) P1 sys_targ)))
    ).


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

Definition hash_micro_config_1 (args:ASP_ARGS) : Term := 
    (hash_dir_asp cds_config_dir_plc cds_img_1_targ 
      args).

    (*
    path_micro_targ1 path_micro_targ1_golden). *)

Definition hash_micro_config_2 (args:ASP_ARGS) : Term := 
    (hash_dir_asp cds_config_dir_plc cds_img_2_targ 
      args).

    (*
    path_micro_targ2 path_micro_targ2_golden). *)


Definition hash_micro_evidence : Term := 
  (hash_evidence_asp cds_config_dir_plc cds_img_3_targ 
    path_micro_composite_golden).

Definition meas_micro (model_args:ASP_ARGS) (system_args:ASP_ARGS) : Term := 
  lseq 
    (
      (* bseq (ALL,ALL) *)
      (hash_micro_config_1 model_args)
      (*
      (hash_micro_config_2 system_args)
      *)
    )
    hash_micro_evidence.

(*
<{
  ((hash_micro_config_1 model_args) +<+ 
   (hash_micro_config_2 system_args)) -> 
   hash_micro_evidence
}>.
*)

Definition micro_appTerm : Term := 
  lseq
    (meas_micro (micro_args_system) (micro_args_system))
    appr_term.

(*
Definition micro_appTerm : Term :=
<{
    ( meas_micro ) ->
    appr_term
}>.
*)

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

Definition provision_micro_hash_1 (args:ASP_ARGS) : Term := 
    (provision_dir_asp cds_config_dir_plc cds_config_1_targ 
      args).
    (* 
    path_micro_targ1_golden). *)

Definition provision_micro_hash_2 (args:ASP_ARGS) : Term := 
    (provision_dir_asp cds_config_dir_plc cds_config_1_targ 
      args).
    (*
    path_micro_targ2_golden). *)



Definition provision_micro_hash_composite : Term := 
      (provision_dir_asp cds_config_dir_plc cds_config_1_targ  
      (*
      [("filepath-golden",  path_micro_composite_golden)]
      *)
      (micro_args_composite)
      ).

Definition micro_appTerm_provision (model_args:ASP_ARGS) (system_args:ASP_ARGS) : Term :=

bseq (ALL,ALL)
  (lseq 
    (hash_micro_config_1 micro_args_union)
    (provision_micro_hash_1 micro_args_union))

    (lseq 
    (meas_micro micro_args_union system_args)
    (provision_micro_hash_composite)).


(*
Definition micro_appTerm_provision (model_args:ASP_ARGS) (system_args:ASP_ARGS) : Term :=

  bseq (ALL,ALL)
    (lseq 
      (hash_micro_config_1 model_args)
      (provision_micro_hash_1 model_args))
    (bseq (ALL,ALL)
      (lseq 
      (hash_micro_config_2 system_args)
      (provision_micro_hash_1 system_args))

      (lseq 
      (meas_micro model_args system_args)
      (provision_micro_hash_composite))
    ).
  *)



    (*
  <{
    (hash_micro_config_1 -> provision_micro_hash_1) +<+ 
    (hash_micro_config_2 -> provision_micro_hash_2) +<+ 
    (meas_micro -> provision_micro_hash_composite)
  }>.
  *)

(*
Definition micro_appTerm_provision : Term :=
  <{
    (hash_micro_config_1 -> provision_micro_hash_1) +<+ 
    (hash_micro_config_2 -> provision_micro_hash_2) +<+ 
    (meas_micro -> provision_micro_hash_composite)
  }>.
*)

Definition example_appTerm_provision : Term :=
<{
    (gather_config_1 -> provision_config_1) +<+
    (gather_config_2 -> provision_config_2)
}>.

Definition simple_sig : Term := 
lseq 
(
  lseq
(asp (ASPC (asp_paramsC attest_id (micro_args_system) P1 sys_targ)))
r_ssl_sig_asp) 
appr_term.

Definition cert_resolute_phrase : Term := 
  (* att P1  *)
      (asp (ASPC (asp_paramsC certificate_id (micro_args_system) P1 cert_resolute_targ))).

Close Scope cop_ent_scope.


Definition large_output_asp_test : Term :=
  asp (ASPC (asp_paramsC large_output_id (micro_args_system) P1 sys_targ)).



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
   ("cds_simple", example_appTerm);
   ("cds_provision", example_appTerm_provision);
   (*
   ("cert_resolute_app", lseq cert_resolute_phrase (asp APPR));
   *)
   ("cds_ssl", cds_ssl);
   ("cds_tpm", cds_tpm);
   ("cds_provision", example_appTerm_provision);
   ("simple_sig", simple_sig);
   ("micro", (lseq (micro_appTerm_provision micro_args_model  micro_args_system) (asp APPR)) );
   ("micro_provision", (micro_appTerm_provision micro_args_model micro_args_system));
   (*
   ("cert_resolute_app", lseq cert_resolute_phrase (asp APPR));
   *)
   
   (* ;
   ("cds", cds_demo_phrase);
   ("cds_appr", lseq cds_demo_phrase (asp APPR))  ]. *)
   
   ("large_output", large_output_asp_test)].

Definition add_EvidenceT_flexible_mechanisms := 
  fun G =>
  Maps.map_map (fun t => (t, eval G P0 (nonce_evt 0) t)) flexible_mechanisms_map.

Definition full_flexible_mechanisms :=
  add_EvidenceT_flexible_mechanisms.
Close Scope string_scope.

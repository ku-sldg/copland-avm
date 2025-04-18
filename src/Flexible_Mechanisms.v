Require Import Term_Defs Flexible_Mechanisms_Vars JSON_Type.

Require Import Demo_Terms CDS_Demo Resolute_Demo.
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

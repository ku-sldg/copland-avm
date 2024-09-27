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

Open Scope string_scope.
Definition flexible_mechanisms_map := 
  [("cert", certificate_style); 
   ("cert_appr", lseq certificate_style (asp APPR)); 
   ("bg", background_check); 
   ("parmut", parallel_mutual_1); 
   ("parmut2", parallel_mutual_2); 
   ("layered_bg", layered_background_check); 
   ("filehash", filehash_auth_phrase);
   ("cds", cds_demo_phrase);
   ("cds_appr", lseq cds_demo_phrase (asp APPR))].

Definition add_EvidenceT_flexible_mechanisms := 
  fun G =>
  Maps.map_map (fun t => (t, eval G P0 (nonce_evt 0) t)) flexible_mechanisms_map.

Definition full_flexible_mechanisms :=
  add_EvidenceT_flexible_mechanisms.
Close Scope string_scope.

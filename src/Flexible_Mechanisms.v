Require Import Term_Defs Flexible_Mechanisms_Vars.
Require Import List String. 
Import ListNotations.

(* Flexible Mechanisms *)
Definition certificate_style : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest_id [])))
      (att P2 (
        lseq 
          (asp (ASPC (asp_paramsC appraise_id [])))
          (asp (ASPC (asp_paramsC certificate_id [])))
      ))
  ).

Definition background_check : Term :=
  lseq
    (att P1 (asp (ASPC (asp_paramsC attest_id []))))
    (att P2 (asp (ASPC (asp_paramsC appraise_id [])))).

Definition parallel_mutual_1 : Term :=
  att P1 (
    lseq 
      (asp (ASPC (asp_paramsC attest_id [])))
      (att P2 (asp (ASPC (asp_paramsC appraise_id []))))
  ).

Definition parallel_mutual_2 : Term :=
  att P0 (
    lseq 
      (asp (ASPC (asp_paramsC attest_id [])))
      (att P2 (asp (ASPC (asp_paramsC appraise_id []))))
  ).

Definition layered_background_check : Term :=
  att P1
    (bpar (ALL, ALL)
      (lseq
        (att P1 (asp (ASPC (asp_paramsC attest_id []))))
        (lseq 
          (asp (ASPC (asp_paramsC attest_id [])))
          (asp (ASPC (asp_paramsC attest_id [])))
        )
      )
      (bpar (ALL, ALL)
        (att P3 (asp (ASPC (asp_paramsC attest_id []))))
        (lseq
          (att P4 (asp (ASPC (asp_paramsC attest_id []))))
          (att P2 (
            (lseq
              (asp (ASPC (asp_paramsC appraise_id [])))
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
      (asp (ASPC (asp_paramsC hashfile_id [])))
      (asp SIG) 
    ).

Definition split_phrase : Term :=
  att P1 ( 
    bseq (ALL, ALL)
      (asp (ASPC (asp_paramsC attest1_id [])))
      (asp (ASPC (asp_paramsC attest2_id [])))
    ).

Definition large_output_asp_test : Term :=
  asp (ASPC (asp_paramsC large_output_id [])).

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
   ("large_output", large_output_asp_test)].

Definition add_EvidenceT_flexible_mechanisms := 
  fun G =>
  Maps.map_map (fun t => (t, eval G P0 (nonce_evt 0) t)) flexible_mechanisms_map.

Definition full_flexible_mechanisms :=
  add_EvidenceT_flexible_mechanisms.
Close Scope string_scope.

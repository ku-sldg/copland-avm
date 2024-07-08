Require Import Term_Defs Flexible_Mechanisms_Vars.
Require Import List. 
Import ListNotations.

(* Flexible Mechanisms *)
Definition certificate_style : Term :=
  att P1 (
    lseq 
      (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P1 sys_targ)))
      (att P2 (
        lseq 
          (asp (ASPC ALL (EXTD 1) (asp_paramsC appraise_id [] P2 sys_targ)))
          (asp (ASPC ALL (EXTD 1) (asp_paramsC certificate_id [] P2 sys_targ)))
      ))
  ).

Definition background_check : Term :=
  lseq
    (att P1 (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P1 sys_targ))))
    (att P2 (asp (ASPC ALL (EXTD 1) (asp_paramsC appraise_id [] P2 sys_targ)))).

Definition parallel_mutual_1 : Term :=
  att P1 (
    lseq 
      (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P1 sys_targ)))
      (att P2 (asp (ASPC ALL (EXTD 1) (asp_paramsC appraise_id [] P2 sys_targ))))
  ).

Definition parallel_mutual_2 : Term :=
  att P0 (
    lseq 
      (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P0 sys_targ)))
      (att P2 (asp (ASPC ALL (EXTD 1) (asp_paramsC appraise_id [] P2 sys_targ))))
  ).

Definition layered_background_check : Term :=
  att P1
    (bpar (ALL, ALL)
      (lseq
        (att P1 (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P1 sys_targ))))
        (lseq 
          (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P3 att_targ)))
          (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P4 att_targ)))
        )
      )
      (bpar (ALL, ALL)
        (att P3 (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P3 sys_targ))))
        (lseq
          (att P4 (asp (ASPC ALL (EXTD 1) (asp_paramsC attest_id [] P4 sys_targ))))
          (att P2 (
            (lseq
              (asp (ASPC ALL (EXTD 1) (asp_paramsC appraise_id [] P2 it_targ)))
              (asp (ASPC ALL (EXTD 1) sig_params))
            )
          )
          )
        )
      )
    ).

Definition flexible_mechanisms := [certificate_style; background_check; parallel_mutual_1; parallel_mutual_2; layered_background_check].

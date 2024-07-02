Require Import Term_Defs.
Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Plcs *)
Definition P0 : Plc := "P0".
Definition P1 : Plc := "P1".
Definition P2 : Plc := "P2".
Definition P3 : Plc := "P3".
Definition P4 : Plc := "P4".

(* ASP IDs *)
Definition attest_id : ASP_ID := "attest_id".
Definition appraise_id : ASP_ID := "appraise_id".
Definition certificate_id : ASP_ID := "certificate_id".

(* TARG IDs *)
Definition sys_targ : TARG_ID := "sys_targ".
Definition att_targ : TARG_ID := "att_targ".
Definition it_targ : TARG_ID := "it_targ".


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

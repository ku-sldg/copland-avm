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
Definition attest1_id : ASP_ID := "attest1_id".
Definition attest2_id : ASP_ID := "attest2_id".
Definition appraise_id : ASP_ID := "appraise_id".
Definition certificate_id : ASP_ID := "certificate_id".
Definition hashfile_id : ASP_ID := "hashfile_id".
Definition large_output_id : ASP_ID := "large_output_id".

(* TARG IDs *)
Definition sys_targ : TARG_ID := "sys_targ".
Definition att_targ : TARG_ID := "att_targ".
Definition it_targ : TARG_ID := "it_targ".
Definition hashfile_targ : TARG_ID := "hashfile_targ".

Close Scope string_scope.
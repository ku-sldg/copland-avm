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
Definition attest : ASP_ID := "attest".
Definition appraise : ASP_ID := "appraise".
Definition certificate : ASP_ID := "certificate".
Definition hashfile : ASP_ID := "hashfile".
Definition large_output : ASP_ID := "large_output".

(* TARG IDs *)
Definition sys_targ : TARG_ID := "sys_targ".

Close Scope string_scope.
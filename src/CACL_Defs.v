Require Import Maps ID_Type.

Require Import List.
Import ListNotations.


Inductive CACL_Permission := 
| CACL_Read    : CACL_Permission 
| CACL_Write   : CACL_Permission
| CACL_Invoke  : CACL_Permission.

Definition CACL_Access : Type := (ID_Type * CACL_Permission).
Definition CACL_Policy : Type := Map ID_Type (list CACL_Access).
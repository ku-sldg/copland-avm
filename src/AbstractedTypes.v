(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)

Require Import EqClass.

(* Abstract type reserved for Identifiers *)
Definition ID_Type : Set. Admitted.

(* Assumed equality for identifiers *)
Global Instance Eq_Class_ID_Type : EqClass ID_Type. Admitted.

(* Default Identifier value *)
Definition min_id_type : ID_Type. Admitted.
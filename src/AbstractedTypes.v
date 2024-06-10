(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)

Require Import EqClass String.

(* Abstract type reserved for Identifiers *)
Definition ID_Type : Set. Admitted.

Definition ID_Type_to_string (id:ID_Type) : string. Admitted.
Definition string_to_ID_Type (s:string) : option ID_Type. Admitted.

(* Assumed equality for identifiers *)
Global Instance Eq_Class_ID_Type : EqClass ID_Type. Admitted.

(* Default Identifier value *)
Definition min_id_type : ID_Type. Admitted.
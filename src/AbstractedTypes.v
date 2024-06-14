(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)

Require Export ResultT EqClass StringT.

(* Abstract type reserved for Identifiers *)
Definition ID_Type : Set. Admitted.

Definition ID_Type_to_stringT (id:ID_Type) : StringT. Admitted.
Definition stringT_to_ID_Type (s:StringT) : ResultT ID_Type StringT. Admitted.

(* Assumed equality for identifiers *)
Global Instance Eq_Class_ID_Type : EqClass ID_Type. Admitted.

(* Default Identifier value *)
Definition min_id_type : ID_Type. Admitted.
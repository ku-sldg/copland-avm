(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)

Require Export ResultT EqClass StringT.

(* Abstract type reserved for Identifiers *)
Definition ID_Type : Set. Admitted.

Definition ID_Type_to_stringT (id:ID_Type) : StringT. Admitted.
Definition stringT_to_ID_Type (s:StringT) : ResultT ID_Type StringT. Admitted.

Axiom canonical_string_id_type : forall (s : StringT) (i : ID_Type),
  ID_Type_to_stringT i = s <-> (stringT_to_ID_Type s = resultC i).

(* Assumed equality for identifiers *)
Global Instance Eq_Class_ID_Type : EqClass ID_Type. Admitted.

(* Default Identifier value *)
Definition min_id_type : ID_Type. Admitted.
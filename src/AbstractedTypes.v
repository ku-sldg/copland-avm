(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)

Require Export Serializable EqClass.

(* Abstract type reserved for Identifiers *)
Definition ID_Type : Set. Admitted.

(* Serializable Class for ID_Type *)
Global Instance Serializable_ID_Type : Serializable ID_Type. Admitted.

Axiom canonical_string_id_type : forall (s : string) (i : ID_Type),
  to_string i = s <-> (from_string s = resultC i).

(* Assumed equality for identifiers *)
Global Instance Eq_Class_ID_Type : EqClass ID_Type. Admitted.

(* Default Identifier value *)
Definition min_id_type : ID_Type. Admitted.
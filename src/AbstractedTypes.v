(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)

Require Export ResultT EqClass.
Require Import String.

(* Abstract type reserved for Identifiers *)
Definition ID_Type : Set. Admitted.

Definition ID_Type_to_string (id:ID_Type) : string. Admitted.
Definition string_to_ID_Type (s:string) : ResultT ID_Type string. Admitted.

Axiom canonical_string_id_type : forall (s : string) (i : ID_Type),
  ID_Type_to_string i = s <-> (string_to_ID_Type s = resultC i).

(* Assumed equality for identifiers *)
Global Instance Eq_Class_ID_Type : EqClass ID_Type. Admitted.

(* Default Identifier value *)
Definition min_id_type : ID_Type. Admitted.
(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)

Require Export Serializable EqClass.

(* Abstract type reserved for Identifiers *)
Definition ID_Type : Set := string.

(* Serializable Class for ID_Type *)
Global Instance Serializable_ID_Type : Serializable ID_Type := {
  to_string := to_string;
  from_string := from_string
}.

Global Instance Eq_Class_ID_Type : EqClass ID_Type := {
  eqb := eqb;
  eqb_eq := eqb_eq
}.

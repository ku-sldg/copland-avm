(* Abstract (Admitted) definition of a general type for 
    Identifiers and associated abstract values/operations *)

Require Export Stringifiable EqClass.

(* Abstract type reserved for Identifiers *)
Definition ID_Type : Set := string.

(* Stringifiable Class for ID_Type *)
Global Instance Stringifiable_ID_Type : Stringifiable ID_Type := {
  to_string := to_string;
  from_string := from_string;
  canonical_stringification := canonical_stringification
}.

Global Instance Eq_Class_ID_Type : EqClass ID_Type := {
  eqb := eqb;
  eqb_eq := eqb_eq
}.

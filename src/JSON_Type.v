Require Import String Maps.

Inductive JSON : Type :=
| JSON_Object : MapC string JSON -> JSON
| JSON_Array : list JSON -> JSON
| JSON_String : string -> JSON
| JSON_Boolean : bool -> JSON
| JSON_Null : JSON.

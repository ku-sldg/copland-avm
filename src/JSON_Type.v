Require Import StringT Maps.

Inductive JSON : Type :=
| JSON_Object : MapC StringT JSON -> JSON
| JSON_Array : list JSON -> JSON
| JSON_String : StringT -> JSON
| JSON_Boolean : bool -> JSON
| JSON_Null : JSON.

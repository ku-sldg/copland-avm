Require Import StringT Maps.

Inductive JSON : Type :=
| JSON__Object : MapC StringT JSON -> JSON
| JSON__Array : list JSON -> JSON
| JSON__String : StringT -> JSON
| JSON__Boolean : bool -> JSON
| JSON__Null : JSON.

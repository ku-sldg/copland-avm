Require Import String Maps.


Inductive JSON :=
| JSON_Object     : MapC string JSON -> JSON
| JSON_Array    : list JSON -> JSON
| JSON_String   : string -> JSON
| JSON_Boolean  : bool -> JSON.


(*
Inductive JSON :=
| JSON_Object     : MapC string InnerJSON -> JSON

with InnerJSON :=
| InJSON_Object   : JSON -> InnerJSON
| InJSON_Array    : list InnerJSON -> InnerJSON
| InJSON_String   : string -> InnerJSON
| InJSON_Boolean  : bool -> InnerJSON.

*)

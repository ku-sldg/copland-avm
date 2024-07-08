Require Import String Maps.

Inductive JSON :=
| JSON_Object     : MapC string InnerJSON -> JSON

with InnerJSON :=
| InJSON_Object   : JSON -> InnerJSON
| InJSON_Array    : list InnerJSON -> InnerJSON
| InJSON_String   : string -> InnerJSON
| InJSON_Boolean  : bool -> InnerJSON.

Require Import JSON_Type String ResultT.

Definition JSON_to_string (js : JSON) : string. Admitted.

Definition string_to_JSON (s : string) : ResultT JSON string. Admitted.

Axiom canonical_serialization_json_string : forall (s : string) (js : JSON),
  JSON_String s = js <-> (JSON_to_string js = s).

Definition JSON_get_JSON (key : string) (js : JSON) : ResultT JSON string. Admitted.

Definition JSON_get_string (key : string) (js : JSON) : ResultT string string. Admitted.

Definition JSON_get_bool (key : string) (js : JSON) : ResultT bool string. Admitted.


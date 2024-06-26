Require Import JSON_Type String ResultT.

Definition JSON_to_string (js : JSON) : string. Admitted.

Definition string_to_JSON (s : string) : ResultT JSON string. Admitted.

Axiom canonical_serialization_json_string : forall (s : string) (js : JSON),
  (string_to_JSON s) = resultC js <-> (JSON_to_string js = s).

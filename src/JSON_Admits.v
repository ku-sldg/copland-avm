Require Import JSON_Type StringT ResultT.

Definition JSON_to_stringT (js : JSON) : StringT. Admitted.

Definition stringT_to_JSON (s : StringT) : ResultT JSON StringT. Admitted.

Definition JSON_get_JSON (key : StringT) (js : JSON) : ResultT JSON StringT. Admitted.

Definition JSON_get_stringT (key : StringT) (js : JSON) : ResultT StringT StringT. Admitted.

Definition JSON_get_bool (key : StringT) (js : JSON) : ResultT bool StringT. Admitted.


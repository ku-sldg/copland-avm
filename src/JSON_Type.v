Require Import String Maps.

Require Import List.


Inductive JSON :=
| JSON_Object   : MapC string JSON -> JSON
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

Definition sum_js_array (ls:list JSON) (f:JSON -> nat) : nat := 
    fold_right (fun js acc => (acc + (f js))) 0 ls.

Definition sum_js_object (m:MapC string JSON) (f:JSON -> nat) : nat := 
    fold_right (fun pr acc => (acc + (f (snd pr)))) 0 m.

Fixpoint JSON_depth (js:JSON) : nat := 
    match js with
    | JSON_Boolean _ => 1 
    | JSON_String _ => 1 
    | JSON_Array ls => 1 + (sum_js_array ls JSON_depth)
    | JSON_Object m => 1 + (sum_js_object m JSON_depth)
    end.
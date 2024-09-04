Require Import String Maps.

Require Import List.


Inductive JSON :=
| JSON_Object   : Map string JSON -> JSON
| JSON_Array    : list JSON -> JSON
| JSON_String   : string -> JSON
| JSON_Boolean  : bool -> JSON.


(*
Inductive JSON :=
| JSON_Object     : Map string InnerJSON -> JSON

with InnerJSON :=
| InJSON_Object   : JSON -> InnerJSON
| InJSON_Array    : list InnerJSON -> InnerJSON
| InJSON_String   : string -> InnerJSON
| InJSON_Boolean  : bool -> InnerJSON.

*)

Definition depth_js_array (ls:list JSON) (f:JSON -> nat) : nat := 
    fold_right (fun js acc => max acc (f js)) 0 ls.

Definition depth_js_map (m: Map string JSON) (f:JSON -> nat) : nat := 
    fold_right (fun pr acc => max acc (f (snd pr))) 0 m.

Fixpoint JSON_depth (js:JSON) : nat := 
    match js with
    | JSON_Boolean _ => 1 
    | JSON_String _ => 1 
    | JSON_Array ls => 1 + depth_js_array ls JSON_depth
    | JSON_Object m => 1 + depth_js_map m JSON_depth
    end.
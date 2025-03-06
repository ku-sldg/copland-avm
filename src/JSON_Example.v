(* THIS FILE DOES NOT WORK AND IS CURRENTLY BEING PUSHED FOR VERSION CONTROL PURPOSES ONLY *)
(* Defines a simple example of JSON in Coq *)

Require Import List String Maps Stringifiable EqClass ErrorStringConstants.
Require Export JSON_Type JSON_Admits ResultT StructTactics.
Import ListNotations.
Import ResultNotation.


Definition JSON_example {A B : Type} : bool. Admitted.
Definition JSON_decoded : JSON := str_pair_to_JSON JSON_example.
Definition JSON_reencoded {A B : Type} : ResultT (A * B) string := str_pair_from_JSON JSON_decoded.
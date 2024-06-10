(* Abstract type for strings.  Literal string representations (i.e. ASCII) 
    in Coq were deemed too heavyweight for this development. *)
Require Import String.

Definition StringT : Set.
Admitted. 

Definition StringT_to_string (s:StringT): string. Admitted.

Definition string_to_StringT (s:string): StringT. Admitted.
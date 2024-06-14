(* Abstract type for strings.  Literal string representations (i.e. ASCII) 
    in Coq were deemed too heavyweight for this development. *)
Require Import String EqClass.

Definition StringT : Set.
Admitted. 

Definition StringT_to_string (s:StringT): string. Admitted.

Definition string_to_StringT (s:string): StringT. Admitted.

Global Instance EqClass_StringT : EqClass StringT. Admitted.
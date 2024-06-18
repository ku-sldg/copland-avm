(* Defining (abstract) representation for raw binary data values.
   BS stands for "Binary String".  May be instantiated with 
   types like strings and byte buffers in concrete implementations.    *)

Require Import StringT ResultT. 

Definition BS : Set. Admitted.

Definition BS_to_stringT (bs:BS) : StringT. Admitted.
Definition stringT_to_BS (s: StringT) : ResultT BS StringT. Admitted.

(* Some default/reserved BS values *)
Definition default_bs : BS. Admitted.
Definition passed_bs  : BS. Admitted.
Definition failed_bs  : BS. Admitted.

(* Defining (abstract) representation for raw binary data values.
   BS stands for "Binary String".  May be instantiated with 
   types like strings and byte buffers in concrete implementations.    *)

Require Import ResultT Stringifiable. 

Definition BS : Set. Admitted.

Global Instance Stringifiable_BS : Stringifiable BS. Admitted.

(* Some default/reserved BS values *)
Definition default_bs : BS. Admitted.
Definition passed_bs  : BS. Admitted.
Definition failed_bs  : BS. Admitted.

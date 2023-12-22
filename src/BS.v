(* Defining (abstract) representation for binary data values.
   BS stands for "Binary String".   *)

Definition BS := nat. (* : Set.
Admitted. *)

Definition default_bs : BS := O.
Definition passed_bs  : BS := O.
Definition failed_bs  : BS := S O.

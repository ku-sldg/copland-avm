Require Import (* EqClass *) Term_Defs_Core.

Require Import List.
Import ListNotations.


Definition ASP_Address := nat. (* : Set. Admitted. *)

Definition empty_ASP_Address : ASP_Address := O. (* Admitted. *)

Definition UUID := nat. (* : Type. Admitted. *)

(* We need this for making proofs and knowing that yes, in fact, UUID is an inhabited type *)
Definition default_uuid : UUID := O. (*  Admitted. *)

(*
Global Instance Eq_Class_uuid : EqClass UUID. Admitted.
*)

Definition PublicKey := nat. (* : Set. Admitted. *)

(* We need this for making proofs and knowing that yes, in fact, PubKey is an inhabited type *)
Definition default_PubKey := O. (* : PublicKey. Admitted. *)

(*
Global Instance Eq_Class_public_key : EqClass PublicKey. Admitted.
*)

Definition PrivateKey := nat. (* : Set. Admitted. *)

(*
Global Instance Eq_Class_private_key : EqClass PrivateKey. Admitted.
*)

Definition empty_Manifest_Plc : Plc := O.
(*Admitted. *)

(*  Admitted types, definitions, and typeclass instances related to Manifests *)

Require Import EqClass Term_Defs_Core Stringifiable.

Require Import List.
Import ListNotations.


Definition FS_Location : Set. Admitted.

Global Instance Stringifiable_FS_Location : Stringifiable FS_Location. Admitted.

Definition empty_FS_Location : FS_Location. Admitted.

Definition Concrete_ASP_ID : Set. Admitted.

Global Instance Stringifiable_Concrete_ASP_ID : Stringifiable Concrete_ASP_ID. Admitted.


Definition UUID : Type. Admitted.

Global Instance Stringifiable_UUID : Stringifiable UUID. Admitted.

(* We need this for making proofs and knowing that yes, in fact, UUID is an inhabited type *)
Definition default_uuid : UUID. Admitted.

Global Instance Eq_Class_uuid : EqClass UUID. Admitted.

Definition PublicKey : Set. Admitted.

Global Instance Stringifiable_PublicKey : Stringifiable PublicKey. Admitted.

(* We need this for making proofs and knowing that yes, in fact, PubKey is an inhabited type *)
Definition default_PubKey : PublicKey. Admitted.

Global Instance Eq_Class_public_key : EqClass PublicKey. Admitted.

Definition empty_Manifest_Plc : Plc.  Admitted.

(*  Admitted types, definitions, and typeclass instances related to Manifests *)

Require Import EqClass Term_Defs_Core Serializable.

Require Import List.
Import ListNotations.


Definition FS_Location : Set. Admitted.

Global Instance Serializable_FS_Location : Serializable FS_Location. Admitted.

Definition empty_FS_Location : FS_Location. Admitted.

Definition UUID : Type. Admitted.

Global Instance Serializable_UUID : Serializable UUID. Admitted.

(* We need this for making proofs and knowing that yes, in fact, UUID is an inhabited type *)
Definition default_uuid : UUID. Admitted.

Global Instance Eq_Class_uuid : EqClass UUID. Admitted.

Definition PublicKey : Set. Admitted.

Global Instance Serializable_PublicKey : Serializable PublicKey. Admitted.

(* We need this for making proofs and knowing that yes, in fact, PubKey is an inhabited type *)
Definition default_PubKey : PublicKey. Admitted.

Global Instance Eq_Class_public_key : EqClass PublicKey. Admitted.

Definition empty_Manifest_Plc : Plc.  Admitted.

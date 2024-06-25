(*  Admitted types, definitions, and typeclass instances related to Manifests *)

Require Import EqClass Term_Defs_Core JSON String.

Require Import List.
Import ListNotations.

(* ASP Locator JSON Admits *)
Definition JSON_Local_ASP : string. Admitted.
Definition JSON_Remote_ASP : string. Admitted.


Definition FS_Location : Set. Admitted.

Global Instance jsonifiable_FS_Location : Jsonifiable FS_Location. Admitted.

Definition empty_FS_Location : FS_Location. Admitted.

Definition UUID : Type. Admitted.

Definition string_to_uuid (s : string) : ResultT UUID string. Admitted.

Global Instance jsonifiable_uuid : Jsonifiable UUID. Admitted.

(* We need this for making proofs and knowing that yes, in fact, UUID is an inhabited type *)
Definition default_uuid : UUID. Admitted.

Global Instance Eq_Class_uuid : EqClass UUID. Admitted.

Definition PublicKey : Set. Admitted.

Global Instance jsonifiable_public_key : Jsonifiable PublicKey. Admitted.

(* We need this for making proofs and knowing that yes, in fact, PubKey is an inhabited type *)
Definition default_PubKey : PublicKey. Admitted.

Global Instance Eq_Class_public_key : EqClass PublicKey. Admitted.

Definition empty_Manifest_Plc : Plc.  Admitted.

Require Import StringT JSON.

(* The Pair JSONIFIABLE Class *)
Global Instance jsonifiable_pair (A B : Type) `{Jsonifiable A, Jsonifiable B} : Jsonifiable (A * B).
Admitted.

(* Manifest Admits *)
Definition MAN_ABS_PLC : StringT. Admitted.

Definition MAN_ASPS : StringT. Admitted.

Definition MAN_APPR_ASPS : StringT. Admitted.

Definition MAN_UUID_PLCS : StringT. Admitted.

Definition MAN_PUBKEY_PLCS : StringT. Admitted.

Definition MAN_TARGET_PLCS : StringT. Admitted.

Definition MAN_POLICY : StringT. Admitted.

(* AM Lib Admits *)
Definition AM_CLONE_UUID : StringT. Admitted.

Definition AM_LIB_ASPS : StringT. Admitted.

Definition AM_LIB_APPR_ASPS : StringT. Admitted.

Definition AM_LIB_PLCS : StringT. Admitted.

Definition AM_LIB_PUBKEYS : StringT. Admitted.

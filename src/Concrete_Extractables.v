Require Import Manifest JSON Manifest_JSON Attestation_Session Term_Defs JSON_Core.
Require Import List.
Import ListNotations.

(* This file contains things that we would like to be extracted
for usage in stub code, but we do not have any good place to plug
in outside of a list of extra stuff. *)

Definition concrete_Jsonifiable_Manifest : Jsonifiable Manifest :=
  Jsonifiable_Manifest.

Definition concrete_Jsonifiable_ASP_Compat_MapT : Jsonifiable ASP_Compat_MapT.
solve [typeclasses eauto].
Defined.

Definition concrete_Jsonifiable_Attestation_Session : Jsonifiable Attestation_Session.
solve [typeclasses eauto].
Defined.

Definition concrete_Jsonifiable_Term : Jsonifiable Term.
solve [typeclasses eauto].
Defined.

Definition concrete_Jsonifiable_Evidence : Jsonifiable Evidence.
solve [typeclasses eauto].
Defined.


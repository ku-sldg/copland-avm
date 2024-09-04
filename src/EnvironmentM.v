(* Definition of a Manifest Environment mapping (EnvironmentM).  *)

Require Import Term_Defs_Core Manifest Maps.

Require Import List.
Import ListNotations.

Definition EnvironmentM : Type := Map Plc Manifest.

Definition e_empty : EnvironmentM := [].
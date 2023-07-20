Require Import Term_Defs_Core Manifest Maps.

Require Import List.
Import ListNotations.

Definition EnvironmentM : Type := MapC Plc Manifest.

Definition e_empty : EnvironmentM := [].
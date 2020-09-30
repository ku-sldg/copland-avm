Require Import Maps Term.

(* An identifier represneting a system component.  This could be logically equivalent to the hash of the component *)
Definition Component := nat.

(* Maps each Component to a list of Components that contribute to its clean runtime context.  For example, a user-space component (target application, measurer, etc.) will almost always depend on an underlying OS kernel for a clean runtime context *)
Definition Context := Map Component (list Component).

(* Maps each Component to a list of Components that can measure it. *)
Definition Measures := Map Component (list Component).

(* A system's privacy policy maps each Place to the list of Components on the system that it is prepared to release measurements of (in the clear) to that Place.  This allows a system to disclose more/less configuration information to each place based on its current trust relationship with that Place. *)
Definition PrivacyPolicy := Map Plc (list Component).

(* Components present on my system *)
Definition MyComponents := list Component.
Require Import AbstractedTypes Term_Defs_Core Maps String
  Term_Defs Manifest_Admits EqClass ErrorStMonad_Coq.

Require Import Example_Phrases_Admits.

Require Import List.
Import ListNotations.


Definition manifest_set (A:Type) : Set.
Admitted.

Definition manifest_set_empty {A:Type} : manifest_set A.
Admitted.

Definition manset_add{A:Type} (x:A) (s:manifest_set A) : manifest_set A.
Admitted.

Definition list_to_manset{A:Type} : list A -> manifest_set A.
Admitted.

Definition filter_manset{A:Type} (f:A -> bool) (s:manifest_set A) : manifest_set A.
Admitted.

Definition is_empty_manset{A:Type} (s:manifest_set A) : bool.
Admitted.


(*
Check In.
In
	 : forall A : Type, A -> list A -> Prop
*)

(*
Check in_dec.
in_dec
	 : forall A : Type,
       (forall x y : A, {x = y} + {x <> y}) ->
       forall (a : A) (l : list A), {In a l} + {~ In a l}
*)

Definition In_set{A:Type} : A -> manifest_set A -> Prop.
Admitted.

Definition in_dec_set {A:Type} :
(forall x y : A, {x = y} + {x <> y}) ->
forall (a : A) (l : manifest_set A), {In_set a l} + {~ In_set a l}.
Admitted.

Lemma In_set_empty_contra{A:Type} : forall (i:A) (P:Prop),
  In_set i manifest_set_empty -> P.
Proof.
Admitted.

Lemma manadd_In_set{A:Type} : forall (s:manifest_set A) i j,
In_set i (manset_add j s) -> 
i = j \/ In_set i s.
Proof.
Admitted.

Lemma manadd_In_add{A:Type} : forall (s:manifest_set A) i,
In_set i (manset_add i s).
Proof.
Admitted.

Lemma in_set_add{A:Type} : forall (s:manifest_set A) i j,
In_set i s -> 
In_set i (manset_add j s).
Proof.
Admitted.

(*
Check existsb.

existsb
	 : forall A : Type, (A -> bool) -> list A -> bool
*)
Definition existsb_set{A:Type} : (A -> bool) -> manifest_set A -> bool.
Admitted.

(*
Check existsb_eq_iff_In
existsb_eq_iff_In
	 : forall (l : list ID_Type) (a : ID_Type),
       existsb (eqb a) l = true <-> In a l
*)
Definition existsb_eq_iff_In_set: forall (l : manifest_set ID_Type) (a : ID_Type),
existsb_set (eqb a) l = true <-> In_set a l.
Admitted.
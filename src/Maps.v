(*
Simple, list-based implementation of finite maps, borrowed/tweaked from here:
https://softwarefoundations.cis.upenn.edu/qc-current/TImp.html

Author:  Adam Petz, ampetz@ku.edu
*)
Require Export Maps_Class.
Require Import ConcreteEvidence.

Require Import List.
Import ListNotations.
Require Import Coq.Arith.EqNat.

(* ================================================================= *)
(** ** List-Based Maps *)

(** To encode typing environments (and, later on, states), we will
    need maps from identifiers to values. However, the function-based
    representation in the _Software Foundations_ version of Imp is not
    well suited for testing: we need to be able to access the domain
    of the map, fold over it, and test for equality; these are all
    awkward to define for Coq functions. Therefore, we introduce a
    simple list-based map representation that uses [id]s as the keys.

    The operations we need are:
       - [empty] : To create the empty map.
       - [get] : To look up the binding of an element, if any.
       - [set] : To update the binding of an element.
       - [dom] : To get the list of keys in the map. *)


    

(** The implementation of a map is a simple association list.  If a
    list contains multiple tuples with the same key, then the binding
    of the key in the map is the one that appears first in the list;
    that is, later bindings can be shadowed. *)

Instance nat_EqClass : EqClass nat :=
  { eqb:= PeanoNat.Nat.eqb;
    eqb_leibniz := beq_nat_true }.

(*
(** The [empty] map is the empty list. *)

Definition map_empty : Map := [].

(** To [get] the binding of an identifier [x], we just need to walk 
    through the list and find the first [cons] cell where the key 
    is equal to [x], if any. *)

Fixpoint map_get (m : Map ) x : option EvidenceC :=
  match m with
  | [] => None
  | (k, v) :: m' => if eqb x k then Some v else map_get m' x
  end.

(** To [set] the binding of an identifier, we just need to [cons] 
    it at the front of the list. *) 

Definition map_set (m:Map) (x:nat) (v:EvidenceC) : Map := (x, v) :: m.

(*
(** Finally, the domain of a map is just the set of its keys. *)
Fixpoint map_dom {K V} (m:Map K V) : list K :=
  match m with
  | [] => []
  | (k', v) :: m' => k' :: map_dom m'
  end.
*)

(** We next introduce a simple inductive relation, [bound_to m x a], that 
    holds precisely when the binding of some identifier [x] is equal to [a] in 
    [m] *)

Inductive bound_to : Map -> nat -> EvidenceC -> Prop :=
  | Bind : forall x m a, map_get m x = Some a -> bound_to m x a.
*)

(*
Polymorphic, list-based implementation of finite maps, borrowed/tweaked from here:
https://softwarefoundations.cis.upenn.edu/qc-current/TImp.html

Authors:  Adam Petz, ampetz@ku.edu
          Will Thomas, 30wthomas@ku.edu
 *)

Require Import String List.
Require Import EqClass ID_Type.

Require Import StructTactics.
Import ListNotations.
Open Scope list_scope.

(* ================================================================= *)
(** ** List-Based Maps *)

(** To encode typing environments (and, later on, states), we will
    need maps from identifiers to values. However, the function-based
    representation in the _Software Foundations_ version of Imp is not
    well suited for testing: we need to be able to accesplit_evt the domain
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
    of the key in the map is
 the one that appears first in the list;
    that is, later bindings can be shadowed. *)

Ltac map_ind m :=
  induction m; ff;
  try (rewrite eqb_eq in *; ff);
  try (rewrite eqb_neq in *; ff).

Definition MapC (A:Type) (B:Type) `{H : EqClass A} := list (A * B).

(** The [empty] map is the empty list. *)

Definition map_empty{A B:Type} `{H : EqClass A} : MapC A B := [].

(** To [get] the binding of an identifier [x], we just need to walk 
    through the list and find the first [cons] cell where the key 
    is equal to [x], if any. *)

Definition map_get {A B:Type} `{H : EqClass A} (x : A) : MapC A B -> option B :=
  fix F m := 
  match m with
  | [] => None
  | (k, v) :: m' => if eqb k x then Some v else F m'
  end.

(** To [set] the binding of an identifier, we just need to [cons] 
    it at the front of the list. *) 

Definition map_set {A B:Type} `{H : EqClass A} (x : A) (v : B) 
    : MapC A B -> MapC A B :=
  fix F m :=
  match m with
  | nil => (x,v) :: nil
  | (hk, hv) :: t =>
      if (eqb hk x)
      then (hk, v) :: t
      else (hk, hv) :: (F t)
  end.

Definition map_vals {A B:Type} `{H : EqClass A} : MapC A B -> list B :=
  fix F m :=
  match m with
  | [] => []
  | (k', v) :: m' => v :: F m'
  end.

Theorem mapC_get_works{A B:Type} `{H : EqClass A} : forall m (x:A) (v:B),
  map_get x (map_set x v m) = Some v.
Proof.
  map_ind m.
Qed.

Definition map_map {A B C : Type} `{HA : EqClass A} (f : B -> C) 
    : MapC A B -> MapC A C :=
  fix F m :=
  match m with
  | [] => []
  | (k, v) :: m' => (k, f v) :: (F m')
  end.

Theorem map_map_get_works : forall {A B C : Type} `{HA : EqClass A} (f : B -> C) m x v,
  map_get x m = Some v ->
  map_get x (map_map f m) = Some (f v).
Proof.
  map_ind m.
Qed.

Definition map_union {A B : Type} `{HA : EqClass A} (fn : B -> B -> B) 
    : MapC A B -> MapC A B -> MapC A B :=
  fix F m1 m2 :=
  match m1 with
  | [] => m2
  | (k, v) :: m1' => 
    match map_get k m2 with
    | None => (k, v) :: F m1' m2
    | Some v' => (k, fn v v') :: F m1' m2
    end
  end.

Theorem map_union_get_spec : forall {A B : Type} `{HA : EqClass A} 
    (m1 m2 : MapC A B) (fn : B -> B -> B) k v,
  map_get k (map_union fn m1 m2) = Some v <->
  ((exists v1 v2,
    map_get k m1 = Some v1 /\
    map_get k m2 = Some v2 /\
    fn v1 v2 = v) \/
  (map_get k m1 = Some v /\ map_get k m2 = None) \/ 
  (map_get k m1 = None /\ map_get k m2 = Some v)).
Proof.
  induction m1; ff;
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *; ff; 
  try find_rewrite_lem IHm1; ff;
  try erewrite <- IHm1 in *; ff;
  try (left; eexists; eexists; ff; fail).
Qed.

Lemma mapC_get_distinct_keys{A B:Type} `{H : EqClass A} : 
  forall m (k1 k2:A) (v1 v2:B),
  k1 <> k2 ->
  map_get k2 m = Some v2 ->
  map_get k2 (map_set k1 v1 m) = Some v2.
Proof.
  map_ind m.
Qed.

Lemma map_set_id{A B:Type} `{H : EqClass A} : forall m (k :A) (v:B),
  map_get k m = Some v ->
  m = map_set k v m.
Proof.
  map_ind m; erewrite <- IHm; ff.
Qed.

Lemma mapC_get_distinct_keys_from_set {A B :Type} `{H : EqClass A} : forall (m : MapC A B) k1 k2 v1 v2,
  k1 <> k2 ->
  map_get k2 (map_set k1 v1 m) = Some v2 ->
  map_get k2 m = Some v2.
Proof.
  map_ind m.
Qed.

Theorem map_distinct_key_rw {A B:Type} `{H : EqClass A} : 
  forall m (k1 k2:A) (v1 v2:B),
  k1 <> k2 ->
  map_get k2 (map_set k1 v1 m) = map_get k2 m.
Proof.
  map_ind m.
Qed.

Theorem map_has_buried : forall {A B : Type} `{EqClass A} (pre : list (A * B)) key val post,
  exists val', map_get key (pre ++ (key, val) :: post) = Some val'.
Proof.
  map_ind pre.
Qed.

Theorem map_app_unfolder: forall {A B : Type} `{EqClass A} 
    (pre : list (A * B)) key val post val',
  map_get key (pre ++ (key, val) :: post) = Some val' ->
  map_get key pre = None ->
  val = val'.
Proof.
  map_ind pre.
Qed.

Theorem map_sandwich_not_none: forall {A B : Type} `{EqClass A} 
    (pre : list (A * B)) key val post,
  map_get key (pre ++ (key, val) :: post) = None -> False.
Proof.
  map_ind pre.
Qed.

Lemma map_set_sandwiched : forall {A B : Type} `{EqClass A},
  forall (m : MapC A B) k v,
  exists preM postM, 
    map_set k v m = preM ++ (k, v) :: postM /\
    map_get k preM = None.
Proof.
  induction m; simpl in *; intuition; eauto.
  - exists nil, nil; simpl in *; eauto.
  - destruct (IHm k v) as [preM' [postM' H']].
    break_match.
    * rewrite eqb_eq in *; subst;
      exists nil, m; eauto.
    * exists ((a0,b) :: preM'), (postM'); 
      intuition.
      ** rewrite H0; eauto.
      ** simpl; rewrite Heqb0; eauto.
Qed.

Theorem map_set_unfolder : forall {A B : Type} `{EqClass A},
  forall (m : MapC A B) k1 k2 v1 v2,
  k1 <> k2 ->
  map_get k1 m = None ->
  map_get k1 (map_set k2 v2 m) = Some v1 ->
  False.
Proof.
  map_ind m.
Qed.

Theorem map_get_none_iff_not_some : forall {A B : Type} `{EqClass A},
  forall (m : MapC A B) k,
  map_get k m = None <-> (forall v, map_get k m = Some v -> False).
Proof.
  map_ind m; erewrite IHm; ff.
Qed.


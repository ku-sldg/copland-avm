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

Definition MapC (A:Type) (B:Type) `{H : EqClass A} := list (A * B).

(** The [empty] map is the empty list. *)

Definition map_empty{A B:Type} `{H : EqClass A} : MapC A B := [].

(** To [get] the binding of an identifier [x], we just need to walk 
    through the list and find the first [cons] cell where the key 
    is equal to [x], if any. *)

Fixpoint map_get{A B:Type} `{H : EqClass A} (m : MapC A B ) (x : A) : option B :=
  match m with
  | [] => None
  | (k, v) :: m' => if eqb k x then Some v else map_get m' x
  end.

(** To [set] the binding of an identifier, we just need to [cons] 
    it at the front of the list. *) 

Fixpoint map_set{A B:Type} `{H : EqClass A} (m:MapC A B) (x:A) (v:B) : MapC A B := 
  match m with
  | nil => (x,v) :: nil
  | (hk, hv) :: t =>
      if (eqb hk x)
      then (hk, v) :: t
      else (hk, hv) :: (map_set t x v)
  end.

Fixpoint map_vals{A B:Type} `{H : EqClass A} (m : MapC A B ) : list B :=
  match m with
  | [] => []
  | (k', v) :: m' => v :: map_vals m'
  end.

Theorem mapC_get_works{A B:Type} `{H : EqClass A} : forall m (x:A) (v:B),
  map_get (map_set m x v) x = Some v.
Proof.
  induction m; ff; rewrite eqb_refl in *; ff.
Qed.

Fixpoint map_map {A B C : Type} `{HA : EqClass A} (f : B -> C) (m : MapC A B) : MapC A C :=
  match m with
  | [] => []
  | (k, v) :: m' => (k, f v) :: (map_map f m')
  end.

Theorem map_map_get_works : forall {A B C : Type} `{HA : EqClass A} (f : B -> C) m x v,
  map_get m x = Some v ->
  map_get (map_map f m) x = Some (f v).
Proof.
  induction m; simpl in *; intuition; try congruence;
  break_match; repeat find_injection; simpl in *;
  find_rewrite; eauto.
Qed.

Fixpoint map_union {A B : Type} `{HA : EqClass A} (m1 m2 : MapC A B) 
    (fn : B -> B -> B) : MapC A B :=
  match m1 with
  | [] => m2
  | (k, v) :: m1' => 
    match map_get m2 k with
    | None => (k, v) :: map_union m1' m2 fn
    | Some v' => (k, fn v v') :: map_union m1' m2 fn
    end
  end.

Theorem map_union_get_spec : forall {A B : Type} `{HA : EqClass A} 
    (m1 m2 : MapC A B) (fn : B -> B -> B) k v,
  map_get (map_union m1 m2 fn) k = Some v <->
  ((exists v1 v2,
    map_get m1 k = Some v1 /\
    map_get m2 k = Some v2 /\
    fn v1 v2 = v) \/
  (map_get m1 k = Some v /\ map_get m2 k = None) \/ 
  (map_get m1 k = None /\ map_get m2 k = Some v)).
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
  map_get m k2 = Some v2 ->
  map_get (map_set m k1 v1) k2 = Some v2.
Proof.
  induction m; simpl in *; intuition; eauto; try congruence.
  repeat break_if; repeat find_injection;
  repeat rewrite eqb_eq in *; subst; eauto;
  try congruence; simpl in *;
  try find_rewrite; eauto;
  rewrite eqb_refl; eauto.
Qed.

Lemma map_set_id{A B:Type} `{H : EqClass A} : forall e (p:A) (m:B),
  map_get e p = Some m ->
  e = map_set e p m.
Proof.
  induction e; simpl in *; intuition; eauto; try congruence;
  repeat break_if; repeat find_injection; eauto.
  erewrite <- IHe; eauto.
Qed.

Lemma mapC_get_distinct_keys_from_set {A B :Type} `{H : EqClass A} : forall (m : MapC A B) k1 k2 v1 v2,
  k1 <> k2 ->
  map_get (map_set m k1 v1) k2 = Some v2 ->
  map_get m k2 = Some v2.
Proof.
  induction m; simpl in *; intuition; eauto; try congruence.
  - break_if; try rewrite eqb_eq in *; intuition.
  - repeat break_if; repeat (rewrite eqb_eq in *; subst); intuition; eauto;
    simpl in *; try rewrite eqb_refl in *; repeat find_injection; eauto;
    repeat find_rewrite; eauto.
Qed.


Lemma map_distinct_key_rw {A B:Type} `{H : EqClass A} : 
  forall m (k1 k2:A) (v1 v2:B),
  k1 <> k2 ->
  map_get (map_set m k1 v1) k2 = map_get m k2.
Proof.
  induction m; simpl in *; intuition; eauto; try congruence.
  - break_match; eauto; rewrite eqb_eq in *; congruence.
  - repeat break_if; repeat find_injection;
    repeat rewrite eqb_eq in *; subst; eauto;
    try congruence; simpl in *;
    try find_rewrite; eauto;
    rewrite eqb_refl; eauto.
Qed.

Theorem map_has_buried : forall {A B : Type} `{EqClass A} (pre : list (A * B)) key val post,
  exists val', map_get (pre ++ (key, val) :: post) key = Some val'.
Proof.
  induction pre; simpl in *; intuition; eauto.
  - rewrite eqb_refl; eauto.
  - break_if; try find_injection; try congruence; eauto.
Qed.

Theorem map_app_unfolder: forall {A B : Type} `{EqClass A} 
    (pre : list (A * B)) key val post val',
  map_get (pre ++ (key, val) :: post) key = Some val' ->
  map_get pre key = None ->
  val = val'.
Proof.
  induction pre; simpl in *; intuition; eauto.
  - rewrite eqb_refl in *; find_injection; eauto.
  - break_if; try find_injection; try congruence; eauto.
Qed.

Theorem map_sandwich_not_none: forall {A B : Type} `{EqClass A} 
    (pre : list (A * B)) key val post,
  map_get (pre ++ (key, val) :: post) key = None -> False.
Proof.
  induction pre; simpl in *; intuition; eauto.
  - rewrite eqb_refl in *; congruence.
  - break_if; try find_injection; try congruence; eauto.
Qed.

Lemma map_set_sandwiched : forall {A B : Type} `{EqClass A},
  forall (m : MapC A B) k v,
  exists preM postM, 
    map_set m k v = preM ++ (k, v) :: postM /\
    map_get preM k = None.
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
  map_get m k1 = None ->
  map_get (map_set m k2 v2) k1 = Some v1 ->
  False.
Proof.
  induction m; intuition; eauto.
  - simpl in *; repeat break_match; 
    repeat find_injection; try (rewrite eqb_eq in *; subst);
    try congruence.
  - destruct (eqb a0 k1) eqn:E.
    * rewrite eqb_eq in *; subst.
      simpl in *; rewrite eqb_refl in *; congruence.
    * destruct (eqb a0 k2) eqn:E1.
      ** rewrite eqb_eq in *; subst.
          simpl in *; repeat find_rewrite.
          rewrite eqb_refl in *.
          assert (map_get (map_set m k2 v2) k1 = Some v1). {
            simpl in *; find_rewrite; congruence.
          }
          eauto.
      ** simpl in *; repeat find_rewrite; simpl in *.
         find_rewrite; eauto.
Qed.

Theorem map_get_none_iff_not_some : forall {A B : Type} `{EqClass A},
  forall (m : MapC A B) k,
  map_get m k = None <-> (forall v, map_get m k = Some v -> False).
Proof.
  induction m; simpl in *; intuition; eauto; try congruence.
  break_match; try congruence.
  erewrite IHm; eauto.
Qed.

(* A two-way implementation of list maps, where you can lookup from a key, or value *)
Definition MapD (A:Type) (B:Type) `{H : EqClass A} `{H1 : EqClass B} := list (A * B).

(** The [empty] map is the empty list. *)

Definition mapD_empty{A B:Type} `{H : EqClass A} `{H1 : EqClass B} : MapD A B := [].

(** To [get] the binding of an identifier [x], we just need to walk 
    through the list and find the first [cons] cell where the key 
    is equal to [x], if any. *)

Fixpoint mapD_get_value{A B:Type} `{H : EqClass A} `{H1 : EqClass B} (m : MapD A B ) x : option B :=
  match m with
  | [] => None
  | (k, v) :: m' => if eqb x k then Some v else mapD_get_value m' x
  end.

  
Fixpoint mapD_get_key{A B:Type} `{H : EqClass A} `{H1 : EqClass B} 
          (m : MapD A B ) (v : B) : option A :=
  match m with
  | [] => None
  | (k, v') :: m' => if eqb v v' then Some k else mapD_get_key m' v
  end.


(** To [set] the binding of an identifier, we just need to [cons] 
    it at the front of the list. *) 

Definition mapD_set{A B:Type} `{H : EqClass A} `{H1 : EqClass B} 
                    (m:MapD A B) (x:A) (v:B) : MapD A B := (x, v) :: m.

Fixpoint mapD_vals{A B:Type} `{H : EqClass A} `{H1 : EqClass B} (m : MapD A B ) : list B :=
  match m with
  | [] => []
  | (k', v) :: m' => v :: mapD_vals m'
  end.

Fixpoint mapD_keys{A B : Type} `{H : EqClass A} `{H1 : EqClass B} (m : MapD A B) : list A :=
  match m with
  | nil => nil
  | (k',v') :: m' => k' :: mapD_keys m'
  end.

(* TODO: Update these proofs to be more general *)
Lemma mapD_key_values_length : forall m,
  List.length (mapD_vals m) = List.length (mapD_keys m).
Proof.
  intros.
  induction m; simpl.
  - reflexivity.
  - destruct a. simpl. rewrite IHm. reflexivity.
Qed.

Theorem mapD_kv_len_match: forall m,
  List.length (mapD_vals m) = List.length m.
Proof.
  intros.
  induction m; simpl.
  - reflexivity.
  - destruct a; simpl; rewrite IHm; reflexivity.
Qed.

Theorem mapD_get_works : forall {A B : Type} `{HA : EqClass A} `{HB : EqClass B} (m : MapD A B) x v,
  mapD_get_key (mapD_set m x v) v = Some x.
Proof.
  induction m; simpl in *; intuition; destEq v v; intuition.
Qed.

(*
(** Finally, the domain of a map is just the set of its keys. *)
Fixpoint map_dom {K V} (m:MapC K V) : list K :=
  match m with
  | [] => []
  | (k', v) :: m' => k' :: map_dom m'
  end.
*)

(** We next introduce a simple inductive relation, [bound_to m x a], that 
    holds precisely when the binding of some identifier [x] is equal to [a] in 
    [m] *)

Inductive bound_to{A B:Type} `{H : EqClass A} : MapC A B -> A -> B -> Prop :=
| Bind : forall x m a, map_get m x = Some a -> bound_to m x a.
Local Hint Constructors bound_to : map_bound_to.

Lemma bound_to_eq_dec {A B: Type} `{H: EqClass A}:
  forall m x,
    {(exists (a:B), bound_to m x a)} + {not (exists (a:B), bound_to m x a)}.
Proof.
  intuition;
  destruct (map_get m x) eqn:E;
  try (right; intros HC; destruct HC as [a HC]; inversion HC; congruence);
  eauto with map_bound_to.
Qed.
    

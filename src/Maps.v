(*
Polymorphic, list-based implementation of finite maps, borrowed/tweaked from here:
https://softwarefoundations.cis.upenn.edu/qc-current/TImp.html

Author:  Adam Petz, ampetz@ku.edu
 *)

Require Import EqClass.

Require Import List.
Import ListNotations.
Require Import Coq.Arith.EqNat Coq.Program.Tactics PeanoNat.

Require Import StructTactics.

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
    of the key in the map is
 the one that appears first in the list;
    that is, later bindings can be shadowed. *)

Definition MapC (A:Type) (B:Type) `{H : EqClass A} := list (A * B).

(** The [empty] map is the empty list. *)

Definition map_empty{A B:Type} `{H : EqClass A} : MapC A B := [].

(** To [get] the binding of an identifier [x], we just need to walk 
    through the list and find the first [cons] cell where the key 
    is equal to [x], if any. *)

Fixpoint map_get{A B:Type} `{H : EqClass A} (m : MapC A B ) x : option B :=
  match m with
  | [] => None
  | (k, v) :: m' => if eqb x k then Some v else map_get m' x
  end.

(** To [set] the binding of an identifier, we just need to [cons] 
    it at the front of the list. *) 

Definition map_set{A B:Type} `{H : EqClass A} (m:MapC A B) (x:A) (v:B) : MapC A B := (x, v) :: m.

Fixpoint map_vals{A B:Type} `{H : EqClass A} (m : MapC A B ) : list B :=
  match m with
  | [] => []
  | (k', v) :: m' => v :: map_vals m'
  end.

Fixpoint invert_map {A B : Type} `{HA : EqClass A, HB : EqClass B} (m : MapC A B) : MapC B A :=
  match m with
  | [] => []
  | (k', v') :: m' => (v', k') :: (invert_map m')
  end.

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
  length (mapD_vals m) = length (mapD_keys m).
Proof.
  intros.
  induction m; simpl.
  - reflexivity.
  - destruct a. simpl. rewrite IHm. reflexivity.
Qed.

Theorem mapD_kv_len_match: forall m,
  length (mapD_vals m) = length m.
Proof.
  intros.
  induction m; simpl.
  - reflexivity.
  - destruct a; simpl; rewrite IHm; reflexivity.
Qed.

Theorem mapD_get_works : forall m x v,
  mapD_get_key (mapD_set m x v) v = Some x.
Proof.
  intros.
  induction x; simpl;
  rewrite Nat.eqb_refl; reflexivity.
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

Lemma bound_to_eq_dec {A B: Type} `{H: EqClass A}:
  forall m x,
    {(exists (a:B), bound_to m x a)} + {not (exists (a:B), bound_to m x a)}.
Proof.
  intros.
  generalizeEverythingElse m.
  induction m; intros.
  -
    right.
    unfold not.
    intros.
    destruct_conjs.
    invc H1.
    simpl in *.
    solve_by_inversion.
  - specialize IHm with x.
    destruct IHm.
    * (* bound_to m x a *)
      destruct a.
      destruct (eqb x a) eqn:E.
      ** (* x = a *)
         left. exists b. econstructor. simpl. 
         rewrite E. auto.
      ** (* x <> a *)
        assert (exists a0, bound_to ((a,b) :: m) x a0). {
          destruct e. exists x0.
          inversion H0; subst. econstructor. simpl.
          rewrite E. auto.
        }
        left. auto.
    * (* ~ (exists a, bound_to m x a )*)
      destruct a.
      destruct (eqb x a) eqn:E.
      ** (* x = a *)
         left. exists b. econstructor; simpl; rewrite E; auto.
      ** (* x <> a *)
         assert (~ (exists a0, bound_to ((a,b) :: m) x a0)). {
          intros Contra. destruct Contra. inversion H0. subst.
          unfold map_get in H1. rewrite E in H1. simpl in *.
          destruct n. exists x0. econstructor. apply H1.
         }
         right. auto.
Qed.
    

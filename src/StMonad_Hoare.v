(* 
Modified from:  https://www.cs.cornell.edu/courses/cs6115/2017fa/notes/Hoare.v

Author:  Adam Petz
*)

(* begin hide *)
Require Import Eqdep.
Require Import String.
Require Import List.
Require Import Lia.

Require Import Coq.Arith.Peano_dec  Coq.Arith.Compare_dec.


Set Implicit Arguments.
Unset Implicit Introduction.
(* end hide *)

(** * Imperative Programming in Coq *)

(** Just as in Haskell, we can simulate writing programs that manipulate
    state by taking advantage of monads.  Another way to think about this
    is that we can embed the primitives of IMP into Coq and we automatically
    get a higher-order, dependently-typed, stateful programming language.

    The language is IMP-like, but it is a little different in that a
    command computes a value. Intuitively, the value computed by a sequence
    of commands is the value of the last command in the sequence. Further,
    unlike IMP, in which there is a finite set of mutable variables, we
    we will have the ability to dynamically allocate new mutable heap
    locations. We also get to use Coq's functional expressions as the
    expressions in the language, including [if].

    We do this here as a _shallow embedding_ in which we reuse the metalanguage
    of Coq to build the constructs of the desired language, in this case
    using a monad to capture the statefulness of the language. With shallow
    embedding, we inherit all the strengths and weaknesses of the metalanguage.
    For example, we can't write down imperative loops directly because that's
    not part of Gallina. On the other hand, we get dependent types and all
    the other machinery of Coq. 

    The alternative approach, which we have already seen earlier when
    defining the semantics of IMP, is a _deep embedding_ in which we inductively
    define the syntax of the language, giving us complete control over what
    the language looks like. However, this requires us to explicitly specify the
    semantics of the language as inductive relations, and the features of
    the metalanguage are harder to exploit.

    The development below builds a module that is parameterized by 
    some universe of values that we can store in the heap, and then later 
    instantiate the universe with a type of my choice.  In the module, we
    will define basic notions of a heap, of commands as a monad which 
    manipulates heaps, and appropriate Hoare-logic rules for reasoning
    about these commands.
*)
Module Type UNIVERSE.
  Parameter heap : Type.
  Parameter empty_heap : heap.
  (*Parameter Cmd : Type -> Type -> Type. *)
End UNIVERSE.

Module MonadHoare(U : UNIVERSE).


  (*
  (** We will model pointers using nats, but any type that provides
      an equality and way to generate a fresh value would do. *)
  Definition ptr := nat.
  Definition ptr_eq_dec := eq_nat_dec.

  (** We will model heaps as lists of pointers and values drawn from
      the universe. *)
  Definition heap := list (ptr * U.t).

  (** We model commands of type [t] as functions that take
      a heap and return an optional pair of a heap and a [t].  So
      this is really a combination of the state and option monad. *)
  Definition Cmd(t:Type) := heap -> option(heap*t).
  
  (** The definitions of [ret] and [bind] for the monad.  Unlike
      Haskell, we could actually prove that the monad laws hold! 
      (This would be a good homework.)  *)
  Definition ret t (x:t) : Cmd t := fun h => Some (h,x).  
  Definition bind t u (c : Cmd t) (f : t -> Cmd u) : Cmd u := 
    fun h1 => 
      match c h1 with 
        | None => None
        | Some (h2,v) => f v h2
      end.

  (** Some notation to approximate Haskell's "do" notation. *)
  Notation "x <- c ; f" := (bind c (fun x => f))
    (right associativity, at level 84, c at next level) : cmd_scope.
  Notation "c ;; f" := (bind c (fun _:unit => f))
    (right associativity, at level 84) : cmd_scope.
  Local Open Scope cmd_scope.

  (** Like Haskell's runST, we can provide a run for the monad, 
      starting with an empty heap. *)
  Definition run(t:Type)(c:Cmd t) := c nil.

  (** Some example commands *)
  Definition c1 := ret 0.
  Compute run c1.
  Definition c2 := x <- ret 0 ; y <- ret 1 ; ret (x+y).
  Compute run c2.

  (** Failure -- this is like throwing an exception.  A good 
      homework for people unfamiliar with monads is to define 
      a "try _ catch _" construct. *)
  Definition exit t : Cmd t := fun h => None.

  (** Allocation -- to allocate a fresh location, we run through
      the heap and find the biggest pointer, and simply return 
      the next biggest pointer.  Another good homework is to 
      change the definitions here to carry along the "next available
      pointer" as part of the state of the system. *)
  Definition max (p1 p2:ptr) := if le_gt_dec p1 p2 then p2 else p1.

  Fixpoint max_heap(h:heap) := 
    match h with 
      | nil => 0
      | (p,_)::rest => max p (max_heap rest)
    end.

  (** The [new u] command allocates a new location in the heap, 
      initializes it with the value [u], and returns the pointer
      to the freshly-allocated location. *)

  Fixpoint insert (h:heap) (x:ptr) (v:U.t) : heap := 
    match h with 
      | nil => (x,v)::nil
      | (y,w)::h' => 
        if le_gt_dec x y then
          (x,v)::(y,w)::h'
        else (y,w)::(insert h' x v)
    end.

  Definition new (u:U.t) : Cmd ptr := 
    fun h => 
      let p := 1 + max_heap h in Some (insert h p u, p).

  (** Lookup a pointer in the heap, returning the value associated
      with it if any. *)  
  Fixpoint lookup (h:heap) (p:ptr) : option U.t := 
    match h with 
      | nil => None
      | (p',u')::rest => if ptr_eq_dec p p' then Some u' else lookup rest p
    end.

  (** The [read] command looks up the given pointer and returns the
      value if any, and fails if there is no value present.  It leaves
      the heap unchanged. *)
  Definition read (p:ptr) : Cmd U.t := 
    fun h => match lookup h p with 
               | None => None
               | Some u => Some (h, u)
             end.

  (** Remove the pointer [p] from the heap, returning a new heap. *)
  Fixpoint remove (h:heap) (p:ptr) : heap := 
    match h with 
      | nil => nil
      | (p',u')::h => if ptr_eq_dec p p' then remove h p else (p',u')::(remove h p)
    end.

  (** To write [u] into the pointer [p], we first check that [p]
      is defined in the heap, and then remove it, and add it back
      with the value [u]. *)
  Definition write (p:ptr) (u:U.t) : Cmd unit := 
    fun h => match lookup h p with 
               | None => None
               | Some _ => Some(insert (remove h p) p u, tt)
             end.

  (** To free the pointer [p], we simply remove it from the heap.
      Again, this will fail if [p] wasn't in the heap to begin with. *)
  Definition free (p:ptr) : Cmd unit := 
    fun h => match lookup h p with 
               | None => None
               | Some _ => Some(remove h p, tt)
             end.

   *)

  (*
  Require Import StVM.
  Require Import MonadVM. *)
  Require Import GenStMonad StructTactics.

  Definition heap := U.heap.
  Definition CVM := St heap.

  (** * Hoare Logic *)

  (** Now that we've defined a language of commands, we can define
      a logic for reasoning about commands. *)
  Definition hprop := heap -> Prop.

  (** The Hoare Total-Correctness Triple [{{P}}c{{Q}}] holds when:
      if we run [c] in a heap [h] satisfying [P], we get back a heap
      [h'] and value [v], satisfying [Q h v h'].  Notice that our
      post-conditions allow us to relate the input heap, the output
      value, and the output heap.  The ability to refer to the initial
      heap is important for giving rules that are as strong as possible
      without having to introduce auxilliary variables. *)
  Definition hoare_tc_triple(t:Type)
    (P : hprop)(c:CVM t)(Q : heap -> t -> hprop) := 
    forall h, P h -> match c h with 
                       | (None,_) => False
                       | (Some v, h') => Q h v h'
                     end.
  Notation "{{ P }} c {{ Q }}" := (hoare_tc_triple P c Q) 
                                    (at level 90) : cmd_scope.

  Local Open Scope cmd_scope.



        Ltac break_let' :=
        match goal with
        | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] =>
          destruct X eqn:?; try solve_by_inversion
        | [ |- context [ (let (_,_) := ?X in _) ] ] =>
          destruct X eqn:?; try solve_by_inversion
        end.

  (** My usual simplification tactic. *)
  Ltac mysimp := 
    unfold hprop, hoare_tc_triple, bind(*, max, free, read, write*) in * ; intros ; 
    repeat (repeat break_let';
        match goal with
                | [ H : _ /\ _ |- _] => destruct H
                | [ H : (_ * _)%type |- _] => destruct H
                | [ H1 : forall _, ?P1 _ -> _, H2 : ?P1 ?h |- _] => 
                  generalize (H1 h H2) ; clear H1 ; intros
                | [ H1 : forall _ _ _, ?P1 _ _ -> _, H2 : ?P1 ?x ?h |- _] => 
                  generalize (H1 _ _ _ H2) ; clear H1 ; intros
                (*| [ H : match ?e with | (Some _,_) => _ | (None,_) => _ end |- _ ] => 
                  destruct e *)
                (*| [ H : context[ptr_eq_dec ?x ?y] |- _ ] => 
                  destruct (ptr_eq_dec x y) ; subst
                | [ |- context[ptr_eq_dec ?x ?y] ] => 
                  destruct (ptr_eq_dec x y) ; subst *)

                (* | [c: CVM _,
                      h: heap (*,
                         HH: context[let _ := (c h) in _]*) |- _] =>
                  destruct (c h); try solve_by_inversion *)
                | [ o:option _ |- _] =>
                  destruct o; try solve_by_inversion
                | [ H : context[le_gt_dec ?x ?y] |- _ ] => 
                  destruct (le_gt_dec x y) 
                | [ |- _ /\ _ ] => split
                | [ H : exists _, _ |- _] => destruct H
                | [ H : Some ?x = Some ?y |- _ ] => inversion H ; clear H ; subst
                | _ => assert False ; [ lia | contradiction ]
              end) ; subst ; simpl in * ; try firstorder ; repeat find_inversion; auto with arith.

  (** A heap [h] always satisfies the predicate [top]. *)
  Definition top : hprop := fun _ => True.

  (** The Hoare-rule for return:  We can run the command in any initial state
      and end up in a state where the heap is unchanged, and the return value
      is equal to the value we passed in.  This is pretty obviously the 
      weakest precondition needed to ensure the command won't fail, and
      the strongest post-condition we can show about the resulting state.*)
  Lemma ret_tc (t:Type) (v:t) : {{ top }} ret v {{ fun h x h' => x=v /\ h=h' }}.
    mysimp.
  Qed.

  (** An alternative, more conventional rule.  I don't like this because
      it forces me to come up with a predicate -- i.e., we can only use
      it in a context where [P] is already known. *)
  Lemma ret_tc' (t:Type) (v:t) (P : t -> hprop) : 
    {{ P v }} ret v {{ fun _ x => P x }}.
  Proof.
    mysimp.
  Qed.

      Ltac dest_cvm :=
      match goal with
      | [c: CVM _,
            h: heap,
               HH: context[let _ := _ in _] |- _] =>
        destruct (c h); try solve_by_inversion
      end.

  (** The rule of consequence:  we can strengthen the pre-condition (i.e.,
      require more before executing), and weaken the post-condition (i.e.,
      ensure less.) 
  *)
  Lemma consequence_tc {S t:Type} {c:CVM t} {P1 P2 : hprop} {Q1 Q2:heap->t->hprop} : 
    {{ P1 }} c {{ Q1 }} -> 
    (forall h, P2 h -> P1 h) -> 
    (forall h x h', Q1 h x h' -> Q2 h x h') -> 
    {{ P2 }} c {{ Q2 }}.
  Proof.
    mysimp.
  Qed.

  (*
  Lemma max_zero : forall n, max 0 n = n.
     induction n ; auto.
  Qed.

  Lemma lookup_max h : forall n, n > max_heap h -> lookup h n = None.
    induction h ; intros ; simpl in * ; mysimp.
    eapply IHh.
    lia.
  Qed. Hint Resolve lookup_max.
    
  (** The [new u] command can be run in any initial state [h], and 
     results in a state [(p,u)::h] where [p] is fresh.  The freshness
     is captured by the fact that [lookup h p = None], i.e., the
     pointer was unallocated in the pre-state. *)
  Lemma new_tc (u:U.t) :
    {{ top }} new u {{ fun h p h' => lookup h p = None /\ h' = insert h p u }}.
  Proof.
    mysimp.
  Qed.
  (** Note that the post-condition for [new] is weaker than it has
      to be.  We could strengthen it to capture the fact that 
      [p] is actually 1 + the max pointer in the heap.  But leaving
      the specification weaker allows us to change our allocation
      strategy. *)

  Lemma lookup_none_remove p h : lookup h p = None -> remove h p = h.
    induction h ; mysimp  ; simpl in * ; mysimp ; try congruence.
  Qed.

  (** The [free p] command can be run in any state where [p] is
      defined, and results in a state where [p] is removed. *)
  Lemma free_tc (p:ptr) : 
    {{ fun h => lookup h p <> None }}
    free p
    {{ fun h _ h' => h' = remove h p }}.
  Proof.
    mysimp ; induction h ; simpl in * ; mysimp.
    destruct (lookup h p) ; mysimp. 
  Qed.

  (** The [read p] command can be run in any state where [p] is
      defined, and results in an unchanged state.  The value returned
      is equal to the the value associated with [p]. *)
  Lemma read_tc (p:ptr) : 
    {{ fun h => lookup h p <> None }}
    read p
    {{ fun h v h' => h = h' /\ lookup h p = Some v }}.
  Proof.
    mysimp. destruct (lookup h p) ; mysimp.
  Qed.

  (** The [write p u] command can be run in any state where [p] is
      defined, and results in a state where [p] maps to [u], but
      is otherwise unchanged. *)
  Lemma write_tc (p:ptr) (u:U.t) : 
    {{ fun h => lookup h p <> None }}
    write p u
    {{ fun h _ h' => h' = insert (remove h p) p u}}.
  Proof.
    mysimp ; destruct (lookup h p) ; mysimp.
  Qed.
*)

  (** The rule for [bind] is the most complicated, but that's more
      because we want to support dependency than anything else.  
      Intuitively, if [{{P1}}c{{Q1}}] and [{{P2 x}}f x{{Q2 x}}], then
      the compound command [x <- c ; f] has as the weakest pre-
      condition needed to ensure we don't fail that [P1] holds and
      for any (demonically-chosen state and value) [x] and [h'] which
      [c] might compute (and hence satisfies [Q1 h x h']), we can
      show that [P2 x h'] holds.  Both conditions are needed to ensure
      that neither command will fail.  

      The post-condition is the strongest post-condition we can
      calculate as the composition of the commands.  It is effectively
      the relational composition of the post-conditions for [c] and
      [f] respectively. 

      Again, note that we can effectively compute the pre- and post-
      conditions instead of forcing a prover to magically come up
      with appropriate conditions.
      *)
  Definition precomp(t:Type)(P1:hprop)(Q1:heap->t->hprop)(P2:t->hprop) : hprop := 
    fun h => P1 h /\ (forall (x:t)(h':heap), Q1 h x h' -> P2 x h').

  Definition postcomp(t u:Type)(Q1:heap->t->hprop)(Q2:t->heap->u->hprop) : 
    heap -> u -> hprop := 
    fun h x h' => exists y, exists h'', Q1 h y h'' /\ Q2 y h'' x h'.

  Lemma bind_tc {t u:Type} {c:CVM t} {f : t -> CVM u} 
    {P1:hprop} {Q1:heap->t->hprop} {P2:t->hprop} {Q2:t->heap->u->hprop} : 
    {{ P1 }} c {{ Q1 }} -> 
    (forall x:t, {{ P2 x }} (f x) {{ Q2 x }}) -> 
    {{ precomp P1 Q1 P2 }}
    x <- c ;; f x 
    {{ postcomp Q1 Q2 }}.
  Proof.
    unfold precomp, postcomp ; mysimp ; generalize (H0 _ _ (H2 _ _ H)) ; intros ; mysimp.

    eauto.
   
    (*
    rewrite Heqp2 in *.
    repeat find_inversion.
    eassumption.
    
    repeat find_inversion.
    rewrite Heqp3 in *.
    solve_by_inversion. *)
  Qed.

  Notation "x <-- c ; f" := (bind_tc c (fun x => f))
    (right associativity, at level 84, c at next level) : cmd_scope.
  Notation "c ;;; f" := (bind_tc c (fun _ => f))
    (right associativity, at level 84) : cmd_scope.

  (*
  (** Just for fun, we can define our own version of [if]. *)
  Lemma if_tc{t:Type}{B1 B2:Prop}(b:({B1}+{B2}))(c1 c2:Cmd t) {P1} {P2} {Q1} {Q2} : 
    {{P1}}c1{{Q1}} -> 
    {{P2}}c2{{Q2}} ->
    {{fun h => if b then P1 h else P2 h}}
    if b then c1 else c2
    {{fun h x h' => if b then Q1 h x h' else Q2 h x h'}}.
  Proof.
    destruct b ; mysimp.
  Qed.
*)

  (** Now we can give a proper interface to run -- we should only 
      pass it commands that will return a value and then we can
      guarantee that we won't get a failure. *)
  Definition run_tc{t:Type}(c:CVM t) : {{top}}c{{fun _ _ => top}} -> t.
  Proof.
    unfold top ; intros ; mysimp. generalize (H U.empty_heap I).
    destruct (c U.empty_heap) ; mysimp.
  Defined.

End MonadHoare.





(*

Require Import StVM.

Module MyUniverse <: UNIVERSE.
 (** Alas, our universe of storable values cannot be big enough
     to store computations.  If we try to add computations to the
     types in U, we get a non-positive occurrence.  In short, you
     seem to need generally recursive types to build storable
     commands.  Not suprisingly, this leads to termination problems,
     as we can use Landin's knot to build a diverging computation... *)
(*
  Inductive U : Type := 
  | Nat_t : nat -> U
  | Pair_t : U -> U -> U.

  Definition t := U. *)
  Definition heap := cvm_st.
  Definition empty_heap := empty_vmst.
End MyUniverse.

Module MyFunctionalImp := MonadHoare(MyUniverse).

Import MyUniverse.
Import MyFunctionalImp.
Local Open Scope cmd_scope.

(** More example commands -- some can go wrong! *)
Definition c3 := z <- new (Nat_t 0) ; w <- read z ; ret w.
Compute run c3.
Definition c4 := z <- new (Nat_t 0) ; write z (Nat_t z) ;; ret z.
Compute run c4.
Definition c5 := free 1.
Compute run c5.
Definition c6 := x <- new (Nat_t 0) ; free x ;; read x.
Compute run c6.
Definition c7 := 
  x <- new (Nat_t 0) ; 
  (if le_gt_dec x 10 then free x else ret tt) ;;
  z <- new (Nat_t 0) ; 
  (if le_gt_dec x 10 then ret (Nat_t 42) else read x).
(** Does c7 succeed? Notice that the two [if] expressions have the same guard
    expression. *)

(** Some example proofs that these commands have specifications -- 
    one way to view this is that we are building commands and
    inferring specifications for them, fully automatically! *)
Definition p1 := ret_tc 0.
Check p1.

(** Unfortunately, the specifications that we calculate are 
    rather unwieldy.  Even these simple proofs yield default
    specifications that are impossible to read. *)
Definition p2 := x <-- ret_tc 0 ; y <-- ret_tc 1 ; ret_tc (x+y).
Check p2.

Definition p3 := z <-- new_tc (Nat_t 0) ; w <-- read_tc z ; ret_tc w.
Check p3.

Definition p4 := z <-- new_tc (Nat_t 0) ; write_tc z (Nat_t z) ;;; ret_tc z.
Check p4.

Definition p5 := free_tc 1.
Check p5.

Definition p6 := x <-- new_tc (Nat_t 0) ; free_tc x ;;; read_tc x.
Check p6.

Definition p7 := 
  x <-- new_tc (Nat_t 0) ; 
  (if_tc (le_gt_dec x 10) (free_tc x) (ret_tc tt)) ;;;
  z <-- new_tc (Nat_t 0) ; 
  (if_tc (le_gt_dec x 10) (ret_tc (Nat_t 42)) (read_tc x)).
Check p7.

(** More generally, we can write a function, like swap, and give
    it a human-readable specification.  Then we can use the 
    combinators to build most of the proof, and all we are left 
    with are the two verification conditions from the rule of consequence.  
*)
Definition swap x y := xv <- read x ; yv <- read y ; write x yv ;; write y xv.

(** We first prove a key lemma from the "McCarthy" axioms of 
    memory that allows us to reason about updates when two 
    pointers are different. *)
Lemma lookup_remove_other : forall h p1 p2, p1 <> p2 -> 
  lookup h p2 = lookup (remove h p1) p2.
Proof.
  induction h ; repeat mysimp. 
Qed.  

Lemma lookup_insert_other : forall h p1 v p2, p1 <> p2 -> 
  lookup h p2 = lookup (insert h p1 v) p2.
Proof.
  induction h ; repeat mysimp ; 
  match goal with 
    | [ |- context[le_gt_dec ?p1 ?p2] ] => destruct (le_gt_dec p1 p2)
  end ; repeat mysimp.
Qed.  

Lemma lookup_insert :  forall h p v,
  lookup (insert h p v) p = Some v.
Proof.
  induction h; repeat mysimp.
  match goal with 
    | [ |- context[le_gt_dec ?p1 ?p2] ] => destruct (le_gt_dec p1 p2)
  end ; repeat mysimp.
Qed.

(** Then we build a tactic that simplifies memory lookups *)
Ltac s := 
  match goal with
    | [ H : ?y <> ?x |- context[lookup (remove ?h ?x) ?y] ] => 
      rewrite <- (@lookup_remove_other h x y) ; [ auto | try congruence]
    | [ H : ?y <> ?x |- context[lookup (insert ?h ?x ?v) ?y] ] => 
      rewrite <- (@lookup_insert_other h x v y) ; [ auto | try congruence]
    | [ |- context [lookup (insert ?h ?x ?v) ?x] ] => 
        rewrite (lookup_insert h x v)
    | _ => mysimp ; simpl in * ; subst ; try congruence ; auto 
  end.
Ltac memsimp := repeat progress (s ; intros).

(** Finally, we build the proof that swap has the following nice
    specification. *)
Definition swap_tc x y :
  {{fun h => lookup h x <> None /\ lookup h y <> None}}
  swap x y
  {{fun h _ h' => lookup h' y = lookup h x /\ lookup h' x = lookup h y}}.
Proof.
  refine (consequence_tc 
             (xv <-- read_tc x ;
              yv <-- read_tc y ;
              write_tc x yv ;;;
              write_tc y xv) _ _).
  unfold precomp ; memsimp. 
  destruct (ptr_eq_dec y x) ; memsimp.
  unfold postcomp ; memsimp.
  destruct (ptr_eq_dec x y) ; memsimp.
Defined.

Definition c := 
  x <- new (Nat_t 0) ; y <- new (Nat_t x) ; z <- new (Nat_t 3) ; v <- read y ; swap z y.

Definition c_tc : 
  {{ top }}
  c
  {{ fun _ _ => top }}.
  refine (consequence_tc 
           (x <-- new_tc (Nat_t 0) ; 
            y <-- new_tc (Nat_t x) ; 
            z <-- new_tc (Nat_t 3) ; 
            v <-- read_tc y ; 
            swap_tc z y) _ _).
  unfold precomp. memsimp.
  destruct (ptr_eq_dec x0 x1) ; memsimp.
  unfold postcomp. memsimp.
Defined.

(** We might like to add a new command that reads out a number
    or that reads out a pair. *)
Definition read_nat (p:ptr) : Cmd nat := 
  v <- read p ; 
  match v with 
    | Nat_t n => ret n
    | _ => exit _
  end.

Definition read_pair (p:ptr) : Cmd (U*U) := 
  v <- read p ; 
  match v with
    | Pair_t x y => ret (x,y)
    | _ => exit _
  end.

(** We can define appropriate proof rules for these now. *)
Definition read_nat_tc (p:ptr) : 
  {{ fun h => exists n, lookup h p = Some (Nat_t n) }}
  read_nat p
  {{ fun h v h' => h = h' /\ lookup h p = Some (Nat_t v) }}.
Proof.
  unfold read_nat ; mysimp ; destruct (lookup h p) ; mysimp ; congruence.
Qed.

Definition read_pair_tc (p:ptr) : 
  {{ fun h => exists us, lookup h p = Some (Pair_t (fst us) (snd us)) }}
  read_pair p
  {{ fun h v h' => h = h' /\ lookup h p = Some (Pair_t (fst v) (snd v)) }}.
Proof.
  unfold read_pair ; mysimp ; destruct (lookup h p) ; mysimp ; congruence.
Qed.

(** Now we can prove that the following code will not get stuck. *)  
Definition alloc_and_swap := 
  x <- new (Nat_t 0) ; y <- new (Pair_t (Nat_t 1) (Nat_t 2)) ; swap x y ;; 
  read_nat y.

(** Here is the proof... *)
Definition alloc_and_swap_tc : {{ top }} alloc_and_swap {{ fun _ _ => top }}.
  refine (
    consequence_tc
      (x <-- new_tc (Nat_t 0) ;
       y <-- new_tc (Pair_t (Nat_t 1) (Nat_t 2)) ; 
       swap_tc x y ;;;
       read_nat_tc y) _ _) ; 
  unfold precomp, postcomp ; memsimp.
  destruct (ptr_eq_dec x x0) ; memsimp.
  rewrite H4. destruct (ptr_eq_dec x x0) ; memsimp ; eauto.
  rewrite lookup_insert in H2. congruence.
Defined.

(** Print out the proof -- it's huge!  *)

(** We can even define loops and infer pre- and post-conditions for them,
    thanks to our ability to define predicates inductively.  Here, we 
    define a loop that iterates [n] times a command [body]. *)
Definition iter(t:Type)(body: t -> Cmd t) : nat -> t -> Cmd t := 
  fix loop(n:nat) : t -> Cmd t := 
  match n with 
    | 0 => body
    | S n => fun x => v <- body x ; loop n v
  end.

(** The pre-condition for the loop can be computed by composing the
    pre-condition of the body [P] with its post-condition [Q] using
    the [precomp] predicate transformer. *)
Definition iter_precomp(t:Type)(P:t->hprop)(Q:t->heap->t->hprop): nat->t->hprop := 
  fix loop(n:nat) : t->hprop := 
  match n with 
    | 0 => P
    | S n => fun x => precomp (P x) (Q x) (loop n)
  end.

(** The post-condition for the loop can be computed by composing the
    post-condition of the body [Q] with itself, using the [postcomp]
    predicate transformer. *)
Definition iter_postcomp(t:Type)(Q:t->heap->t->hprop) : nat->t->heap->t->hprop := 
  fix loop(n:nat) : t -> heap -> t -> hprop := 
  match n with 
    | 0 => Q
    | S n => fun x => postcomp (Q x) (loop n)
  end.

(** Finally, if we can show that a loop body has pre-condition [P] and
    post-condition [Q], then we can conclude that iterating the body [n]
    times results in a command with pre-condition obtained by 
    [iter_precomp P Q] and post-condition obtained by [iter_postcomp Q]. *)
Lemma iter_tc {t:Type} {P} {Q} {body} : 
  (forall x:t, {{ P x }} body x {{ Q x }}) -> 
  forall n x, 
    {{ fun h => iter_precomp P Q n x h }}
    iter body n x
    {{ fun h v h' => iter_postcomp Q n x h v h' }}.
Proof.
  induction n ; simpl ; auto.
  intro. 
  apply (@bind_tc t t (body x) (iter body n) _ _ _ _ (H x)). 
  intro.
  apply (consequence_tc (IHn x0)) ; auto.
Qed.

Definition chain n := 
  v <- new (Nat_t 0) ; iter (fun x => new (Nat_t x)) n v.

Definition chain_tc n := 
  v <-- new_tc (Nat_t 0) ; iter_tc (fun x => new_tc (Nat_t x)) n v.
       

(** ** The problem with Hoare logic. *)

(** One problem with Hoare logic is that it doesn't support abstraction
    very well.  Consider the following situation: We first define an
    increment function and then give it a specification. *)
Definition inc (p:ptr) := v <- read_nat p ; write p (Nat_t (1 + v)).

(** The specification tells us that if [p] points to [n], then running
    [inc p] results in a state where [p] points to [1+n].  *)
Definition inc_tc (p:ptr) : 
  {{ fun h => exists n, lookup h p = Some (Nat_t n) }}
  inc p 
  {{ fun h1 _ h2 => exists n, (lookup h1 p = Some (Nat_t n) /\ 
                               lookup h2 p = Some (Nat_t (1 + n))) }}.
Proof.
  unfold inc.
  eapply consequence_tc.
  eapply bind_tc.
  eapply (read_nat_tc p).
  intros x.
  eapply (write_tc p (Nat_t (1 + x))).
  memsimp.
  memsimp.
Qed.

(** Now consider where we have two points, and some information about
    both of the pointers.  Unfortunately, our specification for [inc]
    is too weak to allow us to recover the fact that [p2] still points
    to some number, so we'll no longer be able to dereference it! *)
Definition problem (p1 p2:ptr) : 
  {{ fun h => (exists n1, lookup h p1 = Some (Nat_t n1)) /\ 
              (exists n2, lookup h p2 = Some (Nat_t n2)) }}
  inc p1
  {{ fun h1 _ h2 => 
       (exists n1, lookup h1 p1 = Some (Nat_t n1) /\ lookup h2 p1 = Some (Nat_t (1+n1)))
       (* /\ (exists n2, lookup h2 p2 = Some (Nat_t n2)) *) }}.
Proof.
  eapply consequence_tc.
  eapply (inc_tc p1).
  memsimp.
  memsimp.
Qed.

(** The problem is even more compounded when we use abstract predicates,
    which are necessary to get at the notion of abstract types.  Here, 
    the [inc] provider has no way to anticipate what properties [P] might
    be preserved by [inc], since [P] could talk about any property of the
    heap. *)
Definition problem2 (p1:ptr)(P:hprop) : 
  {{ fun h => (exists n1, lookup h p1 = Some (Nat_t n1)) /\ P h }}
  inc p1
  {{ fun h1 _ h2 => 
       (exists n1, lookup h1 p1 = Some (Nat_t n1) /\ lookup h2 p1 = Some (Nat_t (1+n1)))
       (* /\ P h2 *) }}.
Proof.
  eapply consequence_tc.
  eapply (inc_tc p1).
  memsimp.
  memsimp.
Qed.

*)



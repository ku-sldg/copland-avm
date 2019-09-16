Require Import Term Instr.
Require Import MyStack.

Require Import List.
Import ListNotations.

(* Generalized State Monad *)
Definition St(S A : Type) : Type := S -> (option A) * S % type.

Definition ret {S A : Type} (a : A) : St S A := fun s => (Some a, s).

Definition bind {S A B : Type} (m : St S A) (f : A -> St S B) : St S B :=
  fun s =>
    let '(a, s') := m s in
    match a with
    | Some v =>
      let '(b, s'') := f v s' in
      (b, s'')
    | _ => (None,s')
    end.

Definition failm {S A : Type} : St S A := fun s => (None, s).
      

(* alias for ret *)
(*Definition write_output {S O} (o : O) : GenHandler1 S O := ret o.*)

Definition modify {S} (f : S -> S) : St S unit := fun s => (Some tt, f s).

Definition put {S} (s : S) : St S unit := fun _ => (Some tt, s).

Definition get {S} : St S S := fun s => (Some s, s).

Definition runSt {S A} (s : S) (h : St S A) :
  (option A) * S % type :=
  h s.

Definition nop {S : Type} := @ret S _ tt.

Notation "a >> b" := (bind a (fun _ => b)) (at level 50).

Notation "x <- c1 ;; c2" := (@bind _ _ _ c1 (fun x => c2))
                              (at level 100, c1 at next level, right associativity).

Notation "e1 ;; e2" := (_ <- e1 ;; e2)
                         (at level 100, right associativity).

Definition when {S A} (b : bool) (m : St S A) : St S unit :=
  if b then m ;; ret tt else nop.

Ltac monad_unfold :=
  repeat unfold
         runSt,
         bind,
         (*write_output,*)
         get,
         when,
         put,
         nop,
         modify,
         ret in *.



(* Specific VM monad *)
Definition ev_stack := gen_stack EvidenceC.
Record vm_st : Type := mk_vm_st
                         {st_stack:ev_stack ;
                          st_trace:list Ev}.

Definition VM := St vm_st.
(*Definition runVM{A:Type} := @runSt vm_config A.*)

(* Sanity checks *)
Definition extractVal (r:vm_st) : nat :=
  let ev := head (st_stack r) in
  let n :=
      match ev with
        | Some (ggc _ n) => n
        | _ => 0
      end in
  n + 1.

Definition test_comp : VM unit :=
  v <- get ;;
    let n := extractVal v in
    put (mk_vm_st [(ggc mtc n)] []) ;;
        ret tt.

Definition empty_vm_state := mk_vm_st [(ggc mtc 48)] [].

Compute (runSt empty_vm_state test_comp).

(* VM monad operations *)
Definition push_stackr (e:EvidenceC) : VM unit :=
  st <- get ;;
     let oldStack := st_stack st in
     let newStack := push_stack _ e oldStack in
     put (mk_vm_st newStack (st_trace st)).

Definition pop_stackr : VM EvidenceC :=
  st <- get ;;
     let oldStack := st_stack st in
     let maybePopped := pop_stack _ oldStack in
     match maybePopped with
     | Some (e,s') =>
       put (mk_vm_st s' (st_trace st)) ;;
           ret e
     | None => failm
     end.
       

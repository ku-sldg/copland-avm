Require Import Term Instr.
Require Import MyStack.

Require Import List.
Import ListNotations.

Definition ev_stack := gen_stack EvidenceC.

(* Generalized State Monad *)
Definition St(S A : Type) : Type := S -> A * S % type.

Definition ret {S A : Type} (a : A) : St S A := fun s => (a, s).

Definition bind {S A B : Type} (m : St S A) (f : A -> St S B) : St S B :=
  fun s =>
    let '(a, s') := m s in
    let '(b, s'') := f a s' in
    (b, s'').

(* alias for ret *)
(*Definition write_output {S O} (o : O) : GenHandler1 S O := ret o.*)

Definition modify {S} (f : S -> S) : St S unit := fun s => (tt, f s).

Definition put {S} (s : S) : St S unit := fun _ => (tt, s).

Definition get {S} : St S S := fun s => (s, s).

Definition runSt {S A} (s : S) (h : St S A) :
  A * S % type :=
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
Record vm_config : Type := mk_vm_config
                            { cec:EvidenceC ;
                              cvm_list:(list AnnoInstr) ;
                              cvm_stack:ev_stack }.

Definition VM := St vm_config.
(*Definition runVM{A:Type} := @runSt vm_config A.*)

Definition extractVal (r:vm_config) : nat :=
  let ev := cec r in
  let n :=
      match ev with
        | ggc _ n => n
        | _ => 0
      end in
  n + 1.

Definition test_comp : VM unit :=
  v <- get ;;
    let n := extractVal v in
  put (mk_vm_config (ggc mtc n) [] []).

Definition empty_vm_state := mk_vm_config (ggc mtc 46) [] [].

Compute (runSt empty_vm_state test_comp).

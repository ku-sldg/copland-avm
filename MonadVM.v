Require Import Term ConcreteEvidence Instr GenStMonad.
Require Import MyStack.
Require Import Maps.

Require Import List.
Import ListNotations.

Require Export StVM.

Print vm_st.


Definition VM := St vm_st.
(*Definition runVM{A:Type} := @runSt vm_config A.*)

(* Sanity checks *)


Definition extractVal (r:vm_st) : nat :=
  let ev := head (st_stack r) in
  let n :=
      match ev with
        | Some (ggc n _) => n
        | _ => 0
      end in
  n + 1.

Definition test_comp : VM unit :=
  v <- get ;;
    let n := extractVal v in
    put (mk_st mtc [(ggc n mtc)] [] 0 []) ;;
        ret tt.

Definition empty_vm_state := mk_st mtc [(ggc 48 mtc)] [] 0 [].

Compute (runSt empty_vm_state test_comp).

(* VM monad operations *)

Definition push_stackm (e:EvidenceC) : VM unit :=
  st <- get ;;
     let '{| st_ev := oldEv; st_stack := oldStack; st_trace := tr; st_pl := oldP; st_store := oldStore |} := st in
     let newStack := push_stack _ e oldStack in
     put (mk_st oldEv newStack tr oldP oldStore).

Definition pop_stackm : VM EvidenceC :=
  st <- get ;;
     let '{| st_ev := oldE; st_stack := oldStack; st_trace := tr; st_pl := oldP; st_store := oldStore |} := st in
     (*let oldStack := st_stack st in*)
     let maybePopped := pop_stack _ oldStack in
     match maybePopped with
     | Some (e,s') =>
       put (mk_st oldE s' tr oldP oldStore) ;;
           ret e
     | None => failm
     end.

Definition put_store (n:nat) (e:EvidenceC) : VM unit :=
  st <- get ;;
     let e' := st_ev st in
     let s' := st_stack st in
     let tr' := st_trace st in
     let p' := st_pl st in
     let store' := st_store st in
  (*let '{| st_ev := _; st_stack := s; st_trace := tr |} := st in*)
     put (mk_st e' s' tr' p' (map_set store' n e)).

Definition get_store_at (n:nat) : VM EvidenceC :=
  st <- get ;;
     let store' := st_store st in
     let maybeEv := map_get store' n in
     match maybeEv with
     | Some e => ret e
     | None => failm
     end.

Definition put_ev (e:EvidenceC) : VM unit :=
  st <- get ;;
     let s' := st_stack st in
     let tr' := st_trace st in
     let p' := st_pl st in
     let store' := st_store st in
  (*let '{| st_ev := _; st_stack := s; st_trace := tr |} := st in*)
    put (mk_st e s' tr' p' store').

Definition get_ev : VM EvidenceC :=
  st <- get ;;
     ret (st_ev st).

Definition get_pl : VM Plc :=
  st <- get ;;
  ret (st_pl st).

Definition modify_evm (f:EvidenceC -> EvidenceC) : VM unit :=
  st <- get ;;
  let '{| st_ev := e; st_stack := s; st_trace := tr; st_pl := p; st_store := store |} := st in
  put (mk_st (f e) s tr p store).

Definition add_trace (tr':list Ev) : vm_st -> vm_st :=
  fun '{| st_ev := e; st_stack := s; st_trace := tr; st_pl := p; st_store := store |} =>
    mk_st e s (tr ++ tr') p store.

Definition add_tracem (tr:list Ev) : VM unit :=
  modify (add_trace tr).

Definition split_evm (i:nat) (sp1 sp2:SP) (e:EvidenceC) (p:Plc) : VM (EvidenceC*EvidenceC) :=
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    add_tracem [Term.split i p] ;;
               ret (e1,e2).

       
Ltac monad_unfold :=
  repeat unfold
         runSt,
  execSt,
  (*push_stackm,
  pop_stackm, *)
  (*push_stack,
  pop_stack, *)
  get_ev,
  get_pl,
  add_tracem,
  modify_evm,
  split_evm,
  add_trace,
  
  
  bind,
  (*write_output,*)
  get,
  when,
  put,
  nop,
  modify,
  ret in *;
  simpl in *.
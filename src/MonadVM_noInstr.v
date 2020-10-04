(*
Definition of the AVM Monad + monadic helper functions.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Term ConcreteEvidence GenStMonad.
Require Import MyStack Maps.

Require Import List.
Import ListNotations.

Require Import StructTactics.

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
Check modify.
Print modify.

Definition split_evm (i:nat) (sp1 sp2:SP) (e:EvidenceC) (p:Plc) : VM (EvidenceC*EvidenceC) :=
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    add_tracem [Term.split i p] ;;
               ret (e1,e2).

(*
Definition prim_trace (i:nat) (p:Plc) (a:Prim_Instr) : (list Ev) :=
  match a with
  | copy => [Term.copy i p]
  | umeas asp_id => [Term.umeas i p asp_id]
  | sign => [Term.sign i p]
  | hash => [Term.hash i p]
  end.
 *)

(*
Definition prim_ev (a:Prim_Instr)(* (p:Plc) *) (e:EvidenceC) : EvidenceC :=
  match a with
  | copy => e
  | umeas i =>
    let bs := invokeUSM i in
    (uuc i bs e)
  | sign =>
    let bs := signEv e in
    (ggc bs e)
  | hash =>
    let bs := hashEv e in
    (hhc bs e)
  end. 
*)

(** * Place-holder axioms for IO operations *)
(* Definition invokeKIM (i:ASP_ID) (q:Plc) (*(args:list Arg)*) : BS. 
Admitted. *)
Print BS.
Definition BS_res : BS.
Admitted.

Check put_ev.

Definition invokeUSM (x:nat) (i:ASP_ID) (p:Plc) : VM EvidenceC :=
  e <- get_ev ;;
  add_tracem [Term.umeas x p i];;
  ret (uuc i BS_res e).

Definition signEv (x:nat) (p:Plc) : VM EvidenceC :=
  e <- get_ev ;;
  add_tracem [Term.sign x p] ;;
  ret (ggc BS_res e).

Definition hashEv (x:nat) (p:Plc) : VM EvidenceC :=
  e <- get_ev ;;
  add_tracem [Term.hash x p] ;;
  ret (hhc BS_res e).

Definition copyEv (x:nat) (p:Plc) : VM EvidenceC :=
  add_tracem [Term.copy x p] ;;
  get_ev.


Definition remote_events (t:AnnoTerm) (p:Plc) : (list Ev).
Admitted.

Definition toRemote (t:Term) (pTo:Plc) (e:EvidenceC) : EvidenceC.
Admitted.
Definition parallel_eval_thread (t:Term) (e:EvidenceC) : EvidenceC.
Admitted.

Definition sendReq (reqi:nat) (q:Plc) (t:AnnoTerm) : VM unit :=
  p <- get_pl ;;
  add_tracem [req reqi p q (unanno t)].

Definition doRemote (t:AnnoTerm) (q:Plc) (e:EvidenceC) (rpyi:nat) : VM unit :=
  add_tracem (remote_events t q) ;;
  put_store rpyi (toRemote (unanno t) q e).

Definition receiveResp (rpyi:nat) (q:Plc) : VM EvidenceC :=
  e <- get_store_at rpyi ;;
  p <- get_pl ;;
  add_tracem [rpy (Nat.pred rpyi) p q] ;;
  ret e.



Definition do_prim (x:nat) (p:Plc) (a:ASP) : VM EvidenceC :=
  match a with
  | CPY => copyEv x p
  | ASPC asp_id =>
    invokeUSM x asp_id p
  | SIG => signEv x p
  | HSH => hashEv x p
  end.



Definition eval_asp (a:ASP) (e:EvidenceC) : EvidenceC :=
  match a with
  | CPY => e
(*  | KIM i q args =>
    let bs := invokeKIM i q args in
    (kkc i args q bs e) *)
  | ASPC i =>
    let bs := BS_res in
    (uuc i bs e)
  | SIG =>
    let bs := BS_res in
    (ggc bs e)
  | HSH =>
    let bs := BS_res in
    (hhc bs e)
  end.



Fixpoint eval (t:Term) (* (p:Plc) *) (e:EvidenceC) : EvidenceC :=
  match t with
  | asp a => eval_asp a e
  | att q t1 => toRemote t1 q e
  | lseq t1 t2 =>
    let e1 := eval t1 e in
    eval t2 e1
         
  | bseq (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := eval t1 e1 in
    let e2' := eval t2 e2 in
    (ssc e1' e2') 
  | bpar (sp1,sp2) t1 t2 =>
    let e1 := splitEv sp1 e in
    let e2 := splitEv sp2 e in
    let e1' := parallel_eval_thread t1 e1 in
    let e2' := parallel_eval_thread t2 e2 in
    (ppc e1' e2')
  end.

Axiom remote_eval : forall e p annt,
    eval annt e = toRemote annt p e.

Axiom para_eval_thread: forall e annt,
    parallel_eval_thread annt e = eval annt e.


Inductive evalR: Term -> EvidenceC -> EvidenceC -> Prop :=
| mttc: forall e, evalR (asp CPY) e e
| uutc: forall i e,
    evalR (asp (ASPC i)) e (uuc i (BS_res) e)
| ggtc: forall e,
    evalR (asp SIG) e (ggc BS_res e)
| hhtc: forall e,
    evalR (asp HSH) e (hhc BS_res e)
| atc: forall q t' e e',
    evalR t' e e' ->
    evalR (att q t') e e'
| lseqc: forall t1 t2 e e' e'',
    evalR t1 e e' ->
    evalR t2 e' e'' ->
    evalR (lseq t1 t2) e e''
| bseqc: forall t1 t2 sp1 sp2 e e1 e2,
    evalR t1 (splitEv sp1 e) e1 ->
    evalR t2 (splitEv sp2 e) e2 ->
    evalR (bseq (sp1,sp2) t1 t2) e (ssc e1 e2)
| bparc: forall t1 t2 sp1 sp2 e e1 e2,
    evalR t1 (splitEv sp1 e) e1 ->
    evalR t2 (splitEv sp2 e) e2 ->
    evalR (bpar (sp1,sp2) t1 t2) e (ppc e1 e2).



Lemma eval_iff_evalR: forall t e e',
    evalR t e e' <-> eval t e = e'.
Proof.
    split.
  - (* -> case *)
    intros.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros.

    + destruct a; try (inv H; reflexivity).
    + inv H. simpl.
      rewrite <- remote_eval.
      eauto.
    + inv H.
      assert (eval t1 e = e'0).
      eauto.
      subst.
      simpl.
      eauto.
    + inv H.
      assert (eval t1 (splitEv sp1 e) = e1) by eauto.
      assert (eval t2 (splitEv sp2 e) = e2) by eauto.
      simpl.
      destruct sp1; destruct sp2;
        simpl; subst; eauto.
    + inv H.
      assert (eval t1 (splitEv sp1 e) = e1) by eauto.
      assert (eval t2 (splitEv sp2 e) = e2) by eauto.
      simpl.
      repeat rewrite para_eval_thread in *.
      destruct sp1; destruct sp2;
        simpl; subst; eauto.
  - (* <- case *)
    intros.
    generalize dependent e.
    generalize dependent e'.

    induction t; intros.
    + inv H.
      destruct a; try econstructor.
    + inv H.
      simpl.
      econstructor.
      rewrite <- remote_eval.
      eauto.
    + econstructor; eauto.
    + destruct s.
      simpl in H.
      destruct s; destruct s0; simpl in *; subst;
        econstructor; (try simpl); eauto; try (econstructor).
    + destruct s.
      simpl in H.
      repeat rewrite para_eval_thread in *.
      destruct s; destruct s0; simpl in *; subst;
        econstructor; (try simpl); eauto; try (econstructor).
Defined.
      
Ltac monad_unfold :=
  repeat unfold
  execSt,  
  do_prim,
  invokeUSM,
  signEv,
  hashEv,
  copyEv,

  sendReq,
  doRemote,
  receiveResp,

  
  get_ev,
  get_pl,
  add_tracem,
  modify_evm,
  split_evm,
  add_trace,
  failm,
  (* Uncommenting these evaluates too much, can't apply lemmas *)
  (*push_stackm,
  pop_stackm, *)
  (*push_stack,
  pop_stack, *)
  (*get_store_at,*)
  get,
  when,
  put,
  nop,
  modify,
  bind,
  ret in *;
  simpl in *.

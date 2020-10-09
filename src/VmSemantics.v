(*
Implementation of the Attestation Virtual Machine (AVM) + proof that it refines the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Preamble Term ConcreteEvidence LTS GenStMonad.
Require Import Main Event_system Term_system.


Require Import MyStack MonadVM MonadVMFacts.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.


Set Nested Proofs Allowed.

(** IO Axioms *)

Definition parallel_att_vm_thread (t:AnnoTerm) (e:EvidenceC) : EvidenceC.
Admitted.

Definition parallel_vm_events (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Definition shuffled_events (el1:list Ev) (el2:list Ev) : list Ev.
Admitted.

Fixpoint build_comp (t:AnnoTerm): VM unit :=
  match t with
  | aasp (n,_) a =>
    p <- get_pl ;;
    e <- do_prim n p a ;;
    put_ev e
  | aatt (reqi,rpyi) q t' =>
    sendReq reqi q t' ;;
    e <- get_ev ;;
    doRemote t' q e rpyi ;;
    e' <- receiveResp rpyi q ;;
    put_ev e'
  | alseq r t1 t2 =>
    build_comp t1 ;;
    build_comp t2 (* TODO: does evidence work out ok? *)
  | abseq (x,y) (sp1,sp2) t1 t2 =>
    e <- get_ev ;;
    p <- get_pl ;;
    pr <- split_evm x sp1 sp2 e p ;;
    let '(e1,e2) := pr in
    put_ev e1 ;;
    build_comp t1 ;;
    e1r <- get_ev ;;
    put_ev e2 ;;
    build_comp t2 ;;
    e2r <- get_ev ;;
    put_ev (ssc e1r e2r) ;;
    add_tracem [Term.join (Nat.pred y) p]
(*

  | abseq (x,y) (sp1,sp2) t1 t2 =>
    e <- get_ev ;;
    p <- get_pl ;;
    pr <- split_evm x sp1 sp2 e p ;;
    let '(e1,e2) := pr in
    put_ev e1 ;;
    push_stackm e2 ;;
    build_comp t1 ;;
    e <- get_ev ;;
    er <- pop_stackm ;; (* TODO:  is stack still necessary? *)
    put_ev er ;;
    push_stackm e ;;
    build_comp t2 ;;
    er' <- pop_stackm ;;
    er'' <- get_ev ;;
    put_ev (ssc er' er'') ;;
    add_tracem [Term.join (Nat.pred y) p]
*)
  | abpar (x,y) (sp1,sp2) t1 t2 =>
    e <- get_ev ;;
    p <- get_pl ;;
    pr <- split_evm x sp1 sp2 e p ;;
    let '(e1,e2) := pr in
    let res1 := parallel_att_vm_thread t1 e in
    (* TODO: change this to a monadic function that consults an environment that is aware of the presence (or absence) of parallel avm threads.  Put initial evidence in store, let environment run the parallel thread and place result evidence, then query for result evidence here. *)
    let res2 := parallel_att_vm_thread t2 e2 in
    let el1 := parallel_vm_events t1 p in
    let el2 := parallel_vm_events t2 p in
    let loc1 := fst (range t1) in
    let loc2 := fst (range t2) in
    put_store loc1 res1 ;;
    put_store loc2 res2 ;;
    add_tracem (shuffled_events el1 el2) ;;
    e1r <- get_store_at loc1 ;;
    e2r <- get_store_at loc2 ;;
    put_ev (ppc e1r e2r) ;;
    add_tracem [Term.join (Nat.pred y) p]
  end.

(** Function-style semantics for VM *)

(*
(* Transform vm_st for a single instruction (A -> B -> A) function for fold_left *)
Definition run_vm_step (a:vm_st) (b:AnnoInstr) : vm_st :=
  execSt a (build_comp b).

Definition run_vm (il:list AnnoInstr) st : vm_st :=
  fold_left (run_vm_step) il st.

Definition run_vm_t (t:AnnoTerm) st : vm_st :=
  run_vm (instr_compiler t) st.
 *)

Definition run_vm (t:AnnoTerm) st : vm_st :=
  execSt st (build_comp t).

Lemma st_congr :
  forall st tr e p o,
    st_ev st = e ->
    st_trace st = tr ->
    st_pl st = p ->
    st_store st = o ->
    st =  {| st_ev := e; st_trace := tr; st_pl := p; st_store := o |}.
Proof.
  intros.
  subst; destruct st; auto.
Defined.

Ltac unfoldm :=  (*repeat unfold run_vm_step in *;*) monad_unfold.

Ltac boom :=
  repeat unfoldm;
  repeat (desp; unfoldm);
  (*try_pop_all; *)
  vmsts.

Ltac do_run :=
  match goal with
  | [H:  run_vm _ _ = _ |- _ ] => invc H; (*unfold run_vm_step in *;*) repeat monad_unfold
  end.

Ltac allss :=
  repeat find_inversion;
  try bogus;
  repeat (do_get_store_at_facts; subst; eauto);
  repeat (do_get_store_at_facts_fail; subst; eauto);
 (* repeat do_flip;
  repeat do_pop_stackm_facts;
  repeat do_pop_stackm_fail; *)
  repeat get_store_at_bogus;
  try do_bd;
  subst; eauto.

Ltac fail_if_in_hyps H := 
  let t := type of H in 
  lazymatch goal with 
  | [G : t |- _ ] => fail "There is already a hypothesis of this proof"
  | [_ : _ |- _ ] => idtac
  end.

Ltac pose_new_proof H := 
  fail_if_in_hyps H;
  pose proof H.

Ltac fail_if_in_hyps_type t := 
  lazymatch goal with 
  | [G : t |- _ ] => fail "There is already a hypothesis of this type"
  | [_ : _ |- _ ] => idtac
  end.

Ltac assert_new_proof_by H tac := 
  fail_if_in_hyps_type H;
  assert H by tac.
    
Ltac dunit :=
  match goal with
  | [H:unit |- _] => destruct H
  end.

Ltac annogo :=
  match goal with
  | [H: _ = snd (anno ?t' _) |- _] =>
    vmsts; repeat dunit;
    destruct t';
    try (inv H; tauto);
    simpl in *;
    repeat break_let;
    simpl in *;
    inv H
  end.

Ltac anhl :=
  match goal with
  | [H: anno _ _ = (_, ?a),
     H2: build_comp ?a _ = _,
     H3: build_comp ?a _ = _,
     IH: context[?a = _ -> _] |- _] =>
    edestruct IH;
    [(rewrite H; reflexivity) |
     apply H2 | apply H3 | idtac]; clear H2; clear H3;
    destruct_conjs; subst
  end.

Lemma h : forall a b t1 t2 t n,
    abpar a b t1 t2 = snd (anno t n) ->
    (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false).
Proof.
  intros.
  destruct a; destruct b.
  assert ( (fst (range t1)) <> (fst (range t2))).
  { eapply afaf; eauto. }
  rewrite PeanoNat.Nat.eqb_neq.
  assumption.
Defined.

Ltac htac :=
  let tac := eapply h; eauto in
  match goal with
  | [H: abpar _ _ ?t1 ?t2 = snd _ |- _] =>
    let X := fresh in
    assert (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false) as X by tac; rewrite X in *; clear X
  end.

Ltac dohtac := try htac;
               try rewrite PeanoNat.Nat.eqb_refl in *;
               try rewrite PeanoNat.Nat.eqb_eq in *.

Lemma hihi : forall t t' n e e' e'' x x' y y' p p' p'' o o' o'',
    t = snd (anno t' n) -> 
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x'; st_pl := p'; st_store := o' |}) ->
    build_comp t {| st_ev := e; st_trace := y; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := y'; st_pl := p''; st_store := o'' |}) ->
    (e' = e'' /\ p' = p'' /\ o' = o'').
Proof.
  induction t; intros.
  - destruct a; 
      simpl in *;
      repeat break_let;
      monad_unfold;
      repeat find_inversion;
      auto.
  - simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    dohtac.
    repeat find_inversion.
    auto.
  -
    simpl in *;
    monad_unfold;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.

    annogo.
    repeat anhl.
    eauto.
  -
    simpl in *.
    monad_unfold;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.

    annogo.
    repeat anhl.
    eauto.
  -
    simpl in *.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.
    monad_unfold.

    dohtac.
    
    repeat find_inversion.
    simpl in *.

    dohtac.

    repeat find_inversion.
    auto.
Defined.

Ltac dohi :=
  let tac := (eapply hihi; eauto) in
  match goal with
  | [H : build_comp ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_store := ?o |} =
         (?opt, {| st_ev := ?e'; st_trace := _; st_pl := ?p'; st_store := ?o' |}),
         H' : build_comp ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_store := ?o |} =
              (?opt, {| st_ev := ?e''; st_trace := _; st_pl := ?p''; st_store := ?o'' |}) |- _] =>
    assert_new_proof_by (e' = e'' /\ p' = p'' /\ o' = o'') tac
  end.

Lemma map_get_get(*{V:Type}`{forall x y : V, Dec (x = y)}*) :
  forall (k:nat) (v:EvidenceC) l',
    Maps.map_get ((k,v) :: l') k = Some v.
Proof.
  intros.
  simpl.
  break_match; eauto.
  rewrite PeanoNat.Nat.eqb_refl in Heqb. congruence.
Defined.

Lemma map_get_get_2(*{V:Type}`{forall x y : V, Dec (x = y)}*) :
  forall (k:nat) (v:EvidenceC) k' v' l',
    k <> k' ->
    Maps.map_get ((k',v') :: (k,v) :: l') k = Some v.
Proof.
  intros; simpl.
  break_if;
    dohtac; tauto.
Defined.

Ltac dohi' :=
  match goal with
  | [H: anno _ _ = (_, ?a),
        H2: build_comp ?a _ = _,
            H3: build_comp ?a _ = _(*,
                IH: context[?a = _ -> _]*) |- _] =>
    edestruct hihi;
    [(rewrite H; reflexivity) |
     repeat dunit; apply H2 | repeat dunit; apply H3 | idtac]; (*clear H2; clear H3;*)
    destruct_conjs; subst
  end.

Ltac jkjk :=
  match goal with
  | [H: context[?X] |- ?X = _] => rewrite H
  end.

Lemma fafaf : forall t t' n e e' e'' p p' p'' o o' o'' x y r s,
    t = snd (anno t' n) ->
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (None, {| st_ev := e'; st_trace := y; st_pl := p'; st_store := o' |}) ->
    build_comp t {| st_ev := e; st_trace := r; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := s; st_pl := p''; st_store := o'' |}) ->
    False.
Proof.
  
  induction t; intros.
  - destruct a;   
      simpl in *;
      break_let;
      monad_unfold;
      solve_by_inversion.

  - simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    monad_unfold.

    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    monad_unfold.
    repeat find_inversion.
  -  
    simpl in *.   
    repeat monad_unfold.   
    repeat break_match; try solve_by_inversion.
    +
      annogo.
      (*
      vmsts.
    repeat find_inversion.
    destruct t'; inv H;
      try (
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    simpl in *.
    repeat break_let.
    inv H.

    annogo. *)

      Check hihi.

      Print dohi.

      Check hihi.

(*

    Ltac dohi' :=
      let tac := (eapply hihi; eauto) in
      match goal with
      | [H : build_comp ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_store := ?o |} =
             (?opt, {| st_ev := ?e'; st_trace := _; st_pl := ?p'; st_store := ?o' |}),
             H' : build_comp ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_store := ?o |} =
                  (?opt, {| st_ev := ?e''; st_trace := _; st_pl := ?p''; st_store := ?o'' |}) |- _] =>
        assert_new_proof_by (e' = e'' /\ p' = p'' /\ o' = o'') tac
      end.
 *)
      
(*
      Ltac anhl :=
        match goal with
        | [H: anno _ _ = (_, ?a),
              H2: build_comp ?a _ = _,
                  H3: build_comp ?a _ = _,
                      IH: context[?a = _ -> _] |- _] =>
          edestruct IH;
          [(rewrite H; reflexivity) |
           apply H2 | apply H3 | idtac]; clear H2; clear H3;
          destruct_conjs; subst
        end.
 *)
      


      dohi'.



      (*
    edestruct hihi.
    rewrite Heqp4.
    reflexivity.
    
    repeat dunit.
    apply Heqp2.
    repeat dunit.
    apply Heqp0. *)
    repeat find_inversion.

    eapply IHt2; eauto.
    

    
    try jkjk; eauto.
    
    +
      annogo.   
      
      eapply IHt1; eauto.
      try jkjk; eauto.
  -
    (*
    destruct t'; inv H;
      try (
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    simpl in *.
    repeat break_let.
    inv H.
     *)
    annogo.

    
    simpl in *.
    repeat break_let.
    monad_unfold.
    
    repeat break_let.
    repeat find_inversion.
    repeat break_match;
      boom; allss.
    repeat dunit.

    dohi'.
    (*


     edestruct hihi.
     rewrite Heqp0.
     simpl. reflexivity.
     apply Heqp6.
     apply Heqp15.
     destruct_conjs; subst. *)
    
    eapply IHt2; eauto.
    try jkjk; eauto.

    (*
     rewrite Heqp1.
     simpl. reflexivity.
     eauto.
     eauto. *)
    repeat dunit.
    eapply IHt1; eauto.
    try jkjk; eauto.
    (*
    
     rewrite Heqp0.
     simpl. reflexivity.
     apply Heqp15. apply Heqp6. *)

     repeat dunit.
     eapply IHt1; eauto.
     jkjk; eauto.
     (*
     rewrite Heqp0.
     simpl. reflexivity.
     eassumption. eassumption.
      *)
     
     
  -
    simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    repeat break_match; 
      repeat find_inversion.
    vmsts.
    simpl in *.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    (*
    rewrite PeanoNat.Nat.eqb_refl in *.

    simpl in *.
    assert (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false) as H0.
     { assert ( (fst (range t1)) <> (fst (range t2))).
      {
        eapply afaf; eauto.
      }
      unfold PeanoNat.Nat.eqb.
      Search PeanoNat.Nat.eqb.
      rewrite PeanoNat.Nat.eqb_neq.
      assumption.
    }
    subst.
    rewrite H0 in *. *)
    repeat find_inversion.

    assert (Maps.map_get
              (Maps.map_set (Maps.map_set o (fst (range t1)) (parallel_att_vm_thread t1 st_ev1)) (fst (range t2))
                            (parallel_att_vm_thread t2 (splitEv s2 st_ev1))) (fst (range t2)) =
            Some (parallel_att_vm_thread t2 (splitEv s2 st_ev1))) as H1.
    {
      unfold Maps.map_set in *.
      apply map_get_get.
    }
    rewrite H1 in *.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    (*
    assert (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false) as H0.
         { assert ( (fst (range t1)) <> (fst (range t2))).
      {
        eapply afaf; eauto.
      }
      unfold PeanoNat.Nat.eqb.
      Search PeanoNat.Nat.eqb.
      rewrite PeanoNat.Nat.eqb_neq.
      assumption.
    }
    rewrite H0 in *.
    rewrite PeanoNat.Nat.eqb_refl in *. *)
    repeat find_inversion.
Defined.

Lemma fals : forall a t'1 n n0 e x y p o u v v' P,
    anno t'1 n = (n0, a) ->
    build_comp a
               {|
                 st_ev := e;
                 st_trace := x;
                 st_pl := p;
                 st_store := o |} = (None, v) ->
    build_comp a
               {|
                 st_ev := e;
                 st_trace := y;
                 st_pl := p;
                 st_store := o |} = (Some u, v') ->
    P.
Proof.
  intros.
  exfalso.
  vmsts.
  repeat dunit.
  eapply fafaf.
  Print jkjk.
  (*
  jkjk.
   *)
  
  rewrite H.
  simpl. reflexivity.
  simpl in *.
  eassumption.
  eassumption.
Defined.

(*
  Ltac build_contra :=
  match goal with
  | [H: build_comp ?a _ = (Some _,_),
  H2: build_comp ?a _ = (None,_) |- _] => eapply fals with (a:=a); eauto
  end.
  TODO:  does this exhibit a bug in Coq?  (Is there ever a case when one wants to use a name matched in a hypothesis as the LHS of a with clause?  Seems to me that the LHS should not be a free variable.
 *)

Ltac build_contra :=
  match goal with
  | [H: build_comp ?b {|
             st_ev := ?e;
             st_trace := _;
             st_pl := ?p;
             st_store := ?o |} = (Some _,_),
        H2: build_comp ?b {|
             st_ev := ?e;
             st_trace := _;
             st_pl := ?p;
             st_store := ?o |} = (None,_) |- _] => eapply fals with (a:=b); eauto
  end.

Lemma gen_foo : forall t t' n m k e p o v,
    t = snd (anno t' n) ->
    build_comp t
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |} =
    (Some tt, v) -> 
    st_trace
      (snd (build_comp t
                       {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |})) =
    m ++ st_trace (snd (build_comp t
                       {| st_ev := e; st_trace := k; st_pl := p; st_store := o |})).
Proof.
  induction t; intros.
  -
    destruct r.
    destruct a;
      simpl;
      repeat rewrite app_assoc;
      reflexivity.
  -
    simpl in *.
    repeat break_let.
    monad_unfold.
    destruct r.
    unfold get_store_at in *.
    monad_unfold.
    dohtac.
    (*
    rewrite PeanoNat.Nat.eqb_refl in *. *)
    repeat find_inversion.

    simpl.
    repeat rewrite app_assoc.
    reflexivity.
  -
    (*
    destruct t';
      try (
          inv H;
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    repeat break_let.
    simpl in *.
    repeat break_let.
    simpl in *.
    inv H.
     *)
    annogo.
    
    monad_unfold.

    
    destruct (build_comp a {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}) eqn:hey.
    vmsts.
    destruct o0; try solve_by_inversion.
    repeat break_let.
    vmsts.
    destruct o1; try solve_by_inversion; try build_contra.
    repeat find_inversion.
    destruct o2; try solve_by_inversion; try (dohi'; build_contra).
    
    repeat find_inversion.
    repeat dunit.
    (*destruct o0; try solve_by_inversion. *)
    simpl.
     
    (*repeat break_match; try solve_by_inversion. *)

(*    
Ltac dohi'' :=
  match goal with
  | [H: anno _ _ = (_, ?a),
        H2: build_comp ?a _ = _,
            H3: build_comp ?a _ = _(*,
                IH: context[?a = _ -> _]*) |- _] =>
    edestruct hihi;
    [(rewrite H; reflexivity) |
     simpl; repeat dunit; apply H2 | simpl; repeat dunit; apply H3 | idtac]; (*clear H2; clear H3;*)
    destruct_conjs; subst
  end.
*)

    dohi'.
    (*
    
    edestruct hihi.
    rewrite Heqp0. reflexivity.
    simpl.
    apply Heqp3.
    simpl.
    repeat dunit.
    apply hey.
    destruct_conjs; subst. *)

    assert (StVM.st_trace (
                snd (build_comp a {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}
              )) =
            m ++
              StVM.st_trace
              (snd (build_comp a {| st_ev := e; st_trace := k; st_pl := p; st_store := o |}))).
    eapply IHt1; eauto.
    try jkjk; eauto.
    (*
    rewrite Heqp0.
    simpl. reflexivity.
    eassumption. *)
    rewrite hey in H.
    simpl in H.
    subst.
    rewrite Heqp3 in *. clear Heqp3.
    simpl in *.

    assert (
        StVM.st_trace
          (snd (build_comp a0
                {| st_ev := st_ev2; st_trace := m ++ st_trace2; st_pl := st_pl2; st_store := st_store2 |})) =
         m ++
           StVM.st_trace (snd (build_comp a0 {| st_ev := st_ev2; st_trace := st_trace2; st_pl := st_pl2; st_store := st_store2 |}))) as H.
    eapply IHt2; eauto.
    try jkjk; eauto.
    (*
    rewrite Heqp1.
    simpl. reflexivity.
    eassumption. *)

    
    
    rewrite Heqp4 in H.
    simpl in *.
    rewrite <- H.
    (*try jkjk; eauto. *)
    rewrite Heqp2.
    simpl.
    reflexivity.

    (*

    +
    dohi'.
    build_contra.
    (*


    
    edestruct hihi.
    rewrite Heqp0.
    reflexivity.
    simpl.
    apply hey.
    apply Heqp3.
    destruct_conjs; subst.
     *)
   

    destruct o0.
    repeat dunit.
    build_contra.
    solve_by_inversion.
     *)
    
    (*
    
    assert (
    StVM.st_trace
           (snd (build_comp a {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |})) =
         m ++
         StVM.st_trace
         (snd (build_comp a {| st_ev := e; st_trace := k; st_pl := p; st_store := o |}))
      ).
    repeat dunit.
    eapply IHt1; eauto.
    try jkjk; eauto.
    (*
    rewrite Heqp0.
    reflexivity.
    eassumption. *)

    rewrite hey in H1.
    simpl in *.
    rewrite Heqp3 in H1.
    simpl in H1.
    rewrite H1 in Heqp2.

    solve_by_inversion.
     *)
    

  - (* abseq case *)

    (*
    destruct t';
      try (
          inv H;
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    simpl in *.
    repeat break_let.
    destruct r; destruct s.
    simpl in *.
    inv H.
     *)
    annogo.
    repeat find_inversion.


    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    repeat break_match;
      repeat find_inversion;
      vmsts; repeat dunit;
        try (try dohi'; build_contra; tauto).
      
    +

    assert (
        StVM.st_trace
           (snd (build_comp a {| st_ev := splitEv s1 e; st_trace := k ++ [Term.split n p]; st_pl := p; st_store := o |})) =
         k ++
         StVM.st_trace
         (snd (build_comp a {| st_ev := splitEv s1 e; st_trace := [Term.split n p]; st_pl := p; st_store := o |}))).
    eapply IHt1; eauto.
    try jkjk; eauto.
    (*
    rewrite Heqp0. reflexivity.
    eassumption. *)

    assert (
        StVM.st_trace
           (snd (build_comp a {| st_ev := splitEv s1 e; st_trace := m ++ k ++ [Term.split n p]; st_pl := p; st_store := o |})) =
         m ++
         StVM.st_trace
         (snd (build_comp a {| st_ev := splitEv s1 e; st_trace := k ++ [Term.split n p]; st_pl := p; st_store := o |}))).
    eapply IHt1.
    try jkjk; eauto.
    (*
    rewrite Heqp0. reflexivity. *)
    rewrite <- app_assoc in Heqp6.
    eassumption.
    rewrite Heqp15 in *.
    simpl in *.
    rewrite <- app_assoc in Heqp6.
    rewrite Heqp6 in H0.
    simpl in *.
    rewrite H0 in *.
    simpl in *.

    assert (
        StVM.st_trace
          (snd (build_comp a0 {| st_ev := splitEv s2 e; st_trace := m ++ st_trace0; st_pl := st_pl2; st_store := st_store2 |})) =
        m ++
          StVM.st_trace
          (snd (build_comp a0 {| st_ev := splitEv s2 e; st_trace := st_trace0; st_pl := st_pl2; st_store := st_store2 |}))).
    eapply IHt2; eauto.
    try jkjk; eauto.
    (*
    rewrite Heqp1. reflexivity.
    eassumption. *)
    rewrite Heqp10 in H1.
    simpl in H1.

    dohi'.
    (*

    edestruct hihi.
    rewrite Heqp0. reflexivity.
    simpl. apply Heqp6.
    simpl. apply Heqp15.
    destruct_conjs; subst.
     *)
    

    
    rewrite Heqp19 in *.
    simpl.
    rewrite app_assoc.
    reflexivity.

  -  
    simpl.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.
    monad_unfold.
    (*
    repeat break_let. *)
    dohtac.
    (*
    rewrite PeanoNat.Nat.eqb_refl in *.
    repeat find_inversion.
    assert ( PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false).
    { assert ( (fst (range t1)) <> (fst (range t2))).
      {
        eapply afaf; eauto.
      }
      unfold PeanoNat.Nat.eqb.
      Search PeanoNat.Nat.eqb.
      rewrite PeanoNat.Nat.eqb_neq.
      assumption.
    }

    rewrite H0 in *. *)
    repeat find_inversion.
    (*repeat break_let.
    repeat find_inversion. *)
    dohtac.
    
    simpl in *.
    dohtac.
      (*

    rewrite PeanoNat.Nat.eqb_refl in *. *)
    repeat find_inversion.
    simpl.
    repeat (rewrite app_assoc).
    reflexivity.
Defined.

(* Instance of gen_foo where k=[] *)
Lemma foo : forall t t' n m e p o v,
    t = snd (anno t' n) ->
    build_comp t
               {| st_ev := e; st_trace := m; st_pl := p; st_store := o |} =
    (Some tt, v) -> 
    
    st_trace (snd (build_comp t
                     {| st_ev := e; st_trace := m; st_pl := p; st_store := o |})) =
    m ++ st_trace (snd (build_comp t
                     {| st_ev := e; st_trace := []; st_pl := p; st_store := o |})).
Proof.
  intros.
  assert (m = m ++ []) as HH by (rewrite app_nil_r; auto).
  rewrite HH at 1.
  eapply gen_foo; eauto.
  rewrite app_nil_r.
  eauto.
Defined.

Lemma alseq_decomp : forall r n t1 t2 t1' t2' e e'' p p'' o o'' tr,
    (alseq r t1' t2') = snd (anno (lseq t1 t2) n) -> 
    build_comp (alseq r t1' t2') {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''; st_store := o'' |}) ->

    exists e' tr' p' o',
      build_comp t1' {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}) /\
      exists tr'',
        build_comp t2' {| st_ev := e'; st_trace := []; st_pl := p'; st_store := o' |} =
        (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) /\
        tr = tr' ++ tr''.
      
Proof.
  intros.
  simpl in *.
  repeat break_let.
  monad_unfold.
  break_match.
  destruct o0; try solve_by_inversion.
  repeat break_let.
  vmsts.
  repeat find_inversion. 
  repeat dunit.
  exists st_ev0. exists st_trace0. exists st_pl0. exists st_store0.
  split.
  reflexivity.
  destruct (build_comp a0 {| st_ev := st_ev0; st_trace := []; st_pl := st_pl0; st_store := st_store0 |}) eqn:hey.
  vmsts.
  destruct o0; try build_contra.
  repeat dunit.
  exists st_trace.
  Check hihi.
  dohi'.
  (*
  edestruct hihi.
  reflexivity.
  rewrite Heqp1.
  simpl.
  apply Heqp3.
  rewrite Heqp1.
  simpl.
  apply hey.
  destruct_conjs; subst.
   *)
  
  split.
  reflexivity.

  destruct (build_comp a {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:heyy.
  vmsts.
  destruct o0; try solve_by_inversion.
  repeat dunit.

    (*
    exfalso.
    eapply fafaf.
    rewrite Heqp0.
    reflexivity.
    simpl.
    eassumption.
    simpl.
    solve_by_inversion. *)

  (*
  
    exfalso.
    
    eapply fafaf.
    rewrite Heqp1.
    reflexivity.
    simpl.
    eassumption.
    simpl.
    eassumption. *)
  
  repeat find_inversion.

  Check foo.

  pose foo.
  specialize foo with (t:= a0) (m:=st_trace0) (e:=st_ev0) (p:= st_pl0) (o:=st_store0) (t':=t2) (n:=n0) (v:={| st_ev := st_ev; st_trace := tr; st_pl := st_pl; st_store := st_store |}).
  rewrite Heqp3.
  simpl.
  rewrite hey.
  simpl.
  intros.
  apply H; try reflexivity.
  try jkjk; eauto.
  (*
  rewrite Heqp1.
  simpl.
  reflexivity.
  reflexivity.
  Unshelve. 
  eauto.
  eauto.
  eauto.
  eauto.
  eauto. *)
Defined.

Lemma trace_irrel_store' : forall t t' n tr1 tr1' tr2 e e' p1' p1 o' o,
    t = snd (anno t' n) ->
    build_comp t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    
    st_store (
        snd(
        build_comp t
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |})) = o'.
Proof.
  intros.
  
  destruct (build_comp t {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o |}) eqn:ff.
  vmsts.
  
  destruct o0; repeat dunit.
  - repeat dohi.
    subst.
    destruct_conjs.
    eauto.
  -
    
    exfalso.
    Check fafaf.
    eapply fafaf; eauto.
Defined.

Lemma trace_irrel_pl' : forall t t' n tr1 tr1' tr2 e e' p1' p1 o' o,
    t = snd (anno t' n) ->
    build_comp t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    
    st_pl (
        snd(
        build_comp t
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |})) = p1'.
Proof.
  intros.
  destruct (build_comp t {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  destruct o0; repeat dunit.
  - repeat dohi.
    destruct_conjs.
    eauto.
  -
    exfalso.
    eapply fafaf; eauto.
Defined.

Lemma trace_irrel_ev' : forall t t' n tr1 tr1' tr2 e e' p1' p1 o' o,
    t = snd (anno t' n) ->
    build_comp t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    
    st_ev (
        snd(
        build_comp t
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |})) = e'.
Proof.
  intros.
  destruct (build_comp t {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  destruct o0; repeat dunit.
  - repeat dohi.
    subst.
    destruct_conjs.
    eauto.
  -
    exfalso.
    eapply fafaf; eauto.
Defined.

(* Congruence lemmas for Copland LTS semantics *)
Lemma lstar_stls :
  forall st0 st1 t tr,
    lstar st0 tr st1 -> lstar (ls st0 t) tr (ls st1 t).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Qed.

Lemma lstar_strem : forall st st' tr p r,
    lstar st tr
          st' ->
    lstar (rem r p st) tr (rem r p st').
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma lstar_stbsl:
  forall st0 st1 j t p e tr,
    lstar st0 tr st1 ->
    lstar (bsl j st0 t p e) tr (bsl j st1 t p e).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

Lemma lstar_stbsr:
  forall st0 st1 j e tr,
    lstar st0 tr st1 ->
    lstar (bsr j e st0) tr (bsr j e st1).
Proof.
  intros.
  induction H; auto.
  eapply lstar_tran; eauto.
  eapply lstar_silent_tran; eauto.
Defined.

(*
Lemma star_stbp:
  forall st0 st1 st2 st3 j,
    star st0 st1 ->
    star st2 st3 ->
    star (bp j st0 st2) (bp j st1 st3).
Proof.
  intros.
  induction H; auto.
  - induction H0; auto.
    eapply star_tran; eauto.
  - eapply star_tran; eauto.
Qed.*)

Lemma ssc_inv : forall e1 e1' e2 e2',
    e1 = e1' ->
    e2 = e2' ->
    ssc e1 e2 = ssc e1' e2'.
Proof.
  intros.
  congruence.
Defined.

Check parallel_eval_thread.
Check parallel_att_vm_thread.

Axiom para_eval_vm : forall t e,
    parallel_eval_thread (unanno t) e = parallel_att_vm_thread t e.

Lemma record_congr :
  forall A,
    A =
    {| st_ev := st_ev A;
       st_trace := st_trace A;
       st_pl := st_pl A;
       st_store := st_store A|}.
Proof.
  intros A.
  destruct A.
  reflexivity.
Defined.

(*
Ltac st_equiv :=
  match goal with
  | |- _ ++ _ ++ _ ++
        st_trace (fold_left _ _ ?st1) =
      _ ++ _ ++ _ ++
        st_trace (fold_left _ _ ?st2) =>
    (*idtac "matched" ;*)
    assert (st1 = st2)
      by (
          eapply st_congr; simpl;
          try (try erewrite trace_irrel_ev;
               try erewrite trace_irrel_stack;
               try erewrite trace_irrel_store;
               try reflexivity;
               rewrite <- record_congr; reflexivity))  
  end.
*)

Lemma haha {A:Type} : forall (m:list A) l req rem rpy,
    m ++ (req :: rem ++ [rpy]) ++ l =
    m ++ [req] ++ rem ++ [rpy] ++ l.
Proof.
  intros.
  simpl.
  repeat rewrite <- app_assoc.
  simpl.
  reflexivity.
Defined.

Lemma pl_immut : forall t t' n e tr p o,
    t = snd (anno t' n) ->
    st_pl
      (snd
         (build_comp t
              {|
                st_ev := e;
                st_trace := tr;
                st_pl := p;
                st_store := o |})) = p.
Proof.
  induction t; intros.
  -
    destruct r.
    destruct a;
      reflexivity.
  - simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.
    (*
    rewrite PeanoNat.Nat.eqb_refl in *. *)
    repeat find_inversion.
    simpl.
    reflexivity.
  - simpl in *.
    monad_unfold.
    repeat break_match;
      try solve_by_inversion.
    simpl.
    repeat dunit.
    vmsts.
    simpl.

    annogo.

    (*

    destruct t'; inv H;
      try (
          repeat break_let;
          solve_by_inversion).
    simpl in *.
    repeat break_let.
    inv H.
     *)
    Ltac jkjk' :=
      match goal with
      | H: _ |- _ => rewrite H; reflexivity
      end.

    (*

    erewrite <- IHt1; eauto.
    erewrite <- IHt2; eauto.
    rewrite Heqp0. simpl.
    jkjk'.
    jkjk; eauto.
    jkjk; eauto.
    simpl.
    vmsts.
    simpl.
    erewrite <- IHt1.
    simpl.
    jkjk; eauto.
    jkjk; eauto.
    rewrite Heqp0.
    simpl.
     *)
    
    
    assert (p = st_pl0).
    {
      edestruct IHt1;
        jkjk'.
    }

    assert (st_pl0 = st_pl).
    {
      edestruct IHt2;
        jkjk'.
    }

    congruence.

    annogo.
    (*

    destruct t'; inv H;
      try (
          repeat break_let;
          solve_by_inversion).
    simpl in *.
    repeat break_let.
    inv H.
     *)
    

    symmetry.
    
    
    edestruct IHt1.
    jkjk; eauto.
    jkjk'; eauto.
    (*
    rewrite Heqp1.
    simpl. reflexivity.
    rewrite Heqp0.
    simpl. reflexivity. *)
    
  -
    annogo.
    (*
    destruct t'; inv H;
      try (
          repeat break_let;
          solve_by_inversion).
    simpl in *.
    repeat break_let.
    inv H.
     *)
    
    
    simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    repeat break_match;
      try solve_by_inversion;
    repeat find_inversion;
    repeat dunit;
    simpl in *; vmsts; simpl in *.
    +
    

    assert (p = st_pl0).
    {
      edestruct IHt1.
      jkjk'; eauto.
      jkjk'; eauto.
    }
    (*
      rewrite Heqp0.
      simpl. reflexivity.
      rewrite Heqp6.
      simpl.
      reflexivity.
    }
*)

    assert (st_pl0 = st_pl).
    {     
      edestruct IHt2;
      jkjk'; eauto.
    }
    (*
      rewrite Heqp1.
      simpl. reflexivity.
      rewrite Heqp10.
      simpl.
      reflexivity.
    } *)
    congruence.
    +
      assert (p = st_pl).
      {
        edestruct IHt1;
          jkjk'; eauto.
      }

      (*
          
        rewrite Heqp0.
        simpl. reflexivity.
        rewrite Heqp6.
        simpl. reflexivity.
      } *)

      assert (st_pl = st_pl0).
      {
        edestruct IHt2;
          jkjk'; eauto.
      }
      (*
        rewrite Heqp1.
        simpl. reflexivity.
        rewrite Heqp10.
        simpl. reflexivity.
      } *)
      congruence.
    +
      symmetry.
      edestruct IHt1;
      jkjk'; eauto.
      (*
      rewrite Heqp0.
      simpl. reflexivity.
      rewrite Heqp6.
      simpl. reflexivity. *)
    +
      symmetry.
      edestruct IHt1;
      jkjk'; eauto.
(*
      rewrite Heqp0.
      simpl. reflexivity.
      rewrite Heqp6.
      simpl. reflexivity. *)
  -
    simpl in *.
    monad_unfold.
    repeat break_let.
    simpl in *.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.

    dohtac.
    (*

    rewrite PeanoNat.Nat.eqb_refl in *.

    assert (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false).
    {
      assert ( (fst (range t1)) <> (fst (range t2))).
      {
        Check afaf.
        simpl in *.
        eapply afaf; eauto.
      }
      unfold PeanoNat.Nat.eqb.
      Search PeanoNat.Nat.eqb.
      rewrite PeanoNat.Nat.eqb_neq.
      assumption.
    }
    rewrite H0 in *.
     *)
    
    repeat find_inversion.
    simpl in *.

    dohtac.
    (*

    rewrite PeanoNat.Nat.eqb_refl in *. *)
    repeat find_inversion.
    reflexivity.
Defined.

Lemma restl' : forall t t' n e e' x tr p p' o o',
    t = snd (anno t' n) -> 
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |}) ->

    build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
Proof.
  intros.
  
  assert (
      st_trace (run_vm t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |}) =
      st_trace ({| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |})).
  unfold run_vm.
  monad_unfold.
  rewrite H0.
  simpl.
  reflexivity.
  Check foo.
  Check trace_irrel_ev'.
  unfold run_vm in *.
  monad_unfold.
  Check trace_irrel_ev'.
  assert (
   st_ev
         (snd
            (build_comp t
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |})) = e').
  eapply trace_irrel_ev'; eauto.

  assert (
   st_pl
         (snd
            (build_comp t
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |})) = p').
  eapply trace_irrel_pl'; eauto.

  assert (
   st_store
         (snd
            (build_comp t
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |})) = o').
  eapply trace_irrel_store'; eauto.
  Check st_congr.

  assert (
      (snd
         (build_comp t
                     {| st_ev := e; st_trace := []; st_pl := p; st_store := o |})) =
      {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
  {
    eapply st_congr; eauto.
    Check foo.
    erewrite foo in H1; eauto.
    eapply app_inv_head.
    eauto.

  }
  
  destruct (build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:aa.
  simpl in *.
  vmsts.
  simpl in *.
  repeat find_inversion.
  destruct o0.
  destruct u.
  reflexivity.
  exfalso.
  eapply fafaf; eauto.
Defined.

Lemma store_get_set : forall e tr p o n e1 e' v0,
    get_store_at n
      {|
        st_ev := e;
        st_trace := tr;
        st_pl := p;
        st_store := Maps.map_set o n e1 |} =
    (Some e', v0) ->
    e' = e1.
Proof.
  intros.
  boom; repeat (break_match; allss).
  unfold get_store_at in *.
  unfold get in *. simpl in *.
  cbn in H.
  break_let.
  rewrite PeanoNat.Nat.eqb_refl in Heqp0.
  boom; repeat (break_match; allss); congruence.
Defined.

Lemma store_get_set_fail_none : forall n e tr p o e1 v,
    get_store_at n
     {|
       st_ev := e;
       st_trace := tr;
       st_pl := p;
       st_store := Maps.map_set o n e1 |} =
    (None, v) ->
    False.
Proof.
  intros.
  unfold get_store_at in *.
  cbn in H.
  break_let.
  rewrite PeanoNat.Nat.eqb_refl in Heqp0.
  boom; repeat (break_match; allss); congruence.
Defined.

Lemma multi_ev_eval : forall t tr tr' e e' p p' o o',
    run_vm t
           {| st_ev := e; st_trace := tr; st_pl := p; st_store := o |} =
           {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}  ->
    e' = eval (unanno t) e.
Proof.
  (*
  induction t; intros.
  - (* aasp case *)
    destruct a; inv H; try reflexivity.
  - (* aatt case *)
    simpl in *.
    destruct r.
    simpl in *.
    unfoldm.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.
    monad_unfold.
    rewrite PeanoNat.Nat.eqb_refl in *.
    allss.
  - (* lseq case *)
    simpl in *.
    do_dca.
    simpl.
    eapply IHt2.
    assert (H2 = p).
    Check pl_immut.
    assert (st_pl (fold_left run_vm_step (instr_compiler t1)
                             {|
                               st_ev := e;
                               st_stack := s;
                               st_trace := tr;
                               st_pl := p;
                               st_store := o |}) = p).
    eapply pl_immut.
    assert (st_pl
             (run_vm (instr_compiler t1)
         {|
         st_ev := e;
         st_stack := s;
         st_trace := tr;
         st_pl := p;
         st_store := o |}) =
       st_pl ({|
       st_ev := H0;
       st_stack := H1;
       st_trace := H;
       st_pl := H2;
       st_store := H3 |})).
    congruence.
    rewrite <- H8 in H9.
    simpl in H9.
    rewrite H8 in H9.
    unfold run_vm in *.
    congruence.
    
    assert (H0 = eval (unanno t1) e).
    eauto.
    subst.
    eauto.
  - (* abseq case *)
    destruct s; simpl in *.
    destruct r.
    
    unfold run_vm_step in *. monad_unfold; monad_unfold.
    
    do_dca.

    do_run.
    desp.
    pairs.

    do_dca.
    do_run.
    desp.
    pairs.

    do_stack1 t2.
    subst.

    unfold pop_stackm in *. monad_unfold.
    pairs.
    apply ssc_inv.
    eauto.
   
    eapply IHt2.
    do_stack1 t1.
    subst.
    unfold pop_stack in *. monad_unfold.
    pairs.
    assert (H2 = p). {
      assert ( st_pl ( run_vm (instr_compiler t1) {|
         st_ev := splitEv s e;
         st_stack := push_stack EvidenceC (splitEv s1 e) s0;
         st_trace := tr ++ [Term.split n p];
         st_pl := p;
         st_store := o |}) =
     st_pl (  {|
       st_ev := H0;
       st_stack := push_stack EvidenceC (splitEv s1 e) s0;
       st_trace := H;
       st_pl := H2;
       st_store := H3 |} )).
      congruence.
      simpl in H1.
      rewrite <- H1.
      apply pl_immut.
      }
    subst.
    eauto.

    do_stack t1 t2.
   
    subst. simpl in *. unfold pop_stackm in Heqppp. monad_unfold.
    pairs.

    unfold pop_stackm in *. monad_unfold.
    unfold push_stack in *. congruence.

    do_stack1 t1.
    subst.
    unfold pop_stackm in *. monad_unfold. congruence.
  - (* abpar case *)
    simpl.
    destruct s.
    destruct r.

    unfold run_vm_step in *. repeat monad_unfold.
    simpl in *.
    unfold run_vm_step in *.
    repeat monad_unfold.

    repeat break_match;
      try
        (boom; allss;
         repeat rewrite para_eval_vm;
         eauto).
   *)
Admitted.

Lemma suffix_prop : forall t t' n e e' tr tr' p p' o o',
    t = snd (anno t' n) ->
    build_comp t
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p;
             st_store := o |} =
    (Some tt, {|
      st_ev := e';
      st_trace := tr';
      st_pl := p';
      st_store := o' |}) ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace (snd (build_comp t
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p;
             st_store := o |})) =
    st_trace ({|
      st_ev := e';
      st_trace := tr';
      st_pl := p';
      st_store := o' |})) as H00.
  rewrite H0.
  simpl.
  reflexivity.

  simpl in H00.
  eexists.
  rewrite <- H00.
  erewrite foo; eauto.
Defined.

Axiom run_at : forall t e n o,
      run_vm t
             {| st_ev := e;
                st_trace := [];
                st_pl := n;
                st_store := o |} =
             {| st_ev := (eval (unanno t) e);
                st_trace := remote_events t n;
                st_pl := n;
                st_store := o |}.

Lemma get_store_in : forall x st st' o y,
    get_store_at x st = (None, st') ->
    st_store st = o ->
    Maps.map_get o x = (Some y) ->
    False.
Proof.
  intros.
  destruct st.
  simpl in *.
  subst.
  monad_unfold.
  unfold get_store_at in *.
  monad_unfold.
  rewrite H1 in *.
  find_inversion.
Defined.

Axiom bpar_shuffle : forall x p t1 t2 et1 et2,
    lstar (bp x (conf t1 p et1) (conf t2 p et2))
          (shuffled_events (parallel_vm_events t1 p)
                           (parallel_vm_events t2 p))
          (bp x (stop p (aeval t1 p et1)) (stop p (aeval t2 p et2))).

Lemma afff : forall t' (n:nat) r s x t n,
    snd (anno t' n) = aatt (r,s) x t ->
    exists t'' n', t = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        cbn in *;
        inv H; tauto).
  - cbn in *.
    simpl in *.
    break_let.
    simpl in *.
    inv H.
    exists t'.
    exists (S r).
    rewrite Heqp.
    simpl.
    reflexivity.
Defined.

Lemma afaff : forall t' n r t1 t2,
    snd (anno t' n) = alseq r t1 t2 ->
    exists t'' n', t1 = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        simpl in *;
        inv H;
        tauto).
  - cbn in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    inv H.
    exists t'1.
    exists (n).
    rewrite Heqp.
    simpl.
    reflexivity.
Defined.

Lemma afaff2 : forall t' n r t1 t2,
    snd (anno t' n) = alseq r t1 t2 ->
    exists t'' n', t2 = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        simpl in *;
        inv H;
        tauto).
  - cbn in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    inv H.
    exists t'2.
    exists (n0).
    rewrite Heqp0.
    simpl.
    reflexivity.
Defined.

Lemma afaff3 : forall t' n n0 n1 s s1 t1 t2,
    snd (anno t' n) =  abseq (n0, n1) (s, s1) t1 t2 ->
    exists t'' n', t1 = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        simpl in *;
        inv H;
        tauto).
  - cbn in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    inv H.
    exists t'1.
    exists (S n0).
    rewrite Heqp.
    simpl.
    reflexivity.
Defined.

Lemma afaff4 : forall t' n n0 n1 s s1 t1 t2,
    snd (anno t' n) =  abseq (n0, n1) (s, s1) t1 t2 ->
    exists t'' n', t2 = snd (anno t'' n').
Proof.
  intros.
  destruct t';
    try (
        unfold anno in H;
        repeat break_let;
        simpl in *;
        inv H;
        tauto).
  - cbn in *.
    simpl in *.
    repeat break_let.
    simpl in *.
    inv H.
    exists t'2.
    exists (n2).
    rewrite Heqp0.
    simpl.
    reflexivity.
Defined.
   
Lemma restl'_2
  : forall (t : AnnoTerm) (e e' : EvidenceC) (x tr : list Ev) (p p' : nat) (o o' : ev_store) t' n,
    t = snd (anno t' n) ->
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |}) ->
    build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
Proof.
  intros.
  Check restl'.
  eapply restl'; eauto.
Defined.

Axiom build_comp_at : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store),
    build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |} =
    (Some tt, {| st_ev := eval (unanno t) e; st_trace := remote_events t n; st_pl := n; st_store := o |}).

Lemma run_lstar : forall t tr et e e' p p' o o' t' n,
    (*well_formed t -> *)
    t = snd (anno t' n) -> 
    build_comp t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o')) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros t tr et e e' p p' o o' t' n HH H.
  
  generalize dependent tr.
  generalize dependent et.
  generalize dependent p.
  generalize dependent p'.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent o.
  generalize dependent o'.
  generalize dependent t'.
  generalize dependent n.
  induction t; intros.
  - (* aasp case *)
    destruct a;
      unfold run_vm in *;
      repeat (monad_unfold; break_let; monad_unfold);
      repeat find_inversion;
      econstructor; try (econstructor; reflexivity).
  - (* aatt case *)
    simpl in *.
    destruct r.
    unfold run_vm in *.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.
    find_inversion.
    find_inversion.
    monad_unfold.
    rewrite PeanoNat.Nat.eqb_refl in *.
    repeat find_inversion.
    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.

    edestruct afff; eauto.
    destruct_conjs.

    eapply IHt; eauto.
    Check run_at.
    Print run_at.

    apply build_comp_at.

    econstructor.
    apply stattstop.
    econstructor.
    
  -
    Print annogo.
    (*
    vmsts; repeat dunit.
    annogo. *)
    
    destruct t';
      try (
          inv HH;
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    


    edestruct alseq_decomp; eauto.
    destruct_conjs.
    
          
    econstructor.
    econstructor.

    subst.

    eapply lstar_transitive.

    eapply lstar_stls.
    inversion HH.
    repeat break_let.
    simpl in *.
    inversion H7.
    rewrite H9 in *.
    rewrite H10 in *.


    eapply IHt1.
    rewrite Heqp0.
    simpl. reflexivity.
    eassumption.

    eapply lstar_silent_tran.
    apply stlseqstop.

    inversion HH.
    repeat break_let.
    simpl in *.
    inversion H7.
    rewrite H9 in *.
    rewrite H10 in *.
    clear H9. clear H10.

    assert (p = H1).
    {
      edestruct pl_immut.
      rewrite Heqp0.
      reflexivity.
      simpl.
      jkjk'; eauto.
      (*
      rewrite H3.
      simpl.
      reflexivity. *)
    }
    rewrite <- H6 in H5. clear H6.
    
    eapply IHt2;
      jkjk'; eauto.
    (*
    jkjk'; eauto.
    rewrite Heqp1. simpl. reflexivity.
    eauto.
     *)
    

  -

    destruct t';
      try (
          inv HH;
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    destruct r; destruct s.

    
    edestruct afaff3; eauto.
    edestruct afaff4; eauto.
    destruct_conjs.
     
    simpl in *.
    repeat break_let.
    invc HH.

    unfold run_vm in *. repeat monad_unfold.
    repeat break_let.
    repeat monad_unfold.
    vmsts.
    

    repeat find_inversion.
    repeat break_match;
      repeat find_inversion;
      simpl in *.

    Check restl'.

    assert (exists l, st_trace3 = [Term.split n p] ++ l) as H00.
    eapply suffix_prop. rewrite Heqp0. reflexivity.
    simpl.
    rewrite Heqp6.
    repeat dunit.
    simpl.
    reflexivity.

    destruct H00 as [H00 H11].
    rewrite H11 in *. clear H11.

    Check restl'.
    


    assert (build_comp (snd (anno x H0))
                       {| st_ev := splitEv s e; st_trace := []; st_pl := p; st_store := o |} =
            (Some tt, {| st_ev := st_ev3; st_trace := H00; st_pl := st_pl3; st_store := st_store3 |})).
    {
      eapply restl'_2.
      reflexivity.
      assert ( Term.split n p :: H00 =  [Term.split n p] ++ H00) by reflexivity.
      
      
      repeat dunit.
      eassumption.
    }
    
    assert (exists l, st_trace = ([Term.split n p] ++ H00) ++ l) as H000.
    eapply suffix_prop.
    rewrite Heqp1. reflexivity.
    simpl.
    unfold run_vm.
    monad_unfold.
    rewrite Heqp10.
    repeat dunit.
    simpl.
    reflexivity.
    destruct H000 as [H000 HHH].
    rewrite HHH in *. clear HHH.

    assert (
        build_comp (snd (anno x0 H1))
                   {| st_ev := splitEv s1 e; st_trace := []; st_pl := st_pl3; st_store := st_store3 |} =
        (Some tt, {| st_ev := st_ev; st_trace := H000; st_pl := p'; st_store := o' |})).
    {
      repeat dunit.
      eapply restl'_2.
      
      reflexivity.
      
      assert ( Term.split n p :: H00 =  [Term.split n p] ++ H00) by reflexivity.
         
      (* rewrite H2 in *. *)
      repeat dunit.
      eassumption.

    }
    
    assert (p = st_pl3).
    {
      edestruct pl_immut.
      simpl in *.
      rewrite Heqp0.
      simpl. reflexivity.
      repeat dunit.
                      
      
      rewrite Heqp6.
      simpl. reflexivity.
    }

    rewrite H3 in *. clear H3.

    assert (st_pl3 = p').
    {
      edestruct pl_immut.
      rewrite Heqp1.
      reflexivity.
      simpl.
      rewrite Heqp10.
      simpl. reflexivity.
    }
    rewrite H3 in *. clear H3.
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    eapply lstar_transitive.
    simpl.
    Check lstar_stbsl.

    eapply lstar_stbsl.  
     
    eapply IHt1; eauto.
  
    unfold run_vm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
     eapply lstar_transitive.
     eapply lstar_stbsr.
        
     eapply IHt2; eauto.

     Check stbsrstop.
     econstructor.
     eapply stbsrstop.
     econstructor.

  -
    destruct s; destruct r.
    simpl in *.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.

    repeat find_inversion.
    monad_unfold.
    repeat break_let.

    

    dohtac.

    (*
    rewrite PeanoNat.Nat.eqb_refl in *.

    assert (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false).
    {
      assert ( (fst (range t1)) <> (fst (range t2))).
      {
        Check afaf.
        simpl in *.
        eapply afaf; eauto.
      }
      unfold PeanoNat.Nat.eqb.
      Search PeanoNat.Nat.eqb.
      rewrite PeanoNat.Nat.eqb_neq.
      assumption.
    }
    rewrite H in *. *)
     
    
    
    destruct t'; inv HH;
      try (
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    repeat break_let.
     
    

    repeat find_inversion.
    repeat break_let.
    repeat find_inversion.
    simpl in *.
    dohtac.
    repeat find_inversion.
    econstructor.
    econstructor.
    eapply lstar_transitive.
    simpl.
    apply bpar_shuffle.
    econstructor.
    apply stbpstop.
    econstructor.
    Unshelve.
    eauto.
    eauto.
Defined.

Lemma run_lstar_corrolary : forall t tr et e e' p p' o o' t' n,
    t = snd (anno t' n) ->
    build_comp t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o')) ->
    st_trace (run_vm t
                     (mk_st e [] p o)) = tr ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  destruct (build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  
  apply run_lstar with (t:=t) (tr:=tr) (e:=e) (p:=p) (o:=o) (e':=st_ev) (p':=st_pl) (o':=st_store) (t':=t') (n:=n); eauto.
  
  destruct o0.
  dunit.
  rewrite hi.
  
  unfold run_vm in H1.
  monad_unfold.
  rewrite hi in H1.
  simpl in *.
  subst.
  reflexivity.
  solve_by_inversion.
Defined.

Theorem vm_ordered' : forall t tr ev0 ev1 e e' o o' t' n,
    well_formed t ->
    t = snd (anno t' n) -> 
    build_comp 
      t
      (mk_st e [] 0 o) =
      (Some tt, (mk_st e' tr 0 o')) ->
    prec (ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  Check ordered.
  eapply ordered with (p:=0) (e:=mt); eauto.
  eapply run_lstar; eauto.
Defined.

Locate prec.

Theorem vm_ordered : forall t tr ev0 ev1 e e' o o' t',
    t = annotated t' -> 
    build_comp
      t
      (mk_st e [] 0 o) =
      (Some tt, (mk_st e' tr 0 o')) ->
    prec (ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  Check ordered.
  eapply ordered with (p:=0) (e:=mt); eauto.
  - unfold annotated in H.
    subst.
    eapply anno_well_formed; eauto.
  - eapply run_lstar; eauto.
Defined.

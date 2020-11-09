(*
Implementation of the Attestation Virtual Machine (AVM) + proof that it refines the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Preamble Term ConcreteEvidence LTS GenStMonad.
Require Import Main Event_system Term_system.


Require Import MonadVM MonadVMFacts Maps VM_IO_Axioms.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.


Set Nested Proofs Allowed.


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
(*  | abseq (x,y) (sp1,sp2) t1 t2 =>
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
    (*
    let res1 := parallel_att_vm_thread t1 e in
    (* TODO: change this to a monadic function that consults an environment that is aware of the presence (or absence) of parallel avm threads.  Put initial evidence in store, let environment run the parallel thread and place result evidence, then query for result evidence here. *)
    let res2 := parallel_att_vm_thread t2 e2 in
    let el1 := parallel_vm_events t1 p in
    let el2 := parallel_vm_events t2 p in
    let loc1 := fst (range t1) in
    let loc2 := fst (range t2) in
    put_store loc1 res1 ;;
    put_store loc2 res2 ;;
    add_tracem (shuffled_events el1 el2) ;; *)

    runParThreads t1 t2 p e1 e2 ;;
    let loc1 := fst (range t1) in
    let loc2 := fst (range t2) in
       
    e1r <- get_store_at loc1 ;;
    e2r <- get_store_at loc2 ;;
    put_ev (ppc e1r e2r) ;;
    add_tracem [Term.join (Nat.pred y) p]
*)
  end.

(** Function-style semantics for VM *)

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

(*
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
 *)

Ltac annogo := vmsts; repeat dunit.

Ltac anhl :=
  annogo;
  match goal with
  | [(*H: well_formed ?a (*anno _ _ = (_, ?a)*), *)
     H2: build_comp ?a _ = _,
     H3: build_comp ?a _ = _,
     IH: context[(*well_formed ?a*) build_comp ?a _ = _ -> _] |- _] =>
    edestruct IH;
    [(*(rewrite H; reflexivity)*) (*apply H | *)
     apply H2 | apply H3 | idtac]; clear H2; clear H3;
    destruct_conjs; subst
  end.

Lemma wf_lseq_pieces: forall r t1 t2,
    well_formed (alseq r t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

Lemma wf_at_pieces: forall t r p,
    well_formed (aatt r p t) ->
    well_formed t.
Proof.
  intros.
  inversion H.
  tauto.
Defined.

(*
Lemma wf_bseq_pieces: forall r s t1 t2,
    well_formed (abseq r s t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.


Lemma wf_bpar_pieces: forall r s t1 t2,
    well_formed (abpar r s t1 t2) ->
    well_formed t1 /\ well_formed t2.
Proof.
  intros.
  inversion H.
  tauto.
Defined.
*)


Ltac do_wf_pieces :=
  match goal with
  | [H: well_formed (alseq _ _ _) |- _] =>
    (edestruct wf_lseq_pieces; eauto)
  | [H: well_formed (aatt _ _ ?t) |- _] =>   
    assert (well_formed t)
      by (eapply wf_at_pieces; eauto)
  (*| [H: well_formed (abseq _ _ _ _ ) |- _] =>
    (edestruct wf_bseq_pieces; eauto)
  | [H: well_formed (abpar _ _ _ _ ) |- _] =>
    (edestruct wf_bpar_pieces; eauto) *)
      
  end.

(*
Lemma h : forall a b t1 t2 (*t n *),
    (*abpar a b t1 t2 = snd (anno t n) -> *)
    well_formed (abpar a b t1 t2) -> 
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
  | [H: well_formed (abpar _ _ ?t1 ?t2) (*(abpar _ _ ?t1 ?t2 = snd _*) |- _] =>
    let X := fresh in
    assert (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false) as X by tac; rewrite X in *; clear X
  end.
*)

Ltac dohtac := (*try htac; *)
               try rewrite PeanoNat.Nat.eqb_refl in *;
               try rewrite PeanoNat.Nat.eqb_eq in *.


Ltac df :=
  repeat (
      cbn in *;
      unfold runSt in *;
      repeat break_let;
      repeat (monad_unfold; cbn in *; find_inversion);
      monad_unfold;
      repeat dunit;
      unfold snd in * ).

Ltac dosome :=
  repeat (
      match goal with
      | [H: match ?o with
            | Some _ => _
            | _ => _
            end
            =
            (Some _, _) |- _] =>
        destruct o; try solve_by_inversion
      end; df).

Ltac subst' :=
  match goal with
  | [H: ?A = _,
        H2: context[?A] |- _] =>
    rewrite H in *; clear H
  | [H: ?A = _ |- context[?A]] =>
    rewrite H in *; clear H
  end.

Ltac dooit :=
  repeat eexists;
  cbn;
  repeat break_let;
  simpl;
  repeat find_inversion;
  subst';
  df;
  reflexivity.

Lemma hihi : forall t (*t' n*) e e' e'' x x' y y' p p' p'' o o' o'',
    (*t = snd (anno t' n) -> *)
    (*well_formed t -> *)
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x'; st_pl := p'; st_store := o' |}) ->
    build_comp t {| st_ev := e; st_trace := y; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := y'; st_pl := p''; st_store := o'' |}) ->
    (e' = e'' /\ p' = p'' /\ o' = o'').
Proof.
  induction t; intros.
  - destruct a;
      df; eauto.
    (*
      simpl in *;
      repeat break_let;
      monad_unfold;
      repeat find_inversion;
      auto. *)
  -
    df.
    (*

    simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    df. *)
    repeat break_match; try solve_by_inversion;
      repeat (df; tauto).
    (*
    df.
    tauto.
    df.
    tauto. *)
    
    (*
    reflexivity.
    tauto.
    df.
    tauto.
    
    dohtac.
    repeat find_inversion.
    auto. *)
  -
    df;
    (*
    simpl in *;
    monad_unfold; *)
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.

    anhl.
    eauto.
    (*
    
    
    
    edestruct IHt1.
    apply Heqp0.
    apply Heqp2.
    destruct_conjs; subst.
    eauto.
     *)
    
      
      
      
      
    

    (*

    annogo.
    edestruct IHt1.
    eassumption.
    apply Heqp0.
    apply Heqp2.
    destruct_conjs.
    subst.
    eauto. *)
    (*

    Print anhl.
  
    
    repeat anhl.
    eauto. *)
    (*
  -
    df;
      (*
    simpl in *.
    monad_unfold; *)
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.
    df.
    repeat anhl.
    eauto.
    
    (*
    edestruct IHt1.
    apply Heqp4.
    apply Heqp13.
    destruct_conjs; subst. *)
    
    (*
    anhl.
    eauto.
     *)
    
    (*
    simpl in *.
    df.
    anhl.
    eauto.
    
    edestruct IHt2.
    apply Heqp8.
    apply Heqp17.
    destruct_conjs; subst.
    tauto. *)
    (*
    df.
    
   
    eassumption.
    
    inversion H.

    
    annogo.
    repeat anhl.
    eauto. *)
  -
    df.
    (*
    simpl in *.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.
    monad_unfold.
    df. *)
    repeat break_match; try solve_by_inversion;
      try (
          repeat (df; try tauto; subst'; try tauto);
          tauto).
*)
Defined.
(*
    df.
    subst'.
    df.
    tauto.
    tauto.
    
    subst'.
    df.
    tauto.
    
    

    dohtac.
    
    repeat find_inversion.
    simpl in *.

    dohtac.

    repeat find_inversion.
    auto. *)

Ltac dohi :=
  annogo;
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
    map_get ((k,v) :: l') k = Some v.
Proof.
  intros.
  simpl.
  break_match; eauto.
  rewrite PeanoNat.Nat.eqb_refl in Heqb. congruence.
Defined.

Lemma map_get_get_2(*{V:Type}`{forall x y : V, Dec (x = y)}*) :
  forall (k:nat) (v:EvidenceC) k' v' l',
    k <> k' ->
    map_get ((k',v') :: (k,v) :: l') k = Some v.
Proof.
  intros; simpl.
  break_if;
    dohtac; tauto.
Defined.

Ltac dohi' :=
  annogo;
  match goal with
  | [(*H: well_formed ?a (*anno _ _ = (_, ?a)*), *)
        H2: build_comp ?a _ = _,
            H3: build_comp ?a _ = _(*,
                IH: context[?a = _ -> _]*) |- _] =>
    edestruct hihi;
    [(* (apply H (*rewrite H; reflexivity*)) | *)
     repeat dunit; apply H2 | repeat dunit; apply H3 | idtac]; (*clear H2; clear H3;*)
    destruct_conjs; subst
  end.

Ltac jkjk :=
  match goal with
  | [H: context[?X] |- ?X = _] => rewrite H
  end.

Lemma fafaf : forall t (*t' n*) e e' e'' p p' p'' o o' o'' x y r s,
    (*t = snd (anno t' n) -> *)
    (*well_formed t -> *)
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (None, {| st_ev := e'; st_trace := y; st_pl := p'; st_store := o' |}) ->
    build_comp t {| st_ev := e; st_trace := r; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := s; st_pl := p''; st_store := o'' |}) ->
    False.
Proof.
  
  induction t; intros.
  - destruct a;
      df; (*
      simpl in *;
      break_let;
      monad_unfold; *)
      solve_by_inversion.

  -
    (*simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    monad_unfold.

    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let. *)
    df.
    dohtac.
    df.
    (*
    monad_unfold.
    repeat find_inversion. *)
  -
    df.
    (*
    simpl in *.   
    repeat monad_unfold.
    
    inversion H. *)
    repeat break_match; try solve_by_inversion.
    +
      
      
      dohi'.
      (*
      clear H7.
      clear H8.
      clear H9. *)

      (*


      edestruct hihi.
      eassumption.
      apply Heqp2.
    [(eassumption (*rewrite H; reflexivity*)) |
     repeat dunit; apply H2 | repeat dunit; apply H3 | idtac]

      (*
      annogo. *)

      dohi'. *)

      

      df.

      (*
      edestruct hihi
      apply Heqp2.

      dohi'.

      eapply IHt2.
      eassumption.
      eassumption. *)
      eauto.
      (*

      eapply IHt2; eauto. *)
      (*
     
      try jkjk; eauto.    *)
    +
      
      annogo.
      eauto.
      (*
      
      
      eapply IHt1; eauto. *)
      (*
      try jkjk; eauto. *)
      (*
  -
    (*
    inversion H.

    
    annogo.
  
   
    simpl in *.
    repeat break_let.
    monad_unfold.
    
    repeat break_let.
    repeat find_inversion. *)
    df.
    repeat break_match;
      boom; allss;
        annogo;
        try dohi';
        eauto.
    (*
    +
      dohi'; eauto.
      

      dohi'.
      eauto.
      (*
    
    eapply IHt2; eauto. *)
      (*try jkjk; eauto. *)
    +
      eauto.
    + eauto.
      

  
    eapply IHt1; eauto.
    (*try jkjk; eauto.*)

   
    eapply IHt1; eauto. *)
    
    (*
    jkjk; eauto.  *)    
     
  -
    (*
    simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    repeat find_inversion. *)
    df.
    repeat break_match;
      try (
          df;
          dohtac;
          solve_by_inversion).

    (*
      repeat find_inversion.
    +
      df.
      (*
    vmsts.
    simpl in *.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let. *)
      dohtac.
      solve_by_inversion.
      subst'.
      solve_by_inversion.
      (*
      df.
      

    repeat find_inversion.

    assert (map_get
              (map_set (map_set o (fst (range t1)) (parallel_att_vm_thread t1 (splitEv s1 st_ev1))) (fst (range t2))
                            (parallel_att_vm_thread t2 (splitEv s2 st_ev1))) (fst (range t2)) =
            Some (parallel_att_vm_thread t2 (splitEv s2 st_ev1))) as H1.
    {
      unfold map_set in *.
      apply map_get_get.
    }
    rewrite H1 in *.
    repeat find_inversion. *)
    +
      df.
      dohtac.
      solve_by_inversion.
    +
      df.
      dohtac.
      solve_by_inversion.
      
      
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    dohtac.

    repeat find_inversion. *)
*)
Defined.

Lemma fals : forall a (*t'1 n n0*) e x y p o u v v' P,
    (*anno t'1 n = (n0, a) -> *)
    (*well_formed a -> *)
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
  annogo.
  eapply fafaf; eauto.
Defined.

(*

  eassumption.
  (*
  Print jkjk.
  (* jkjk. *)
  rewrite H.
  simpl. reflexivity. *)
  simpl in *.
  eassumption.
  eassumption.
Defined.
*)

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




Lemma always_some : forall (*t' n*) t vm_st vm_st' op,
    (*t = snd (anno t' n) -> *)
    (*well_formed t -> *)
    build_comp 
      t
      vm_st =
    (op, vm_st') ->
    op = Some tt.
Proof.
  induction t; intros.
  -
    destruct a;
      try (df; tauto).
    (*
    +
      df.
      reflexivity.
      cbn in *.
      subst.
      cbn in *.
      repeat find_inversion.
      reflexivity.
    +
      cbn in *.
      subst.
      cbn in *.
      repeat find_inversion.
      reflexivity.
    +
      cbn in *.
      subst.
      cbn in *.
      repeat find_inversion.
      reflexivity.
    +
      cbn in *.
      subst.
      cbn in *.
      repeat find_inversion.
      reflexivity. *)
  -
    df.
    dohtac.
    df.
    tauto.
    (*


    
    cbn in *.
    repeat break_let.
    simpl in *.
    subst.
    cbn in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    cbn in *.
    dohtac.
    repeat find_inversion.
    repeat break_let.
    monad_unfold.
    repeat find_inversion.
    reflexivity. *)
  -
    df.
    (*
    do_wf_pieces.
     *)
    
    (*
    
    


    
    subst.
    cbn in *.
    repeat break_let.
    simpl in *.
    monad_unfold. *)
    (*
    destruct (build_comp t1 vm_st) eqn:hi. *)
    
    destruct o eqn:hhh;
      try (df; eauto).
    (*
    +
      df.
      eauto.
    +
      df.
      eauto.
      
    repeat break_let.
    repeat find_inversion.
    eapply IHt2; eauto.
    df.
    edestruct IHt1; eauto. *)
    
    (*
    reflexivity.
    rewrite Heqp0.
    simpl.
    eassumption.
    repeat find_inversion.
    edestruct IHt'1.
    reflexivity.
    rewrite Heqp.
    simpl.
    eassumption.
    reflexivity. *)
    (*
  -
    df.
    (*
    do_wf_pieces. *)
    (*
    cbn in *.
    repeat break_let.
    simpl in *.
    subst.
    cbn in *.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    simpl in *. *)

    repeat break_match;
      try (
          df; eauto).

    (*
      repeat find_inversion;
      try eauto. *)
    
    (*
    +
      edestruct IHt2; eauto.
      reflexivity.
      rewrite Heqp0.
      simpl.
      eassumption.
      reflexivity.
    +
      edestruct IHt'1.
      reflexivity.
      rewrite Heqp.
      simpl.
      eassumption.
      reflexivity.
    +
      edestruct IHt'1.
      reflexivity.
      rewrite Heqp.
      simpl.
      eassumption.
      reflexivity. *)
  -
    df.
    Print dohtac.
    Print htac.
    dohtac.
    df.
    dohtac.
    repeat break_match; try solve_by_inversion;
      df;
      try (eauto; tauto);
      try (df; dohtac; solve_by_inversion).

    (*
    +
      df.
      eauto.
    +
      df.
      eauto.
    +
      df.
      dohtac.
      solve_by_inversion.
    +
      df.
      dohtac.
      solve_by_inversion.
     *)
    
      
      
      
      
        
      
    (*do_wf_pieces. *)
    
    (*
    cbn in *.
    repeat break_let.
    simpl in *.
    subst.
    cbn in *.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    simpl in *. *)


    (*
    repeat (dohtac; df).
    df.
    dohtac.
    eauto.
    dohtac.
    df.
    dohtac.
    df.
    eauto. *)
*)
Defined.


(*
    repeat break_match;
      repeat find_inversion;
      try eauto.



          
          assert (abpar (n, (S n1)) (s0,s1) a a0 = snd (anno (bpar (s0,s1) t'1 t'2) n)).
          {
            cbn.
            repeat break_let.
            simpl.
            repeat find_inversion.
            subst.
            repeat find_inversion.
            
            rewrite Heqp2 in *.
            repeat find_inversion.
            reflexivity.
          }
          
          
          Ltac abpar_restore_htac :=
            let G := fresh in
            let HH := fresh in
            let HHH := fresh in
            let blah := fresh in
            let blah' := fresh in
            match goal with
            | [H2: context[abpar (?p', _) (?s0, ?s1) ?a ?a0],
                   H: anno ?t'1 (S ?p') = (_,?a),
                      H': anno ?t'2 _ = (_,?a0) |- _] =>
              assert ( exists r b,
                         abpar r b a a0 = snd(anno (bpar (s0,s1) t'1 t'2) p')) as G by dooit
            end;
            destruct G as [blah HH];
            destruct HH as [blah' HHH];
            dohtac;
            clear HHH;
            clear blah;
            clear blah';
            df;
            dohtac;
            df.
          unfold get_store_at in *.
          monad_unfold.

          abpar_restore_htac.
          repeat break_let.
          unfold get_store_at in *.
          monad_unfold.
          repeat break_let.
          df.
          assert (abpar (n, (S n1)) (s0,s1) a a0 = snd (anno (bpar (s0,s1) t'1 t'2) n)).
          {
            cbn.
            repeat break_let.
            simpl.
            repeat find_inversion.
            subst.
            repeat find_inversion.
            
            rewrite Heqp4 in *.
            repeat find_inversion.
            reflexivity.
          }
          abpar_restore_htac.
          Defined.

Check always_some.
*)

Lemma gen_foo : forall t (*t' n*) m k e p o v,
    (*t = snd (anno t' n) -> *)
    (*well_formed t -> *)
    build_comp t
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |} =
    (Some tt, v) -> 
    st_trace
      (snd (build_comp t
                       {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |})) =
    m ++ st_trace (snd (build_comp t
                       {| st_ev := e; st_trace := k; st_pl := p; st_store := o |})).
Proof.
  (*
  intros.
  rewrite H0.
  simpl.
  vmsts.
  simpl in *. *)
  induction t; intros.
  -
    destruct r.
    destruct a;
      simpl;
      repeat rewrite app_assoc;
      reflexivity.
  -
    df.
    (*
    simpl in *.
    repeat break_let.
    monad_unfold.
    destruct r.
    unfold get_store_at in *.
    monad_unfold. *)
    dohtac.
    df.
    (*
    repeat find_inversion.
    simpl. *)
    repeat rewrite app_assoc.
    reflexivity.
  -
    df.
    annogo.
    
    (*


    do_wf_pieces.
        
    
    monad_unfold. *)

    (*
    
    destruct (build_comp t1 {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}) eqn:hey.
    vmsts. *)

    dosome.

    (*

    
    destruct o0; try solve_by_inversion.
    df. *)
    (*
    repeat break_let.
    vmsts. *)
    (*
    destruct o1; try solve_by_inversion; try build_contra.
    repeat find_inversion.
    destruct o2; try solve_by_inversion; try (dohi'; build_contra).
    
    repeat find_inversion. 
    repeat dunit.
    simpl. *)

    assert (o4 = Some tt).
    {
      eapply always_some; eauto.
    }
    subst.
    df.

    assert (o3 = Some tt).
    {
      eapply always_some; eauto.
    }
    subst.
    df.
    
    

    dohi'.

    assert (StVM.st_trace (
                snd (build_comp t1 {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}
              )) =
            m ++
              StVM.st_trace
              (snd (build_comp t1 {| st_ev := e; st_trace := k; st_pl := p; st_store := o |}))).
    eapply IHt1; eauto.
    (*try jkjk; eauto. *)
    subst'.
    (*
    rewrite hey in *.
    simpl in *. 
    subst. *)
    subst'.
    (*
    rewrite Heqp3 in *. clear Heqp3. *)
    simpl in *.
    subst.

    assert (
        StVM.st_trace
          (snd (build_comp t2
                {| st_ev := st_ev0; st_trace := m ++ st_trace0; st_pl := st_pl0; st_store := st_store0 |})) =
         m ++
           StVM.st_trace (snd (build_comp t2 {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store0 |}))) as HH.
    eapply IHt2; eauto.
    (*try jkjk; eauto. *)
    repeat (subst'; simpl in * ).
    eauto.
    (*
    
    rewrite Heqp4 in H.
    simpl in *.
    rewrite <- H.
    (*try jkjk; eauto. *)
    rewrite Heqp2.
    simpl.
    reflexivity.   *)

    (*

  - (* abseq case *)
    Ltac df' :=
      repeat (cbn in *; unfold runSt in *; repeat break_let; repeat (monad_unfold; cbn in *; find_inversion); monad_unfold; repeat dunit).
    annogo.
        (*
    do_wf_pieces.
    df'.
         *)
    
    (*
    monad_unfold.
    repeat break_let.
    repeat find_inversion. *)
    df.

    

    

    dosome.
    (*
    
    destruct o4; try solve_by_inversion.
    Print df.
    df. *)

    (*
    df'.
     *)



    
    (*
    
    destruct o8; try solve_by_inversion.
    df.
     *)
    

    assert (o18 = Some tt).
    { eapply always_some; eauto. }
    subst.
    df.
    assert (o14 = Some tt).
    {
      eapply always_some; eauto. 
    }
    subst.
    df.
    annogo.

    

    (*
    assert (o14 = Some tt).
    { eapply always_some; eauto. }
    subst.
    df.

    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    repeat break_match;
      repeat find_inversion;
      vmsts; repeat dunit;
        try (try dohi'; build_contra; tauto).

    admit. *)
    
      
   
    annogo.
    df.
    dohi'.
    (*
    df'.
    dohi'.
    df'. *)
    df.

    assert (
        StVM.st_trace
           (snd (build_comp t1 {| st_ev := splitEv s0 e; st_trace := m ++ (k ++ [Term.split n p]); st_pl := p; st_store := o |})) =
         m ++
         StVM.st_trace
         (snd (build_comp t1 {| st_ev := splitEv s0 e; st_trace := k ++ [Term.split n p]; st_pl := p; st_store := o |}))).
    (* repeat (rewrite <- app_assoc in Heqp4). *)
    rewrite <- app_assoc in Heqp4.
    eapply IHt1; eauto.

    (*
    eassumption.
    rewrite <- app_assoc in Heqp4.
    eassumption.

    
    
    eapply IHt1; eauto. *)
    subst'.
    (*
    rewrite Heqp13 in *.
    df'. *)
    df.
    rewrite app_assoc in *.
    subst'.
    df.
    (*
    rewrite Heqp4 in *.
    df'. *)
    
    subst.

    assert (
         StVM.st_trace (snd (build_comp t2{| st_ev := splitEv s1 e; st_trace := m ++ st_trace0; st_pl := st_pl0; st_store := st_store0 |})) =
         m ++ StVM.st_trace (snd (build_comp t2 {| st_ev := splitEv s1 e; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store0 |}))
      ).
    eapply IHt2; eauto.
    subst'.
    df.
    tauto.
    
    (*
    rewrite Heqp8 in *.
    df'. *)
    (*
    rewrite Heqp17 in *.
    df'.
     *)

    (*
    subst'.
    rewrite H0.
    rewrite app_assoc.
    tauto. *)


    (*

    edestruct IHt2.
    eassumption.
    eassumption.
    
    subst'.

    df'.
    rewrite app_assoc in H0.
    rewrite Heqp4 in *.
    df'.
    subst'.
    df'.
    subst.
    




    
    rewrite Heqp14 in *.
    simpl in H2.
    rewrite H2 in *.
    df.
    annogo.
    dohi'.
    df.
    subst'.
    df.
    subst'.
    df.
    annogo.
    dohi'.
    df.


    (*
    eapply IHt2.
    (*
    eassumption.
    eassumption.
    eapply IHt1; eauto.
    try jkjk; eauto. *)
    subst.

    annogo.

    dohi'.

    eapply IHt2. *)
    

    assert (
        StVM.st_trace
           (snd (build_comp t2 {| st_ev := splitEv s1 e; st_trace := m ++ k ++ [Term.split n p]; st_pl := p; st_store := o |})) =
         m ++
         StVM.st_trace
         (snd (build_comp t2 {| st_ev := splitEv s1 e; st_trace := k ++ [Term.split n p]; st_pl := p; st_store := o |}))).
    eapply IHt2; eauto.
    try jkjk; eauto.
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
    rewrite Heqp10 in H1.
    simpl in H1.

    dohi'.
       
    rewrite Heqp19 in *.
    simpl.
    rewrite app_assoc.
    reflexivity.
*)

  -
    repeat (df; dohtac).
    repeat break_match; df;
      subst';
      repeat (rewrite app_assoc);
      try tauto;
      try solve_by_inversion.

    (*

      try solve_by_inversion.

    +
      df.
      subst'.
      repeat (rewrite app_assoc).
      tauto.
    +
      df.
      subst'.
      repeat (rewrite app_assoc).
      tauto.
    +
      repeat find_inversion.
    +
      repeat find_inversion.
    +
      df.
      subst'.
      solve_by_inversion.
    +
      df.
      subst'.
      solve_by_inversion.
    +
      repeat find_inversion.
    +
      repeat find_inversion.  *) 
*)
Defined.

(* Instance of gen_foo where k=[] *)
Lemma foo : forall t (*t' n*) m e p o v,
    (*t = snd (anno t' n) -> *)
    (*well_formed t -> *)
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

Lemma alseq_decomp : forall r (*n t1 t2*) t1' t2' e e'' p p'' o o'' tr,
    (*(alseq r t1' t2') = snd (anno (lseq t1 t2) n) ->  *)
    (*well_formed (alseq r t1' t2') -> *)
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
  (*
  do_wf_pieces.
   *)
  df.
  (*
  simpl in *.
  repeat break_let.
  monad_unfold. *)

  dosome.

  (*
  
  
  destruct o0; try solve_by_inversion.
  df. *)
  annogo.
  (*
  repeat break_let.
  vmsts.
  repeat find_inversion. 
  repeat dunit. *)
  exists st_ev. exists st_trace. exists st_pl. exists st_store.
  split.
  reflexivity.
  destruct (build_comp t2' {| st_ev := st_ev; st_trace := []; st_pl := st_pl; st_store := st_store |}) eqn:hey.
  vmsts.
  destruct o0; try build_contra.
  annogo.

  exists st_trace0.
  Check hihi.
  dohi'.
  
  split.
  reflexivity.

  (*

  
  destruct (build_comp t2' {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:heyy.
  vmsts.
  destruct o0; try solve_by_inversion.
  repeat dunit.
  
  repeat find_inversion. *)

  Check foo.

  pose foo.
  specialize foo with (t:= t2') (m:=st_trace) (e:=st_ev) (p:= st_pl) (o:=st_store) (*(t':=t2) (n:=n0)*) (v:={| st_ev := st_ev0; st_trace := tr; st_pl := st_pl0; st_store := st_store0 |}).
  intros.
  (*
  pose (H0 H2). *)
  repeat concludes.
  subst'.
  (*
  rewrite Heqp1 in *.
  df'. *)
  df.
  tauto.
  (*
  rewrite hey in *.
  df'.
  eassumption. *)
  
  (*
  rewrite Heqp3.
  simpl.
  rewrite hey.
  simpl.
  intros.
  apply H; try reflexivity.
  try jkjk; eauto.
   *)
  
Defined.

Lemma trace_irrel_store' : forall t (*t' n*) tr1 tr1' tr2 e e' p1' p1 o' o,
    (*t = snd (anno t' n) -> *)
    (*well_formed t -> *)
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
  simpl.
  vmsts.
  simpl.
  destruct o0; repeat dunit.
  - repeat dohi.
    tauto.
  -
    exfalso.
    eapply fafaf; eauto.
Defined.

Lemma trace_irrel_pl' : forall t (*t' n*) tr1 tr1' tr2 e e' p1' p1 o' o,
    (*t = snd (anno t' n) -> *)
    (*well_formed t -> *)
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
    tauto.
  -
    exfalso.
    eapply fafaf; eauto.
Defined.

Lemma trace_irrel_ev' : forall t (*t' n*) tr1 tr1' tr2 e e' p1' p1 o' o,
    (*t = snd (anno t' n) -> *)
    (*well_formed t -> *)
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

(*
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
*)

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

(*
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
*)

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

Ltac jkjk' :=
  match goal with
  | H: _ |- _ => rewrite H; reflexivity
  end.

Lemma pl_immut : forall t e tr p o,
    (*t = snd (anno t' n) -> *)
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
  -
    df.
    (*

    simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let. *)
    
    dohtac.
    df.
    reflexivity.
    (*
    repeat find_inversion.
    simpl.
    reflexivity. *)
  -
    
    
    simpl in *.
    monad_unfold.
    repeat break_match;
      try solve_by_inversion.
    df.

    (*
    simpl.
    repeat dunit.
    vmsts.
    simpl.

    Print annogo.
    vmsts; repeat dunit; simpl in *; repeat break_let; simpl in *.
     *)
    annogo.
    simpl.
    
    
(*
    annogo. 
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

    (*
    annogo.
    
    symmetry.
       
    edestruct IHt1.
    jkjk; eauto.
    jkjk'; eauto. *)

    (*
  -
    annogo.
    (*
    vmsts; repeat dunit; simpl in *; repeat break_let; simpl in *. *)
    (*
    annogo.
     *)
    df.
    (*
    
        
    simpl in *.
    repeat break_let.
    monad_unfold.
    repeat break_let. *)
    
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
      (*
      jkjk'; eauto.
       *)
      
    }

    assert (st_pl0 = st_pl).
    {     
      edestruct IHt2;
      jkjk'; eauto.
    }

    congruence.
    +
      assert (p = st_pl).
      {
        edestruct IHt1;
          jkjk'; eauto.
      }

      assert (st_pl = st_pl0).
      {
        edestruct IHt2;
          jkjk'; eauto.
      }

      congruence.
    +
      symmetry.
      edestruct IHt1;
      jkjk'; eauto.
    +
      symmetry.
      edestruct IHt1;
      jkjk'; eauto.
  -
    df.
    (*
    simpl in *.
    monad_unfold.
    repeat break_let.
    simpl in *.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let. *)

    dohtac.
    df.
    (*
    
    repeat find_inversion. *)




    
    repeat break_match;
      try solve_by_inversion;
    repeat find_inversion;
    simpl in *;
      try
        reflexivity.
*)
Defined.

Ltac do_pl_immut :=
  let tac :=
      (symmetry;
       erewrite <- pl_immut in *;
       jkjk'
      ) in
  repeat (
      match goal with
      | [H: build_comp _ {| st_ev := _; st_trace := _;
                                                    st_pl := ?p;
                                                             st_store := _ |} =
            (_,
             {| st_ev := _; st_trace := _;
                                        st_pl := ?p';
                                                 st_store := _ |}) |- _] =>
        assert_new_proof_by (p = p') (tac)     
      end); subst.

(*
Lemma restl' : forall t t' n e e' x tr p p' o o' e2 e2' p2 p2' o2 o2' tr',
    t = snd (anno t' n) -> 
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |}) ->

    build_comp t {| st_ev := e2; st_trace := []; st_pl := p2; st_store := o2 |} =
    (Some tt, {| st_ev := e2'; st_trace := tr'; st_pl := p2'; st_store := o2' |}) ->
    tr = tr'.
Proof.
  intros.
  
  assert (
      st_trace (run_vm t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |}) =
      st_trace ({| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |})).
  {
  unfold run_vm.
  monad_unfold.
  rewrite H0.
  simpl.
  reflexivity.
  }

  assert (
      st_trace (run_vm t {| st_ev := e2; st_trace := []; st_pl := p2; st_store := o2 |}) =
      st_trace ({| st_ev := e2'; st_trace := tr'; st_pl := p2'; st_store := o2' |})).
  {
  unfold run_vm.
  monad_unfold.
  rewrite H1.
  simpl.
  reflexivity.
  }
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
   st_ev
         (snd
            (build_comp t
               {| st_ev := e2; st_trace := []; st_pl := p2; st_store := o2 |})) = e2').
  eapply trace_irrel_ev'; eauto.

  

  assert (
   st_pl
         (snd
            (build_comp t
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |})) = p').
  eapply trace_irrel_pl'; eauto.

  assert (
   st_pl
         (snd
            (build_comp t
               {| st_ev := e2; st_trace := []; st_pl := p2; st_store := o2 |})) = p2').
  eapply trace_irrel_pl'; eauto.

  assert (
   st_store
         (snd
            (build_comp t
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |})) = o').
  eapply trace_irrel_store'; eauto.

  assert (
   st_store
         (snd
            (build_comp t
               {| st_ev := e2; st_trace := []; st_pl := p2; st_store := o2 |})) = o2').
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
    erewrite foo in H2; eauto.
    eapply app_inv_head.
    eauto.

  }

  assert (
      (snd
         (build_comp t
                     {| st_ev := e2; st_trace := []; st_pl := p2; st_store := o2 |})) =
      {| st_ev := e2'; st_trace := tr'; st_pl := p2'; st_store := o2' |}).
  {
    eapply st_congr; eauto.
  }

  (*
  
    Check foo.
    erewrite foo in H2; eauto.
    eapply app_inv_head.
    eauto.

  } *)
  
  destruct (build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |}) eqn:aa.
  destruct (build_comp t {| st_ev := e2; st_trace := []; st_pl := p2; st_store := o2 |}) eqn:aaa.
  simpl in *.
  vmsts.
  simpl in *.
  repeat find_inversion.
  destruct o0.
  destruct u.
  rewrite H0 in *.
  simpl in *.
  clear H2.
  subst.
  reflexivity.
  exfalso.
  eapply fafaf; eauto.
Defined.
*)




Lemma restl' : forall t (*t' n*) e e' x tr p p' o o',
    (*t = snd (anno t' n) ->  *)
    (*well_formed t -> *)
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |}) ->

    build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
Proof.
  intros.
  
  assert (
      st_trace (run_vm t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |}) =
      st_trace ({| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |})).
  {
  unfold run_vm.
  
  monad_unfold.
  subst'.
  (*
  rewrite H0. *)
  simpl.
  reflexivity.
  }
  
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
    erewrite foo in H0; eauto.
    eapply app_inv_head.
    eauto.

  }
  
  destruct (build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:aa.
  simpl in *.
  vmsts.
  simpl in *.
  repeat find_inversion.
  assert (o0 = Some tt).
  {
    eapply always_some; eauto.
  }
  subst.
  tauto.
  (*
  
   
  destruct o0.
  annogo.
  (*
  destruct u. *)
  reflexivity.
  exfalso.
  eapply fafaf; eauto. *)
Defined.

Lemma restl'_2
  : forall (t : AnnoTerm) (e e' : EvidenceC) (x tr : list Ev) (p p' : nat) (o o' : ev_store) (*t' n*),
    (*t = snd (anno t' n) -> *)
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |}) ->
    build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
Proof.
  intros.
  Check restl'.
  eapply restl'; eauto.
Defined.

Lemma store_get_set : forall e tr p o n e1 e' v0,
    get_store_at n
      {|
        st_ev := e;
        st_trace := tr;
        st_pl := p;
        st_store := map_set o n e1 |} =
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
       st_store := map_set o n e1 |} =
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

Check eval.
Print eval.
Print eval_asp.
Check build_comp.

Lemma suffix_prop : forall t (*t' n*) e e' tr tr' p p' o o',
    (*t = snd (anno t' n) -> *)
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
  subst'.
  (*
  rewrite H. *)
  simpl.
  reflexivity.

  simpl in H00.
  eexists.
  rewrite <- H00.
  erewrite foo; eauto.
Defined.

Lemma evshape_at : forall e es t n,
    Ev_Shape e es ->
    Ev_Shape (toRemote (unanno t) e) (Term.eval (unanno t) n es).
Proof.
Admitted.



Lemma evshape_par : forall e es a p,
    Ev_Shape e es ->
    Ev_Shape (parallel_att_vm_thread a e)
             (Term.eval (unanno a) p es).
Proof.
Admitted.

Check toRemote.

Definition remote_evidence (t:AnnoTerm) (e:EvidenceC) : EvidenceC.
Admitted.

Definition remote_trace (t:AnnoTerm) (p:Plc) : list Ev.
Admitted.

Check pl_immut.

Axiom build_comp_external' : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store) (tr:list Ev),
    build_comp t {| st_ev := e; st_trace := tr; st_pl := n; st_store := o |} =
    (Some tt,
     {| st_ev := remote_evidence t e;
        st_trace := tr ++ (remote_trace t n);
        st_pl :=
          st_pl
            (snd 
               (build_comp t
                           {| st_ev := e;
                              st_trace := [];
                              st_pl := n;
                              st_store := o |}));
        st_store :=
          st_store
            (snd 
               (build_comp t
                           {| st_ev := e;
                              st_trace := [];
                              st_pl := n;
                              st_store := o |}));
     |}).

Lemma build_comp_external : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store),
    build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |} =
    (Some tt,
     {| st_ev := remote_evidence t e;
        st_trace := remote_trace t n;
        st_pl :=
          st_pl
            (snd 
               (build_comp t
                           {| st_ev := e;
                              st_trace := [];
                              st_pl := n;
                              st_store := o |}));
        st_store :=
          st_store
            (snd 
               (build_comp t
                           {| st_ev := e;
                              st_trace := [];
                              st_pl := n;
                              st_store := o |}));
     |}).
Proof.
  intros.
  assert ([] ++ (remote_trace t n) = (remote_trace t n)) by eauto.
  eapply build_comp_external'.
Defined.

  

Axiom at_evidence : forall t e,
    toRemote (unanno t) e = remote_evidence t e.

Axiom at_events : forall t p,
  remote_events t p = remote_trace t p.

Axiom par_evidence : forall t e,
    parallel_att_vm_thread t e = remote_evidence t e.

Axiom par_events : forall t p,
  parallel_vm_events t p = remote_trace t p.


Lemma build_comp_at' : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store) (tr: list Ev),
    build_comp t {| st_ev := e; st_trace := tr; st_pl := n; st_store := o |} =
    (Some tt,
     {| st_ev := toRemote (unanno t) e;
        st_trace := tr ++ remote_events t n;
        st_pl := n;
        st_store :=
          st_store
            (snd 
               (build_comp t
                           {| st_ev := e;
                              st_trace := [];
                              st_pl := n;
                              st_store := o |}));
     |}).
Proof.
  intros.
  rewrite at_evidence.
  rewrite at_events.
  Check pl_immut.
  assert (st_pl (snd (build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |})) = n).
  eapply pl_immut.
  rewrite <- H at 3.

  eapply build_comp_external'.
Defined.


Lemma build_comp_at : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store),
    build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |} =
    (Some tt,
     {| st_ev := toRemote (unanno t) e;
        st_trace := remote_events t n;
        st_pl := n;
        st_store :=
          st_store
            (snd 
               (build_comp t
                           {| st_ev := e;
                              st_trace := [];
                              st_pl := n;
                              st_store := o |}));
     |}).
Proof.
  intros.
  rewrite at_evidence.
  rewrite at_events.
  Check pl_immut.
  assert (st_pl (snd (build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |})) = n).
  eapply pl_immut.
  rewrite <- H at 3.

  eapply build_comp_external.
Defined.

Lemma build_comp_par' :
  forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store) (tr:list Ev),
    build_comp t {| st_ev := e; st_trace := tr; st_pl := n; st_store := o |} =
    (Some tt,
     {|
       st_ev := parallel_att_vm_thread t e;
       st_trace := tr ++ parallel_vm_events t n;
       st_pl := n;
       st_store :=
         st_store
           (snd
              (build_comp t
                          {| st_ev := e;
                             st_trace := [];
                             st_pl := n;
                             st_store := o |}))
     |}).
Proof.
  intros.
  rewrite par_evidence.
  rewrite par_events.
  Check pl_immut.
  assert (st_pl (snd (build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |})) = n).
  eapply pl_immut.
  rewrite <- H at 3.

  eapply build_comp_external'.
Defined.


Lemma build_comp_par :
  forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store),
    build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |} =
    (Some tt,
     {|
       st_ev := parallel_att_vm_thread t e;
       st_trace := parallel_vm_events t n;
       st_pl := n;
       st_store :=
         st_store
           (snd
              (build_comp t
                          {| st_ev := e;
                             st_trace := [];
                             st_pl := n;
                             st_store := o |}))
     |}).
Proof.
  intros.
  rewrite par_evidence.
  rewrite par_events.
  Check pl_immut.
  assert (st_pl (snd (build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |})) = n).
  eapply pl_immut.
  rewrite <- H at 3.

  eapply build_comp_external.
Defined.

Ltac evShapeFacts :=
  match goal with
  | [H: Ev_Shape mtc _ |- _] => invc H
  | [H: Ev_Shape _ mt |- _] => invc H
  | [H: Ev_Shape (uuc _ _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (uu _ _ _ _) |- _] => invc H
  | [H: Ev_Shape (ggc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (gg _ _) |- _] => invc H
 (* | [H: Ev_Shape (hhc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (hh _ _) |- _] => invc H *)
                                        (*
  | [H: Ev_Shape (nnc _ _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (nn _ _) |- _] => invc H
  | [H: Ev_Shape (ssc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (ss _ _) |- _] => invc H
  | [H: Ev_Shape (ppc _ _) _ |- _] => invc H
  | [H: Ev_Shape _ (pp _ _) |- _] => invc H *)
  end.



  

Lemma multi_ev_eval : forall t (*t' n*) tr tr' e e' p p' o o' es e's,
    (*t = snd (anno t' n) -> *)
    well_formed t ->
    build_comp t (mk_st e tr p o) = (Some tt, (mk_st e' tr' p' o')) ->
    Ev_Shape e es ->
    Term.eval (unanno t) p es = e's ->
    Ev_Shape e' e's.
Proof.
  induction t; intros.
  -
    destruct a;
      try (
          df;
          (*
          simpl in *;
          cbn in *;
          unfold run_vm in *;
          monad_unfold;
          repeat break_let;
          monad_unfold;
          repeat find_inversion; *)
          eauto).
      
  -
    do_wf_pieces.
    df.
    (*
     simpl in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      repeat break_let.
      
      repeat find_inversion.
      unfold get_store_at in *.
      monad_unfold.
      repeat break_let. *)
    dohtac.
    df.
    (*
      repeat find_inversion. *)

      
      annogo.
      (*clear H. *)
      eapply IHt.
      eassumption.
      (*
      subst'.
      rewrite Heqp.
      reflexivity. *)
      Check build_comp_at. 
      eapply build_comp_at.
      eassumption.
      reflexivity.
      

      
      (*
      eapply evshape_at; eauto.
       *)
                           

  -
    do_wf_pieces.

    (*
    destruct t';
      try (
          inv H;
          repeat break_let;
          simpl in *;
          solve_by_inversion). *)

    (*
    Check alseq_decomp.
    annogo.

    Print alseq_decomp. *)

    edestruct suffix_prop.
    eassumption.
    subst.

    edestruct alseq_decomp; eauto.
    eapply restl'.
    eassumption.

    destruct_conjs.
    (*
    clear H0. *)
    df.
    (*
    cbn in *.
    repeat break_let.
    inv H. *)
    
    eapply IHt2.
    (*
    +
      
      rewrite Heqp1.
      reflexivity. *)
    +
      eassumption.
    +
      
      eassumption.
    + eapply IHt1.
      (*
      ++
      rewrite Heqp0. 
      reflexivity. *)
      ++ eassumption.
      ++ eassumption.
        
      ++ eassumption.
      ++
        reflexivity.
    +
      do_pl_immut.
      (*
      assert (H4 = p).
      {
        Check pl_immut.
        erewrite <- pl_immut with (t:=a).
        rewrite H6.
        simpl. reflexivity.
        (*
        rewrite Heqp0.
        reflexivity. *)
      } *)
      congruence.
      (*
  -
    do_wf_pieces.

    (*
    destruct t';
      try (
          inv H;
          repeat break_let;
          simpl in *;
          solve_by_inversion). *)
    df.
    (*

    cbn in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    repeat find_inversion. *)
    repeat break_match;
      try solve_by_inversion.
    +
      df.
      (*
      
      repeat find_inversion.
      repeat dunit.
      vmsts. *)
      annogo.
      simpl in *.
      assert (exists l, st_trace0 = [Term.split n p] ++ l) as H00.
      {
        
        eapply suffix_prop.
        (*rewrite Heqp0. reflexivity. *)
        simpl.
        eassumption.
      }
      destruct_conjs.
      subst.
      assert (exists l, st_trace = ([Term.split n p] ++ H00) ++ l) as H00'.
      {
        
        
        eapply suffix_prop.
        (*rewrite Heqp1. reflexivity. *)
        simpl.
        eassumption.
      }
      destruct_conjs; subst.
      assert (
           build_comp t1
            {|
            st_ev := splitEv s0 e;
            st_trace := [];
            st_pl := p;
            st_store := o |} =
          (Some tt,
          {|
          st_ev := st_ev0;
          st_trace := H00;
          st_pl := st_pl0;
          st_store := st_store0 |})).
      {
        eapply restl'_2 with (x:= [Term.split n p]) (*(t':=t'1) (n:=(S n))*).
        (*
        rewrite Heqp0.
        reflexivity. *)
        eassumption.
      }
      assert (
           build_comp t2
            {|
            st_ev := splitEv s1 e;
            st_trace := [];
            st_pl := st_pl0;
            st_store := st_store0 |} =
          (Some tt,
          {|
          st_ev := st_ev;
          st_trace := H00';
          st_pl := st_pl;
          st_store := st_store |})).
      {
        eapply restl'_2 with (x:= ([Term.split n p] ++ H00)) (*(t':=t'2) (n:=n2)*).
        (* rewrite Heqp1.
        reflexivity. *)
        eassumption.
      }
      
      econstructor.
      destruct s0.
      ++
        eapply IHt1.
        (*
        +++
      rewrite Heqp0.
      reflexivity. *)
      +++
        eassumption.
      +++
        eassumption.
        
      +++
        
        destruct e;
        
          try (
              evShapeFacts;
             econstructor; eauto).
      +++
        simpl.
        eauto.
      ++
        simpl in *.
        eapply IHt1.
        (*
        rewrite Heqp0.
        reflexivity. *)
        eassumption.
        eassumption.
        econstructor.
        reflexivity.
      ++
        destruct s1.
        +++
          simpl.
          eapply IHt2.
          (*
          rewrite Heqp1.
          reflexivity. *)
          eassumption.
          eassumption.
          destruct e;
            try (evShapeFacts;
                 econstructor; eauto).
          do_pl_immut.
          congruence.

          (*

          assert (st_pl0 = p).
          {
            Check pl_immut.
            erewrite <- pl_immut with (t:=a).
            rewrite Heqp6.
            simpl. reflexivity.
            (*
            rewrite Heqp0.
            reflexivity. *)
          }
          congruence. *)
        +++
          simpl.
          eapply IHt2.
          (*
          rewrite Heqp1.
          reflexivity. *)
          eassumption.
          eassumption.
          econstructor.
          do_pl_immut.
          (*
          assert (st_pl0 = p).
          {
            Check pl_immut.
            erewrite <- pl_immut with (t:=a).
            rewrite Heqp6.
            simpl. reflexivity.
            (*
            rewrite Heqp0.
            reflexivity. *)
          } *)
          congruence.
    +
      repeat find_inversion.
  -
    do_wf_pieces.

    (*

    destruct t';
      try (
          inv H;
          repeat break_let;
          simpl in *;
          solve_by_inversion). *)

    df.
    (*

    cbn in *.
    repeat break_let.
    monad_unfold.
    repeat break_let.
    repeat find_inversion.
    monad_unfold.
    unfold get_store_at in *.
    monad_unfold. *)
    
    dohtac.
    df.

    (*

    repeat break_let. *)
    dohtac.
    monad_unfold.
    repeat find_inversion.
    dosome.
    (*
    destruct o4; try solve_by_inversion.
    repeat break_let.
    repeat find_inversion. 
    
    destruct o5; try solve_by_inversion.
    repeat find_inversion. *)



    (*
    repeat break_match; try solve_by_inversion.
    +
      df.
      repeat break_match; try solve_by_inversion.
      ++
        df.
        econstructor. *)

    (*

    

    assert (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false).
    {
      admit.
      (*
      Check h.
      eapply h with  (b:=(s1,s2)) (t:= bpar (s1, s2)  t'1 t'2) (n:=n).
      cbn.
      repeat break_let.
      repeat find_inversion.
      simpl.
      rewrite Heqp5 in *.
      repeat find_inversion.
      reflexivity. *)
    }
    rewrite H in *.
    df.
    (*
    repeat find_inversion.
    simpl in *. *)
    dohtac.
    df.
     *)
    
    econstructor.
    (*
    repeat find_inversion.
    econstructor. *)


    

    destruct s0.
    +
      simpl.
      eapply IHt1; eauto.
      (*
      rewrite Heqp0.
      reflexivity. *)

      
      eapply build_comp_par.
    +
      simpl.
      eapply IHt1.
      (*
      rewrite Heqp0.
      reflexivity. *)
      eassumption.
      eapply build_comp_par.
      econstructor.
      eauto.
    +
      destruct s1.
      ++
        simpl.
        eapply IHt2; eauto.
        (*
        rewrite Heqp1.
        reflexivity. *)
        eapply build_comp_par.
      ++
        simpl.
        eapply IHt2.
        (*
        rewrite Heqp1. reflexivity. *)
        eassumption.
        eapply build_comp_par.
        econstructor.
        eauto.
*)
        Unshelve.
        eauto.
        exact (aasp (0,0) (ASPC 1 [])).
        exact mtc.
        eauto.
        eauto.
        (*
        exact (aasp (0,0) (ASPC 1 [])).
        exact mtc.
        eauto.
        eauto.
        exact (aasp (0,0) (ASPC 1 [])).
        exact mtc.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
 *)

Defined.

  (*      
     (*   
        
      simpl.
      eapply IHt2; eauto.
      rewrite Heqp1.
      reflexivity.
      eapply build_comp_par.
      
    
      

    
    eapply IHt1; eauto.
    rewrite Heqp0.
    reflexivity.
    Print build_comp_at.

    admit.
    destruct s1.
    +
      simpl.
      reflexivity.

    + simpl.
     *)

      destruct s1;
      destruct s2;
      try
        eapply evshape_par; eauto.
    eapply evshape_par; eauto.
    destruct s2;
      eauto.
    Unshelve.
    eauto.
Defined.
*)


    (*
    
    
    
    repeat break_match;
      try solve_by_inversion.
    
    
      
      
          
          
          
        
        
        destruct s1.
        ++++
      destruct e;
        try (inv H1;
             econstructor; eauto).
        ++++
      simpl.
      econstructor.
      destruct s1.
      admit.
      simpl.
      reflexivity.
      destruct e.
      ++
        inv H1.
        cbn.
        destruct s1.
        simpl.
        econstructor.
        simpl.
        econstructor.
      ++
        inv H1.
        destruct s1.
        simpl.
        econstructor.
        eauto.
        simpl in *.
        
      
      unfold snd.
      
      eassumption.
      econstructor.
      eapply IHt1.
      ++
      rewrite Heqp0.
      reflexivity.
      ++


      destruct_conjs.
      subst.
      Check restl'_2.
      apply restl'_2 with (x:= [Term.split n p]) (t':=t'1) (n:=(S n)).
      +++ rewrite Heqp0.
         reflexivity.
      +++ apply Heqp6.
        

      
      edestruct restl'.
      Check restl'_2.
      ++
        rewrite Heqp0.
        reflexivity.
      ++
        simpl.
        apply Heqp6.
        
      econstructor.
      eapply IHt1.
      cbn in *.
      rewrite Heqp0.
      reflexivity.
      dunit.
      dunit.
      edestruct restl'.
      rewrite Heqp0.
      reflexivity.
      simpl.
      vmsts.
      simpl in *.
      apply Heqp6.
      eassumption.
      eassumption.
      
      
    
      
        
        
        
      
      
    cbn in *.
    repeat break_let.
    inv H.
    rewrite Heqp1.
    simpl in *.
    repeat find_inversion.
    rewrite Heqp1.

    

    destruct alseq_decomp with (t1 := t'1) (t2:=t'2) (r:=(n,n1)) (n:=n) (t1':=a) (t2':=a0) (e:=e) (e'':=e') (p:=p) (p'':=p') (o:=o) (o'':=o') (tr:=tr)
    cbn.
    repeat break_let.
    simpl.
    repeat find_inversion.
    rewrite Heqp3 in *.
    repeat find_inversion.
    reflexivity.
    Check restl'.
    
    eapply restl' with (t':=lseq t'1 t'2) (n:=n).
    cbn.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    rewrite Heqp3 in *.
    repeat find_inversion.
    reflexivity.
    cbn.
    assert 
      eassumption.

    *)
    
    
    
    (*
    cbn.
    Check restl'.
    eapply restl'.
    rewrite H.
    simpl.
    repeat break_let.
    simpl.
    rewrite <- H.
    destruct r.
    reflexivity.
    
     *)



    
      
      
    




(*
Lemma multi_ev_eval : forall t tr tr' e e' p p' o o' es e's,
    run_vm t
           {| st_ev := e; st_trace := tr; st_pl := p; st_store := o |} =
    {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}  ->
    Ev_Shape e es ->
    Term.eval (unanno t) p es = e's ->
    Ev_Shape e' e's.
Proof.
  induction t; intros.
  -
    destruct a.
    +
      simpl in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      repeat find_inversion.
      eauto.

      (*
      Lemma evshape_determ :
        forall e es es',
          Ev_Shape e es ->
          Ev_Shape e es' ->
          es = es'.
      Proof.
      Admitted.
       
      

      eapply evshape_determ; eauto.
       *)
      
    +
      simpl in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      repeat find_inversion.
      econstructor; eauto.
    +
      simpl in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      repeat find_inversion.
      econstructor; eauto.
    +
      simpl in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      repeat find_inversion.
      econstructor; eauto.
  -
    simpl in *.
      cbn in *.
      unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      repeat break_let.
      
      repeat find_inversion.
      unfold get_store_at in *.
      monad_unfold.
      repeat break_let.
      dohtac.
      repeat find_inversion.
      admit. (* TODO: axiom? *)

  -
    simpl in *.
    cbn in *.
    unfold run_vm in *.
    monad_unfold.
    monad_unfold.
    repeat break_match;
      try solve_by_inversion.
    +
      simpl in *.
      repeat find_inversion.
      vmsts.
      simpl in *.
      repeat find_inversion.
      vmsts.
      dunit.
      destruct o1; try solve_by_inversion.
      ++
        repeat find_inversion.
        eapply IHt2.
        rewrite Heqp1.
        simpl.
        reflexivity.
        eapply IHt1.
        rewrite Heqp0.
        simpl.
        reflexivity.
        eassumption.
        reflexivity.
        assert (st_pl0 = p).
        {
          admit.
        }
        rewrite H.
        reflexivity.
      ++
        eapply IHt2.
        rewrite Heqp1.
        simpl.
        reflexivity.
        eapply IHt1.
        rewrite Heqp0.
        simpl.
        reflexivity.
        eassumption.
        reflexivity.
        assert (st_pl0 = p).
        {
          admit.
        }
        rewrite H.
        reflexivity.
    +
      simpl in *.
      vmsts.
      simpl in *.
      repeat find_inversion.
      
        
        
        
      
    
      
      
      
    
    
      

      inv H1.
      inv H1
      
      
      
    















  
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
*)


(*
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
*)

Lemma get_store_in : forall x st st' o y,
    get_store_at x st = (None, st') ->
    st_store st = o ->
    map_get o x = (Some y) ->
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

(*
Axiom bpar_shuffle : forall x p t1 t2 et1 et2,
    lstar (bp x (conf t1 p et1) (conf t2 p et2))
          (shuffled_events (parallel_vm_events t1 p)
                           (parallel_vm_events t2 p))
          (bp x (stop p (aeval t1 p et1)) (stop p (aeval t2 p et2))).
 *)

(*
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
*)
   




Lemma run_lstar : forall t tr et e e' p p' o o' (*t' n*),
    (*well_formed t ->  *)
    (*t = snd (anno t' n) ->  *)
    build_comp t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o')) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros t tr et e e' p p' o o' (*t' n HH*) H.

  generalizeEverythingElse t.

  (*
  
  generalize dependent tr.
  generalize dependent et.
  generalize dependent p.
  generalize dependent p'.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent o.
  generalize dependent o'.
  generalize dependent t'.
  generalize dependent n. *)
  induction t; intros.
  - (* aasp case *)
    destruct a;
      df; (*
      unfold run_vm in *;
      repeat (monad_unfold; break_let; monad_unfold);
      repeat find_inversion; *)
      econstructor; try (econstructor; reflexivity).
  - (* aatt case *)
    (*do_wf_pieces. *)
    destruct r.
    (*
    simpl in *.
    destruct r.
    unfold run_vm in *.
    monad_unfold.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.
    find_inversion.
    find_inversion.
    monad_unfold. *)
    df.
    dohtac.
    (*
    rewrite PeanoNat.Nat.eqb_refl in *.
    repeat find_inversion. *)
    df.
    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.

    (*

    edestruct afff; eauto.
    destruct_conjs. *)

    eapply IHt; eauto.

    apply build_comp_at.

    econstructor.
    apply stattstop.
    econstructor.
    
  -
    (*
    do_wf_pieces. *)

    (*
    destruct t';
      try (
          inv HH;
          repeat break_let;
          simpl in *;
          solve_by_inversion). *)
    
    edestruct alseq_decomp; eauto.
    destruct_conjs.
             
    econstructor.
    econstructor.

    subst.

    eapply lstar_transitive.

    eapply lstar_stls.
    (*
    inversion HH.
    repeat break_let.
    simpl in *.
    inversion H7. 
    
    rewrite H9 in *.
    rewrite H10 in *. *)
    df.


    eapply IHt1.
    (*
    rewrite Heqp0.
    simpl. reflexivity. *)
    eassumption.
    (*eassumption. *)

    eapply lstar_silent_tran.
    apply stlseqstop.

    (*

    inversion HH.
    repeat break_let.
    simpl in *.
    inversion H7.
    rewrite H9 in *.
    rewrite H10 in *.
    clear H9. clear H10.
     *)
    df.
    do_pl_immut.
    (*

    assert (p = H1).
    {
      edestruct pl_immut.
      simpl.
      jkjk'; eauto.
      (*
      reflexivity.
      rewrite Heqp0.
      reflexivity.
      simpl.
      jkjk'; eauto. *)
    }
    rewrite <- H6 in H5. clear H6. *)
    
    eapply IHt2; eauto.
    (*
      jkjk'; eauto. *)

    (*
  -
    (*
    do_wf_pieces. *)

    (*

    destruct t';
      try (
          inv HH;
          repeat break_let;
          simpl in *;
          solve_by_inversion). *)
    destruct r; destruct s.

    (*
   
    edestruct afaff3; eauto.
    edestruct afaff4; eauto.
    destruct_conjs.
     
    simpl in *.
    repeat break_let.
    invc HH.

    unfold run_vm in *. repeat monad_unfold.
    repeat break_let.
    repeat monad_unfold. *)
    df.
    vmsts.

    (*
    
    repeat find_inversion. *)
    dosome.
    df.
    (*
    repeat break_match;
      repeat find_inversion;
      simpl in *.
     *)
    

    Check restl'.

    assert (exists l, st_trace1 = [Term.split n p] ++ l) as H00.
    eapply suffix_prop.
    eassumption.
    (*
    rewrite Heqp0. reflexivity. 
    simpl.
    rewrite Heqp6. 
    repeat dunit.
    simpl.
    reflexivity. *)

    destruct H00 as [H00 H11].
    subst'.
    (*
    rewrite H11 in *. clear H11. *)

    Check restl'.
    
    assert (build_comp (*(snd (anno x H0))*) t1
                       {| st_ev := splitEv s e; st_trace := []; st_pl := p; st_store := o |} =
            (Some tt, {| st_ev := st_ev1; st_trace := H00; st_pl := st_pl1; st_store := st_store1 |})).
    {
      eapply restl'_2.
      (*
      reflexivity. *)
      (*
      assert ( Term.split n p :: H00 =  [Term.split n p] ++ H00) by reflexivity. *)
      
      
      repeat dunit.
      eassumption.
    }
    
    assert (exists l, st_trace = ([Term.split n p] ++ H00) ++ l) as H000.
    eapply suffix_prop.
    eassumption.
    (*
    rewrite Heqp1. reflexivity. 
    simpl. 
    unfold run_vm.
    monad_unfold.
    rewrite Heqp10. 
    repeat dunit.
    simpl.
    reflexivity. *)
    destruct H000 as [H000 HHH].
    subst'.
    (*
    rewrite HHH in *. clear HHH. *)

    assert (
        build_comp (*(snd (anno x0 H1)) *) t2
                   {| st_ev := splitEv s0 e; st_trace := []; st_pl := st_pl1; st_store := st_store1 |} =
        (Some tt, {| st_ev := st_ev; st_trace := H000; st_pl := p'; st_store := o' |})).
    {
      repeat dunit.
      eapply restl'_2.
      (*
      
      reflexivity.
      
      assert ( Term.split n p :: H00 =  [Term.split n p] ++ H00) by reflexivity. *)
         
      (* rewrite H2 in *. *)
      repeat dunit.
      eassumption.

    }

    repeat do_pl_immut.
    (*
    
    assert (p = st_pl3).
    {
      edestruct pl_immut.
      simpl in *.
      (*
      rewrite Heqp0.
      simpl. reflexivity. *)
      repeat dunit.
                            
      rewrite Heqp6.
      simpl. reflexivity.
    }

    rewrite H3 in *. clear H3. 


    assert (st_pl3 = p').
    {
      edestruct pl_immut.
      (*
      rewrite Heqp1.
      reflexivity. *)
      simpl.
      rewrite Heqp10.
      simpl. reflexivity.
    }
    rewrite H3 in *. clear H3. *)
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
    df.
    (*
    simpl in *.
    monad_unfold.
    repeat break_let.
    unfold get_store_at in *.

    repeat find_inversion.
    monad_unfold.
    repeat break_let. *)
    dosome.

    (*

    dohtac. *)
    df.
    repeat break_match; try solve_by_inversion;
      df.
    +
      repeat break_match; try solve_by_inversion.
      ++
        df.
        econstructor.
        econstructor.
        eapply lstar_transitive.
        simpl.
        apply bpar_shuffle.
        econstructor.
        apply stbpstop.
        econstructor.
      ++
        df.
        dohtac.
        solve_by_inversion.
      ++
        dohtac.
        solve_by_inversion.
    +
      repeat break_match; try solve_by_inversion.
      ++
        df.
        econstructor.
        econstructor.
        eapply lstar_transitive.
        simpl.
        apply bpar_shuffle.
        econstructor.
        apply stbpstop.
        econstructor.
      ++
        dohtac.
        solve_by_inversion.
      ++
        dohtac.
        solve_by_inversion.
    +
      repeat break_match; try solve_by_inversion.
      ++
        df.
        econstructor.
        econstructor.
        eapply lstar_transitive.
        simpl.
        apply bpar_shuffle.
        econstructor.
        apply stbpstop.
        econstructor.
      ++
        dohtac.
        solve_by_inversion.
      ++
        dohtac.
        solve_by_inversion.
      
      
        
        
        
      
        
        
    
      

    (*
         
    destruct t'; inv HH;
      try (
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    repeat break_let.
     
    repeat find_inversion.
    repeat break_let.
    repeat find_inversion.
    simpl in *. *)

     (*   
    df.
    dohtac.
    df. *)

    
    (*
    repeat find_inversion. *)


        (*
    econstructor.
    econstructor.
    eapply lstar_transitive.
    simpl.
    apply bpar_shuffle.
    econstructor.
    apply stbpstop.
    econstructor. *)
*)
    Unshelve.
    exact mtc.
    eauto.
    eauto.
    exact mtc.
    eauto.
    eauto.
    (*
    exact (aasp (0,0) (ASPC 1 [])).
    exact mtc.
    eauto.
    eauto.
     *)
    
Defined.

Lemma run_lstar_corrolary : forall t tr et e e' p p' o o' (*t' n*),
    (*t = snd (anno t' n) -> *)
    (*well_formed t ->  *)
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
  
  apply run_lstar with (t:=t) (tr:=tr) (e:=e) (p:=p) (o:=o) (e':=st_ev) (p':=st_pl) (o':=st_store) (*(t':=t') (n:=n)*); eauto.
  
  destruct o0.
  dunit.
  rewrite hi.
  
  unfold run_vm in *.
  monad_unfold.
  rewrite hi in *.
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
  eapply run_lstar. eauto.
Defined.


    
  

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

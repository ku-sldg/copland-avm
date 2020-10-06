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
  | abpar (x,_) (sp1,sp2) t1 t2 =>
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
    put_ev (ppc e1r e2r) 
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

(*
Ltac do_flip :=
  match goal with
  | [H: (pop_stackm _ = _) |- _ ] =>
    (*idtac "doing pop_stackm flip"; *)
    symmetry in H
  end.
*)

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

(* Starting trace has no effect on store *)
Lemma trace_irrel_store : forall t1 tr1 tr1' tr2 e e' p1' p1 o' o,
    run_vm t1
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
           {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |} ->
    
    st_store (
        run_vm t1
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |}) = o'.
Proof.
  induction t1; intros.
  - simpl in *.
    destruct a.
    + unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      inv H.
      reflexivity.
    + unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      inv H.
      reflexivity.
    +
      
      unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      inv H.
      reflexivity.
    +
      unfold run_vm in *.
      monad_unfold.
      repeat break_let.
      monad_unfold.
      inv H.
      reflexivity.
  - simpl in *.
    unfold run_vm in *.
    repeat (monad_unfold; repeat break_let; monad_unfold).
    boom; repeat break_match; allss.
  - 




    unfold run_vm in *.
    repeat monad_unfold.
    break_match.
    break_match.
    repeat break_let.
    simpl in *.
    break_match.
    vmsts.
    subst.
    invc H.
    assert (st_store2 = st_store0).
    {
      erewrite <- IHt1_1.
      rewrite Heqp0.
      simpl. reflexivity.
      rewrite Heqp. simpl. reflexivity.
    }
    subst.
    simpl.
       
    erewrite <- IHt1_2.
    rewrite Heqp2.
    simpl.
    reflexivity.
    rewrite Heqp2.
    simpl.
    clear Heqp0.
    clear Heqp.
    assert (o' = st_store).
    {
      erewrite <- IHt1_2.
      rewrite Heqp1. simpl. reflexivity.
      rewrite Heqp1. simpl.

      
      admit.
    }
    subst.
    reflexivity.
    admit.
    simpl.
    vmsts.
    subst.
    simpl.
    break_match.
    break_match.
    break_let.
    vmsts.
    admit.
    vmsts.
    invc H.
    erewrite <- IHt1_1.
    rewrite Heqp. simpl. reflexivity.
    rewrite Heqp0.
    simpl.
    reflexivity.
  -
    admit.
  -
    admit.


  (*
  - simpl.
    inv H. reflexivity.   
  - simpl; destruct a;
      boom;
      repeat break_match;
      allss.
   *)
Admitted.

(* Starting trace has no effect on evidence *)
Lemma trace_irrel_ev : forall il1 tr1 tr1' tr2 e e' p1' p1 o1 o1',
    run_vm il1 {| st_ev := e; st_trace := tr1; st_pl := p1; st_store := o1 |} =
    {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o1' |} ->
    
    st_ev (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o1 |}) = e'.
Proof.
  (*
  induction il1; intros.
  - simpl.
    inv H. reflexivity.   
  - simpl; destruct a;
      boom;
      repeat break_match;
      allss.
   *)
  Admitted.

(* Starting trace has no effect on place *)
Lemma trace_irrel_place : forall il1 tr1 tr1' tr2 e e' p p' o o',
    run_vm il1 {| st_ev := e; st_trace := tr1; st_pl := p; st_store := o |} =
    {| st_ev := e'; st_trace := tr1'; st_pl := p'; st_store := o' |} ->
    
    st_pl (
        run_vm il1 {| st_ev := e; st_trace := tr2; st_pl := p; st_store := o |}) = p'.
Proof.
  (*
  induction il1; intros.
  - simpl.
    inv H. reflexivity.   
  - simpl; destruct a;
      boom;
      repeat break_match;
      allss.
   *)
Admitted.

(* A distributive property of st_trace.  Says we can pull the front of a starting trace (m) outside and prepend it to a st_trace call with the rest of the original starting trace (k) as the starting trace *)
Lemma gen_foo : forall t m k e p o,
    st_trace (run_vm t {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |})
(*
      (fold_left (run_vm_step) il
                        {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |})*) =
    m ++ st_trace (run_vm t
                        {| st_ev := e; st_trace := k; st_pl := p; st_store := o |}).
Proof.
  (*
  induction il; simpl; intros m k e s p o.
  - auto.
  - destruct a as [n p0 | n sp1 sp2 | n | l m' n | | | i q t (*| i rpyi q*)];
          boom;
          repeat break_match;
          allss;
          repeat rewrite IHil;
          repeat rewrite app_assoc;
          congruence.
   *)
Admitted.

(* Instance of gen_foo where k=[] *)
Lemma foo : forall t m e p o,
    st_trace (run_vm t
                     {| st_ev := e; st_trace := m; st_pl := p; st_store := o |}) =
    m ++ st_trace (run_vm t
                          {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}).
Proof.
  intros.
  assert (m = m ++ []) as H by (rewrite app_nil_r; auto).
  rewrite H at 1.
  apply gen_foo.
Defined.

(*
Lemma compile_not_empty :
  forall t,
    (instr_compiler t) <> [].
Proof.
  intros.
  induction t;
    try destruct a;
    try destruct r;
    try destruct s;
    simpl; try congruence.
  - simpl.
    destruct (instr_compiler t1); simpl; congruence.
Defined.
*)

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


(*
Lemma put_ev_after_immut_stack{A:Type} : forall s (h:VM A) e,
    st_stack (execSt s h) = st_stack (execSt s (h ;; (put_ev e))).
Proof.
  intros.
  boom; repeat break_match; allss.
Defined.
*)

(*
Lemma update_ev_immut_stack'{A:Type} : forall s (h:VM A) e,
    st_stack (execSt s h) = st_stack (execSt s ((put_ev e);; h)).
Proof.
Abort.
*)  (* NOT true for arbitrary h:  h could match on e to update its stack *)


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

Lemma st_trace_destruct' :
  forall t1 t2 e m p o,
    st_trace
      (run_vm t2
              (run_vm t1
                      {| st_ev := e;
                         st_trace := m;
                         st_pl := p;
                         st_store := o|})) =
    m ++ 
    st_trace
      (run_vm t1
              {| st_ev := e;
                 st_trace := [];
                 st_pl := p;
                 st_store := o |}) ++
      st_trace
      (run_vm t2
              {| st_ev :=
                   (st_ev
                      (run_vm t1
                              {| st_ev := e; st_trace := [];
                                 st_pl := p; st_store := o |}));
                    st_trace := [];
                    st_pl := p;
                    st_store :=
                      (st_store
                         (run_vm t1
                                 {| st_ev := e; st_trace := [];
                                    st_pl := p; st_store := o |}));|}).
Proof.





  (*
  induction il1; try reflexivity; intros.
  - simpl.
    rewrite foo.
    reflexivity.
  - simpl.
    Check foo.
    destruct a as [n p0 | n sp1 sp2 | n | l m' n | | i q t (*| i rpyi q*) | l m' ls1 ls2];
      try (  (* apriminstr, asplit, reqrpy cases *)
          try destruct r;
          unfold run_vm_step; fold run_vm_step;
          monad_unfold;
          rewrite foo;
          repeat rewrite <- app_assoc;
          rewrite IHil1;
          repeat rewrite <- app_assoc;
          st_equiv;
          congruence);
      try (boom; allss);
      try (
          boom; repeat break_match; allss;
          rewrite foo;
          rewrite IHil1;
          repeat rewrite <- app_assoc;
          st_equiv;
          rewrite H;
          eauto; congruence).

    unfold get_store_at.
    monad_unfold.
    rewrite PeanoNat.Nat.eqb_refl.
    simpl.
    rewrite foo.
    repeat rewrite <- app_assoc.
    rewrite IHil1.
    repeat rewrite <- app_assoc.
    Print st_equiv.

    
    assert ( forall l,  m ++
                (req i p t (unanno a) :: remote_events a t ++ [rpy (Nat.pred q) p t]) ++ l =
        m ++
  [req i p t (unanno a)] ++
  remote_events a t ++
  [rpy (Nat.pred q) p t] ++ l) as HH.
    { intros.
      erewrite haha.
      eauto.
    }
    rewrite <- HH.

    st_equiv.
    rewrite H.
    eauto.
   *)
Admitted.

Lemma pl_immut : forall t e tr p o,
    st_pl
      (run_vm t
              {|
                st_ev := e;
                st_trace := tr;
                st_pl := p;
                st_store := o |}) = p.
Proof.
  (*
  induction il; intros.
  - simpl. reflexivity.
  -
    destruct a as [n p0 | n sp1 sp2 | n | l m n | | | i q t (*| i rpyi q*)];
      try (boom; repeat break_match; allss).
   *)
Admitted.

Lemma trace_under_st_ev : forall t e trd trd' p o,
    StVM.st_ev
      (run_vm t
              {|
                st_ev := e;
                st_trace := trd;
                st_pl := p;
                st_store := o |}) =
    StVM.st_ev
      (run_vm t
              {|
                st_ev := e;
                st_trace := trd';
                st_pl := p;
                st_store := o |}).
Proof.
  intros.
  erewrite trace_irrel_ev; eauto.
  eapply st_congr; eauto.
Defined.
    
Lemma trace_under_st_store : forall t e trd trd' p o,
    StVM.st_store
      (run_vm t
              {|
                st_ev := e;
                st_trace := trd;
                st_pl := p;
                st_store := o |}) =
    StVM.st_store
      (run_vm t
              {|
                st_ev := e;
                st_trace := trd';
                st_pl := p;
                st_store := o |}).
Proof.
  intros.
  erewrite trace_irrel_store; eauto.
  eapply st_congr; eauto.
Defined.

(*

Lemma destruct_compiled_appended : forall trd trd' il1 il2 e e'' s s'' p p'' o o'',
    run_vm
      (il1 ++ il2)
        {| st_ev := e;   st_stack := s;   st_trace := trd; st_pl := p; st_store := o |} =
        {| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p''; st_store := o''  |} ->
    (exists tr1 e' s' p' o',
        run_vm
          (il1)
          {| st_ev := e;  st_stack := s;  st_trace := trd; st_pl := p; st_store := o  |} =
          {| st_ev := e'; st_stack := s'; st_trace := tr1; st_pl := p'; st_store := o'  |} /\
        exists tr2,
          run_vm
            (il2)
            {| st_ev := e';  st_stack := s';  st_trace := tr1; st_pl := p'; st_store := o' |} =
            {| st_ev := e''; st_stack := s''; st_trace := tr1 ++ tr2; st_pl := p''; st_store := o''  |} /\
          trd' = tr1 ++ tr2).
Proof.
  intros.
  remember (run_vm (il1) {| st_ev := e; st_stack := s; st_trace := trd; st_pl := p |}) as A.
  
  exists (st_trace A).
  exists (st_ev A).
  exists (st_stack A).
  exists (st_pl A).
  exists (st_store A).
  Check st_congr.

  split; try apply record_congr.
  -
    remember (run_vm (il2)
                     {| st_ev := st_ev A;
                        st_stack := st_stack A;
                        st_trace := st_trace A;
                        st_pl := st_pl A;
                        st_store := st_store A|}) as B.
    
  exists (st_trace (run_vm (il2)
                      {| st_ev := st_ev A;
                         st_stack := st_stack A;
                         st_pl := p;
                         st_trace := [];
                         st_store := st_store A |})).
  rewrite HeqB.
  rewrite HeqA.
  unfold run_vm in *.
  Check record_congr.
  
  rewrite <- record_congr.

  rewrite <- fold_left_app.
  rewrite foo.
  destruct A; unfold run_vm.
  Check trace_irrel_ev.
  simpl in HeqB.
  destruct B.
  Check trace_under_st_ev.


  erewrite trace_under_st_ev. (*with (trd':=[]).*)
  erewrite trace_under_st_stack.
  erewrite trace_under_st_store.
  
  split.
  +
    rewrite <- app_assoc.
    Check st_trace_destruct'.
    erewrite <- st_trace_destruct'.
    rewrite fold_left_app in *.
    rewrite H.
    reflexivity.
  +

    erewrite trace_under_st_ev. (*with (trd':=[]).*)
    erewrite trace_under_st_stack.
    erewrite trace_under_st_store.

    (*rewrite <- HH.*)
    symmetry.
    rewrite fold_left_app in *.
    repeat 
    rewrite <- foo.
    assert (
        StVM.st_trace (fold_left run_vm_step il2
        (fold_left run_vm_step il1
           {| st_ev := e; st_stack := s; st_trace := trd; st_pl := p; st_store := o |})) =
        StVM.st_trace ({| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p''; st_store := o'' |})) as H1 by congruence.
    simpl in *. rewrite <- H1.


    
    assert (StVM.st_pl (fold_left run_vm_step il1
                        {|
                        st_ev := e;
                        st_stack := s;
                        st_trace := trd;
                        st_pl := p;
                        st_store := o |}) = p) as H2 by (apply pl_immut).
    rewrite <- H2 at 4.
    rewrite <- record_congr. auto.
Defined.
*)

Lemma restl' : forall t e e' x tr p p' o o',
    run_vm t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |} ->

    run_vm t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
    {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}.
Proof.
  intros.
  assert (
      st_trace (run_vm t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |}) =
      st_trace ({| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_store := o' |})).
  congruence.
  eapply st_congr;
    try eapply trace_irrel_ev;
    try eapply trace_irrel_place;
    try eapply trace_irrel_store;
    eauto.
  + (* st_trace case *)
    rewrite foo in *.
    simpl in *.
    Check app_inv_head.
    eapply app_inv_head.
    eauto.
Defined.

(*
Lemma destruct_compiled_appended_fresh : forall trd' il1 il2 e e'' s s'' p p'' o o'',
    run_vm
      (il1 ++ il2)
        {| st_ev := e;   st_stack := s;   st_trace := []; st_pl := p; st_store := o |} =
        {| st_ev := e''; st_stack := s''; st_trace := trd'; st_pl := p''; st_store := o''  |} ->
    (exists tr1 e' s' p' o',
        run_vm
          (il1)
          {| st_ev := e;  st_stack := s;  st_trace := []; st_pl := p; st_store := o  |} =
          {| st_ev := e'; st_stack := s'; st_trace := tr1; st_pl := p'; st_store := o'  |} /\
        exists tr2,
          run_vm
            (il2)
            {| st_ev := e';  st_stack := s';  st_trace := []; st_pl := p'; st_store := o' |} =
            {| st_ev := e''; st_stack := s''; st_trace := tr2; st_pl := p''; st_store := o''  |} /\
          trd' = tr1 ++ tr2).
Proof.
  intros trd' il1 il2 e e'' s s'' p p'' o o' H0.
  edestruct (destruct_compiled_appended); eauto.
  destruct_conjs.
  assert (p = H2) as H8. {
    assert (st_pl (run_vm il1 {| st_ev := e; st_stack := s; st_trace := []; st_pl := p; st_store := o |}) =
            st_pl {| st_ev := H; st_stack := H1; st_trace := x; st_pl := H2; st_store := H3 |}). {
    congruence. }
    rewrite pl_immut in H8.
    simpl in *. auto. }
  exists x. exists H. exists H1. exists p. exists H3.
  split.
  - 
    congruence.
  - exists H5.
    split.
    + rewrite H8.
      eapply restl'; eauto.
    + assumption.
Defined.
 *)


(*

Ltac do_dca :=
  match goal with
  | [ H: run_vm (_ ++ _) _ = _ |- _] =>
    idtac "ran do_dca";
    apply destruct_compiled_appended in H;
    destruct_conjs
  end.

Ltac do_dca_fresh :=
  match goal with
  | [ H: run_vm (_ ++ _) _ = _ |- _] =>
    idtac "ran do_dca";
    apply destruct_compiled_appended_fresh in H;
    destruct_conjs
  end.

Ltac do_stack0 :=                    
  match goal with
  | [H:  run_vm (instr_compiler _)
                {| st_ev := _; st_stack := ?s0; st_trace := _ |} =
         {| st_ev := _; st_stack := ?s1; st_trace := _ |} |- _ ] =>
    assert (s0 = s1) by (eauto)
  end.

(* When running an entire compiled term, stack is restored to where it started *)
Lemma multi_stack_restore : forall t tr1 tr1' e e' s s' p p' o o',
    run_vm (instr_compiler t)
           {| st_ev := e;  st_stack := s;  st_trace := tr1;  st_pl := p;  st_store := o |} =
           {| st_ev := e'; st_stack := s'; st_trace := tr1'; st_pl := p'; st_store := o' |}  ->
    s = s'.
Proof.
  induction t; intros; simpl in *.
  - (* asp_instr case *)
    destruct a;
      inv H; try reflexivity.
  - (* aatt case *)
    destruct r.
    invc H.
    unfold run_vm_step in *.
    unfold execSt in *.
    simpl in *.
    monad_unfold.
    repeat break_let.
    allss.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    rewrite PeanoNat.Nat.eqb_refl in *.
    allss.
  - (* alseq case *)
    do_dca.
    eapply IHt2.
    assert (s = H1).
    eapply IHt1; eauto.
    subst.
    eapply restl'; eauto.
  - (* abseq case *)
    destruct s.
    destruct r.
    simpl in *.

    (* do_run. *)
    
    do_dca.
      
    simpl in *.
    do_stack0.
    unfoldm.

    subst.
    (*
    rewrite H1 in Heqppp. *)
    monad_unfold.

    unfold push_stack in *.
    do_dca.

    do_run. 
    desp.
    
    pairs.
    do_stack0.
    subst.
    do_pop_stackm_facts.
 
    congruence.
    do_stack0.
    subst.
    monad_unfold.
    unfold pop_stackm in *. monad_unfold. congruence.

  - (* abpar case *)
    destruct s.
    destruct r. 
 
    boom; repeat (break_match; allss).
Defined.

Ltac do_stack1 t1 :=
  match goal with
  | [H:  run_vm (instr_compiler t1)
                {| st_ev := _; st_stack := ?s0; st_trace := _ |} =
         {| st_ev := _; st_stack := ?s1; st_trace := _ |} |- _ ] =>
    assert (s0 = s1) by (eapply multi_stack_restore; eauto)
  end; destruct_conjs.

Ltac do_stack t1 t2 :=
  match goal with
  | [H:  run_vm (instr_compiler t1)
                {| st_ev := _; st_stack := ?s0; st_trace := _ |} =
         {| st_ev := _; st_stack := ?s1; st_trace := _ |},
         G:  run_vm (instr_compiler t2)
                    {| st_ev := _; st_stack := ?s; st_trace := _ |} =
             {| st_ev := _; st_stack := ?s'; st_trace := _ |} |- _ ] =>
    assert (s0 = s1 /\ s = s') by (split;eapply multi_stack_restore; eauto)
  end; destruct_conjs.
*)

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

Lemma suffix_prop : forall t e e' tr tr' p p' o o',
    run_vm t
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p;
             st_store := o |} =
    {|
      st_ev := e';
      st_trace := tr';
      st_pl := p';
      st_store := o' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace (run_vm t
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p;
             st_store := o |}) =
    st_trace ({|
      st_ev := e';
      st_trace := tr';
      st_pl := p';
      st_store := o' |})) as H0.
  congruence.

  simpl in H0.
  eexists.
  rewrite <- H0.
  rewrite foo.
  reflexivity.
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
  intros.
  simpl.
  Search PeanoNat.Nat.eqb.
  remember (PeanoNat.Nat.eqb k k') as oo.
  
  destruct oo.
  Search PeanoNat.Nat.eqb.
  assert (k = k').
  apply EqNat.beq_nat_eq. auto.
  congruence.
  rewrite PeanoNat.Nat.eqb_refl. reflexivity.
Defined.

(*
Lemma wf_bpar : forall t r s x y,
    (*well_formed (abpar r s x y) -> *)
    (annotated t = (abpar r s x y)) ->
  range x <> range y.
Proof.
  intros.
  assert (well_formed (annotated t)).
  unfold annotated. apply anno_well_formed.
  intros.
  generalize dependent x.
  generalize dependent y.
  generalize dependent r.
  generalize dependent s.
  generalize dependent H0.
  induction t; intros.
  - inv H.
  - unfold annotated in *. unfold anno in *. fold anno in *.
    simpl in *. expand_let_pairs. simpl in *. inv H.
  - unfold annotated in *. unfold anno in *. fold anno in *.
    simpl in *. expand_let_pairs. simpl in *. inv H.
    expand_let_pairs. simpl in *. solve_by_inversion.
  - unfold annotated in *. unfold anno in *. fold anno in *.
    simpl in *. expand_let_pairs. simpl in *. inv H.
    expand_let_pairs. solve_by_inversion.
  - unfold annotated in *. unfold anno in *. fold anno in *.
    repeat expand_let_pairs. simpl in *.
    invc H0.
    invc H.
    destruct (anno t1 1).
    simpl in *.
    destruct (anno t2 n).
    simpl in *.
    destruct (range a).
    destruct (range a0).
    simpl in *.
    subst.
    find_inversion.
Abort.
*)

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

Lemma alseq_decomp : forall r t1 t2 e e'' p p'' o o'' tr tr''', 
    build_comp (alseq r t1 t2) {| st_ev := e; st_trace := tr'''; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''; st_store := o'' |}) ->

    exists e' tr' p' o',
      build_comp t1 {| st_ev := e; st_trace := tr'''; st_pl := p; st_store := o |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |}) /\
      exists tr'',
        build_comp t2 {| st_ev := e'; st_trace := []; st_pl := p'; st_store := o' |} =
        (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) /\
        tr = tr' ++ tr''.
      
Proof.
Admitted.

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
    repeat break_let.
    rewrite PeanoNat.Nat.eqb_refl in *.
    repeat find_inversion.
    auto.
  - simpl in *.
    monad_unfold.
    repeat break_match;
      try (repeat find_inversion).

    + 
      try dunit; repeat find_inversion; vmsts; repeat dunit.
    
      destruct t'; inv H;
        try (
          repeat break_let;
          simpl in *;
          inv H1).
      repeat break_let.
      edestruct IHt1.
      symmetry.
      rewrite Heqp6.
      simpl in *.
      inv H.
      reflexivity.

      apply Heqp2. apply Heqp0.
      destruct_conjs; subst.
      edestruct IHt2.
      rewrite Heqp7.
      simpl in *.
      inv H.
      reflexivity.
      apply Heqp3. apply Heqp1.
      destruct_conjs; subst.
      eauto.
  -
    simpl in *.
    monad_unfold.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    repeat break_match;
      try (repeat find_inversion).
    vmsts.
    simpl in *.
    repeat dunit.
    
     destruct t'; inv H;
        try (
          repeat break_let;
          simpl in *;
          inv H1).
     repeat break_let.
     edestruct IHt1.
     rewrite Heqp2. simpl in *.
     inv H.
     reflexivity.
     
    

    apply Heqp13. apply Heqp4.
    destruct_conjs; subst.
    edestruct IHt2.
    rewrite Heqp3.
    simpl in *.
    inv H.
    reflexivity.

    apply Heqp8. apply Heqp17.
    destruct_conjs; subst. eauto.
  - simpl in *.
    monad_unfold.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    rewrite PeanoNat.Nat.eqb_refl in *.
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
    repeat find_inversion.
    repeat break_let.
    simpl in *.
    repeat find_inversion.
    rewrite PeanoNat.Nat.eqb_refl in *.
    vmsts.
    simpl in *.
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

Lemma fafaf : forall e e' e'' p p' p'' o o' o'' x y r s t t' n,
    t = snd (anno t' n) ->
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (None, {| st_ev := e'; st_trace := y; st_pl := p'; st_store := o' |}) ->
    build_comp t {| st_ev := e; st_trace := r; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := s; st_pl := p''; st_store := o'' |}) ->
    False.
Proof.
  intros.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent e''.
  generalize dependent p.
  generalize dependent p'.
  generalize dependent p''.
  generalize dependent o.
  generalize dependent o'.
  generalize dependent o''.
  generalize dependent x.
  generalize dependent y.
  generalize dependent r.
  generalize dependent s.
  generalize dependent t'.
  generalize dependent n.
  
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
    rewrite PeanoNat.Nat.eqb_refl in *.
    monad_unfold.
    repeat find_inversion.
  -
    edestruct alseq_decomp; eauto.
    destruct_conjs.

    simpl in *.
    
    repeat monad_unfold.
    (*
    destruct (build_comp t1 {| st_ev := e; st_trace := x; st_pl := p; st_store := o |}) as [HH].
    destruct HH eqn:HHH.
    repeat break_let.
    destruct o0.
    repeat dunit.
    repeat find_inversion.
    vmsts.
    simpl in *.
     *)
    
    
    repeat break_match; try solve_by_inversion.
    + 
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
    edestruct hihi.
    rewrite Heqp4.
    reflexivity.
    
    simpl in *.
    
    repeat dunit.
    apply Heqp2. apply Heqp0.
    repeat find_inversion.
    destruct_conjs; subst.
    eapply IHt2.
    rewrite Heqp5. simpl. reflexivity.
    eassumption. eassumption.
    + repeat find_inversion.
      destruct t'; inv H;
      try (
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    simpl in *.
    repeat break_let.
    inv H.
    eapply IHt1.
    rewrite Heqp3. reflexivity.
    eassumption. eassumption.
  -
    
      
    


    (*
    assert (st_ev2 = st_ev0). admit.
    assert (st_pl = st_pl0). admit.
    assert (st_store2 = st_store0). admit.
    subst.
    repeat find_inversion.
    eapply IHt2.
    eapply Heqp3.
    assert (st_pl2 = p''). admit.
    subst.
    eapply Heqp1.
    vmsts.
    repeat find_inversion.
    assert (e' = st_ev0). admit.
    assert (p' = st_pl0). admit.
    assert (o' = st_store0). admit.
    subst.
    eapply IHt1. apply Heqp2.

    destruct u.

    apply Heqp0.

    vmsts.
    destruct u.

    Search trace_irrel_ev.
    Check trace_irrel_ev.



    eauto.
    

    vmsts.
    invc H.
    solve_by_inversion.
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



    destruct u.
    destruct u1.
    destruct u0.
    Print dohi.
    edestruct hihi.
    dohi.
    dohi.
    dohi.
    destruct_conjs; subst.
    eapply IHt2. apply Heqp17. eassumption.
    (*
    dohi.
    destruct_conjs; subst.
    eauto.
     *)
    

    simpl in *.
    vmsts.
    simpl in *.

    repeat dunit.
    eapply IHt1. eassumption. eassumption.
    (*
    repeat dohi.
    destruct_conjs; subst.
    eauto. *)
    vmsts.
    simpl in *.
    dunit.
    dunit.
    eapply IHt1. eassumption. eassumption.
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
    rewrite PeanoNat.Nat.eqb_refl in *.
    vmsts.
    simpl in *.
    assert (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false) as H0.
    admit.
    subst.
    rewrite H in *.
    repeat find_inversion.

    assert (Maps.map_get
              (Maps.map_set (Maps.map_set o (fst (range t1)) (parallel_att_vm_thread t1 st_ev1)) (fst (range t2))
                            (parallel_att_vm_thread t2 (splitEv s2 st_ev1))) (fst (range t2)) =
            Some (parallel_att_vm_thread t2 (splitEv s2 st_ev1))).
    admit.
    rewrite H0 in *.
    repeat find_inversion.
    unfold get_store_at in *.
    monad_unfold.
    repeat break_let.
    assert (PeanoNat.Nat.eqb (fst (range t1)) (fst (range t2)) = false).
    admit.
    rewrite H in *.
    rewrite PeanoNat.Nat.eqb_refl in *.
    repeat find_inversion.
*)
Admitted.

    
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
  assert (run_vm t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
          {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
  eapply restl'.
  unfold run_vm.
  monad_unfold.
  rewrite H0.
  simpl.
  reflexivity.
  unfold run_vm in *.
  monad_unfold.
  destruct (build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) eqn:asdf.
  simpl in *.
  vmsts.
  invc H0.
  destruct o0.
  destruct u.
  inv H1.
  reflexivity.

  exfalso.
  eapply fafaf; eauto.
Defined.

Lemma run_lstar : forall t tr et e e' p p' o o' t' n,
   (* annotated x = t -> *)
    (*well_formed t -> *)
    t = snd (anno t' n) -> 
    (*t = annotated t' ->  *)
    build_comp t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o'))
    (*run_vm t
           (mk_st e [] p o) =
           (mk_st e' tr p' o')*) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros  t tr et e e' p p' o o' t' n HH H.
  
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
  induction t; intros. (* unfold annotated in *. *)
  - (* aasp case *)
    destruct a;
      unfold run_vm in *;
      repeat (monad_unfold; break_let; monad_unfold);
      invc H;
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

    Lemma build_comp_at : forall (t : AnnoTerm) (e : EvidenceC) (n : nat) (o : ev_store),
        build_comp t {| st_ev := e; st_trace := []; st_pl := n; st_store := o |} =
        (Some tt, {| st_ev := eval (unanno t) e; st_trace := remote_events t n; st_pl := n; st_store := o |}).
    Proof.
    Admitted.

    apply build_comp_at.

    econstructor.
    apply stattstop.
    econstructor.
    
  -
    simpl in *.
    


    edestruct alseq_decomp; eauto.
    destruct_conjs.
    
          
    econstructor.
    econstructor.

    rewrite H6.

    eapply lstar_transitive.

    eapply lstar_stls.
    subst.
    edestruct afaff; eauto.
    destruct_conjs.

    eapply IHt1; eauto.
    eapply lstar_silent_tran.
    apply stlseqstop.

    edestruct afaff2; eauto.
    destruct_conjs.

    eapply IHt2; eauto.
    (* inv wft. eauto. *)
    assert (p = H1). {
      assert (
          st_pl (run_vm t1
                        {| st_ev := e; st_trace := [];
                           st_pl := p; st_store := o |}) =
          st_pl ({| st_ev := x; st_trace := H0;
                    st_pl := H1; st_store := H2 |})).
      unfold run_vm.
      monad_unfold.
      simpl.
      rewrite H3.
      simpl. reflexivity.
      
      rewrite pl_immut in *. simpl in *.
      congruence. }
    subst; eauto.

  -
    destruct s; destruct r; simpl in *.
    unfold run_vm in *. repeat monad_unfold.
    repeat break_let.
    repeat monad_unfold.
    vmsts.
    repeat find_inversion.
    repeat break_match;
      repeat find_inversion;
      simpl in *.

    Check restl'.

    assert (exists l, st_trace3 = [Term.split n0 p] ++ l) as H0.
    eapply suffix_prop.
    unfold run_vm.
    monad_unfold.
    rewrite Heqp4.
    simpl.
    reflexivity.
    destruct H0 as [H0 H1].
    rewrite H1 in *. clear H1.

    Check restl'.

    destruct t'; inv HH;
      try (
          repeat break_let;
          simpl in *;
          solve_by_inversion).
    simpl in *.
    repeat break_let.
    inv HH.


    
    

    assert (build_comp a {| st_ev := splitEv s e; st_trace := []; st_pl := p; st_store := o |} =
            (Some tt, {| st_ev := st_ev3; st_trace := H0; st_pl := st_pl3; st_store := st_store3 |})).
    {
      eapply restl'_2.

      destruct u.
      rewrite Heqp0.
      reflexivity.
      assert ( Term.split n p :: H0 =  [Term.split n p] ++ H0). admit.
      rewrite H in *.
      repeat dunit.
      eassumption.
    }
    (* 
      rewrite Heqp4.
      simpl.
      reflexivity.
      Check restl'.
      eapply restl'.
      unfold run_vm.
      monad_unfold.
      rewrite Heqp4.
      simpl.
      reflexivity.
    }
     *)
    

    assert (exists l, st_trace = ([Term.split n p] ++ H0) ++ l) as H00.
    eapply suffix_prop.
    unfold run_vm.
    monad_unfold.
    rewrite Heqp8.
    simpl.
    reflexivity.
    destruct H00 as [H00 HHH].
    rewrite HHH in *. clear HHH.

    assert (
        build_comp a0 {| st_ev := splitEv s0 e; st_trace := []; st_pl := st_pl3; st_store := st_store3 |} =
        (Some tt, {| st_ev := st_ev; st_trace := H00; st_pl := p'; st_store := o' |})).
    {
      repeat dunit.
      eapply restl'_2.
      rewrite Heqp1.
      reflexivity.
      
      assert ( Term.split n p :: H0 =  [Term.split n p] ++ H0). admit.
       
      
      rewrite H2 in *.
      repeat dunit.
      eassumption.

    }
    (*
      unfold run_vm.
      monad_unfold.
      rewrite Heqp8.
      simpl.
      reflexivity.
    }
     *)
    

    assert (p = st_pl3).
    {
      admit.
    }

    rewrite H3 in *. clear H3.

    assert (st_pl3 = p').
    {
      admit.
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

    Check afaff3.
    (*

    edestruct afaff3; eauto.
     
    
    destruct_conjs.
     *)
    
     
    eapply IHt1; eauto.
    rewrite Heqp0. reflexivity.
  
    unfold run_vm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.

    (*
     do_run.
     do_dca_fresh.
     clear H.
     rewrite H14.
     do_stack1 t2.
     *)
    
     eapply lstar_transitive.
     eapply lstar_stbsr.
     (*

    edestruct afaff4; eauto.
    destruct_conjs.
      *)
     
     
     eapply IHt2; eauto.
     rewrite Heqp1. reflexivity.
     (* inv wft; eauto. *)
     (*rewrite H in *. 
     eauto.

     do_run.
     pairs.
     eapply lstar_tran.
      *)

     Check stbsrstop.
     econstructor.
     eapply stbsrstop.
     econstructor.

  -
    

  - (* abpar case *)
    destruct s; destruct r.
    simpl in *.
    unfold run_vm_step in *. monad_unfold; monad_unfold.
    repeat break_match.
    +
      vmsts.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      do_get_store_at_facts; eauto.
      subst.
      simpl.
      econstructor.
      econstructor.
      eapply lstar_transitive.
      simpl.

      apply bpar_shuffle.
      econstructor.
      apply stbpstop.
      econstructor.
    + vmsts.
      repeat find_inversion.
      do_get_store_at_facts; eauto.
      subst.
      invc H4.
      unfold Maps.map_set in *.
      Check In.

      elimtype False. eapply get_store_in.
      eassumption.
      simpl.
      reflexivity.

      eapply map_get_get.
    + vmsts.
      repeat find_inversion.
      subst.
      unfold Maps.map_set in *.
      elimtype False. eapply get_store_in.
      eassumption.
      simpl.
      reflexivity.
      eapply map_get_get_2.
      eapply afaf; eauto.
Defined.


Lemma run_lstar_corrolary : forall t tr et e s p o t' n,
    t = snd (anno t' n) -> 
    st_trace (run_vm (instr_compiler t)
                     (mk_st e s [] p o)) = tr ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  Check run_lstar.
  eapply run_lstar with (t:=t) (tr:=tr) (e:=e) (s:=s) (p:=p) (o:=o); eauto.
  Check st_congr.
  eapply st_congr; try reflexivity.
  eassumption.
Defined.

Theorem vm_ordered' : forall t tr ev0 ev1 e e' s s' o o' t' n,
    well_formed t ->
    t = snd (anno t' n) -> 
    run_vm
      (instr_compiler t)
      (mk_st e s [] 0 o) =
      (mk_st e' s' tr 0 o') ->
    prec (ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  Check ordered.
  eapply ordered with (p:=0) (e:=mt); eauto.
  eapply run_lstar; eauto.
Defined.

Locate prec.

Theorem vm_ordered : forall t tr ev0 ev1 e e' s s' o o' t',
    t = annotated t' -> 
    run_vm
      (instr_compiler t)
      (mk_st e s [] 0 o) =
      (mk_st e' s' tr 0 o') ->
    prec (ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  Check ordered.
  eapply ordered with (p:=0) (e:=mt); eauto.
  -
    unfold annotated in H.
    subst.
    eapply anno_well_formed; eauto.
  -
    eapply run_lstar; eauto.
Defined.

(*
Implementation of the Attestation Virtual Machine (AVM) + proof that it refines the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists (*Preamble*) Term ConcreteEvidence LTS GenStMonad.
Require Import Main Event_system Term_system.
Require Import Auto.


Require Import MonadVM MonadVMFacts Maps Axioms_Io Impl_vm External_Facts Helpers_VmSemantics.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Set Nested Proofs Allowed.

Lemma always_some : forall t vm_st vm_st' op,
    well_formed t ->
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
  -
    repeat (df; dohtac).
    tauto.
  -
    df. 
    do_wf_pieces.
    
    destruct o eqn:hhh;
      try (df; eauto). 
  -
    df.   
    do_wf_pieces.

    repeat break_match;
      try (
          df; eauto). 
  -
    do_wf_pieces.
    repeat (df; dohtac).
    tauto.
Defined.

Lemma gen_foo : forall t m k e p o v,
    well_formed t ->
    build_comp t
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |} =
    (Some tt, v) -> 
    st_trace
      ( execSt (build_comp t)
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}) =
    m ++
      st_trace
          (execSt (build_comp t)
                  {| st_ev := e; st_trace := k; st_pl := p; st_store := o |}).
Proof.
  
  induction t; intros.
  -
    destruct r.
    destruct a;
      simpl;
      repeat rewrite app_assoc;
      reflexivity.
  -
    repeat (df; dohtac).
    repeat rewrite app_assoc.
    reflexivity.
  -
    df.
    annogo.
    do_wf_pieces.
    dosome.
    assert (o4 = Some tt).
    {
      eapply always_some.
      apply H0.
      eauto.
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
    repeat subst'.
    simpl in *.
    subst.
    assert (
        StVM.st_trace
          (snd (build_comp t2
                {| st_ev := st_ev0; st_trace := m ++ st_trace0; st_pl := st_pl0; st_store := st_store0 |})) =
         m ++
           StVM.st_trace (snd (build_comp t2 {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store0 |}))) as HH.
    eapply IHt2; eauto.
    repeat (subst'; simpl in * ).
    eauto.
  - (* abseq case *)
    Ltac df' :=
      repeat (cbn in *; unfold runSt in *; repeat break_let; repeat (monad_unfold; cbn in *; find_inversion); monad_unfold; repeat dunit).
    annogo.
        
    do_wf_pieces.
    df'.
    df.
    dosome.
    
    assert (o17 = Some tt).
    { eapply always_some; eauto. }
    subst.
    df.
    assert (o13 = Some tt).
    {
      eapply always_some.
      apply H1.
      eauto.
    }
    subst.
    df.
    annogo.
    df.
    dohi'.

    assert (
        StVM.st_trace
           (snd (build_comp t1 {| st_ev := splitEv s0 e; st_trace := m ++ (k ++ [Term.split n p]); st_pl := p; st_store := o |})) =
         m ++
         StVM.st_trace
         (snd (build_comp t1 {| st_ev := splitEv s0 e; st_trace := k ++ [Term.split n p]; st_pl := p; st_store := o |}))).
    {
      rewrite <- app_assoc in Heqp4.
      eapply IHt1; eauto.
    }
    subst'.
    df.
    rewrite app_assoc in *.
    subst'.
    df.  
    subst.

    assert (
         StVM.st_trace (snd (build_comp t2{| st_ev := splitEv s1 e; st_trace := m ++ st_trace0; st_pl := st_pl0; st_store := st_store0 |})) =
         m ++ StVM.st_trace (snd (build_comp t2 {| st_ev := splitEv s1 e; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store0 |}))
      ).
    eapply IHt2; eauto.
    subst'.
    df.
    tauto.  
  -
    do_wf_pieces.
    repeat (df; dohtac).
    repeat (rewrite app_assoc); tauto.
Defined.

(* Instance of gen_foo where k=[] *)
Lemma foo : forall t m e p o v,
    well_formed t ->
    build_comp t
               {| st_ev := e; st_trace := m; st_pl := p; st_store := o |} =
    (Some tt, v) -> 
    
    st_trace
      (execSt (build_comp t)
              {| st_ev := e; st_trace := m; st_pl := p; st_store := o |}) =
    m ++
      st_trace
      (execSt (build_comp t)
                     {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}).
Proof.
  intros.
  assert (m = m ++ []) as HH by (rewrite app_nil_r; auto).
  rewrite HH at 1.
  eapply gen_foo; eauto.
  rewrite app_nil_r.
  eauto.
Defined.

Lemma alseq_decomp : forall r t1' t2' e e'' p p'' o o'' tr,
    well_formed (alseq r t1' t2') ->
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
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl. exists st_store.
  split.
  reflexivity.
  destruct (build_comp t2'
                       {| st_ev := st_ev; st_trace := []; st_pl := st_pl; st_store := st_store |}) eqn:hey.
  vmsts.
  assert (o0 = Some tt).
  {
    eapply always_some; eauto.
  }
  subst.

  (*
  
  destruct o0; try build_contra. *)
  annogo.

  exists st_trace0.
  dohi'.
  
  split.
  reflexivity.

  pose foo.
  specialize foo with (t:= t2') (m:=st_trace) (e:=st_ev) (p:= st_pl) (o:=st_store) (v:={| st_ev := st_ev0; st_trace := tr; st_pl := st_pl0; st_store := st_store0 |}).
  intros.
  repeat concludes.
  df.
  subst'.
  df.
  tauto. 
Defined.

(*
Ltac tacky H H0 ff := (eapply hihi; [apply H | apply H0 | apply ff]).
Print tacky.
*)

Lemma trace_irrel_store' : forall t tr1 tr1' tr2 e e' p1' p1 o' o,
    well_formed t ->
    build_comp t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    
    st_store
      (execSt (build_comp t)
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |}) = o'.
Proof.
  intros.
  destruct (build_comp t {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  assert (o0 = Some tt).
  eapply always_some; eauto.
  subst.
  repeat dohi.
  df.
  tauto.





  (*
  destruct o0; repeat dunit.
  - *)


  
    
(*
    assert (e' = st_ev /\ p1' = st_pl /\ o' = st_store).
    (eapply hihi; [apply H | apply H0 | apply ff]).
    my_tac (eapply hihi; [apply H | apply H0 | apply ff]).
    eapply hihi.
    apply H.
    apply H0.
    apply ff.
 *)

    (*
     assert (e' = st_ev /\ p1' = st_pl /\ o' = st_store) by
    (eapply hihi; [apply H | apply H0 | apply ff]). *)
     


    
(*
    assert_new_proof_by' (e' = st_ev /\ p1' = st_pl /\ o' = st_store) (eapply hihi; [apply H | apply H0 | apply ff]).

    
    Ltac tacky H H0 ff := (eapply hihi; [apply H | apply H0 | apply ff]).
    Print tacky.
    assert_new_proof_by (e' = st_ev /\ p1' = st_pl /\ o' = st_store) (tacky H H0 ff).
    (eapply hihi; [apply H | apply H0 | apply ff]).
*)
    
(*
    repeat dohi.
    df.
    tauto.
  -
    exfalso.
    eapply fafaf; eauto. *)
Defined.

Lemma trace_irrel_pl' : forall t tr1 tr1' tr2 e e' p1' p1 o' o,
    well_formed t ->
    build_comp t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    
    st_pl
      (execSt (build_comp t)
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |}) = p1'.
Proof.
  intros.
  destruct (build_comp t {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  assert (o0 = Some tt).
  eapply always_some; eauto.
  subst.
  repeat dohi.
  df.
  tauto.
Defined.

Lemma trace_irrel_ev' : forall t tr1 tr1' tr2 e e' p1' p1 o' o,
    well_formed t ->
    build_comp t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    
    st_ev
      (execSt (build_comp t)
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |}) = e'.
Proof.
  intros.
  destruct (build_comp t {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  assert (o0 = Some tt).
  eapply always_some; eauto.
  subst.
  repeat dohi.
  df.
  tauto.
Defined.

Lemma restl' : forall t e e' x tr p p' o o',
    well_formed t ->
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
    simpl.
    reflexivity.
  }
  
  unfold run_vm in *.
  assert (
   st_ev
     (execSt
        (build_comp t)
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = e').
  eapply trace_irrel_ev'; eauto.

  assert (
   st_pl
     (execSt
        (build_comp t)
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = p').
  eapply trace_irrel_pl'; eauto.

  assert (
   st_store
     (execSt
        (build_comp t)
               {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) = o').
  eapply trace_irrel_store'; eauto.

  assert (
      (execSt
         (build_comp t)
         {| st_ev := e; st_trace := []; st_pl := p; st_store := o |}) =
      {| st_ev := e'; st_trace := tr; st_pl := p'; st_store := o' |}).
  {
    eapply st_congr; eauto.
    erewrite foo in H1.
    eapply app_inv_head.
    eauto.
    eauto.
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
  df.
  tauto.
Defined.

Lemma suffix_prop : forall t e e' tr tr' p p' o o',
    well_formed t ->
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
  assert (st_trace
            (execSt (build_comp t)
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p;
             st_store := o |}) =
    st_trace ({|
      st_ev := e';
      st_trace := tr';
      st_pl := p';
      st_store := o' |})) as H00.
  unfold execSt.
  subst'.
  simpl.
  reflexivity.
  simpl in H00.
  eexists.
  rewrite <- H00.
  erewrite foo; eauto.
Defined.

Lemma multi_ev_eval : forall t tr tr' e e' p p' o o' es e's,
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
          eauto).
  -
    do_wf_pieces.
    repeat (df; dohtac).    
    annogo.
    eapply IHt.
    eassumption.
    eapply build_comp_at; eauto.
    eassumption.
    reflexivity.
  -
    do_wf_pieces.
    edestruct suffix_prop.
    apply H.
    eassumption.
    subst.

    edestruct alseq_decomp.
    eassumption.
    eapply restl'.
    eassumption.
    eassumption.
    destruct_conjs.
    df.
    
    eapply IHt2.
    + eassumption.
    + eassumption.
    + eapply IHt1.
      ++ eassumption.
      ++ eassumption.
      ++ eassumption.      
      ++ reflexivity.
    + do_pl_immut.
      dosome.
      do_pl_immut.
      assert (H5 = p).
      erewrite <- pl_immut.
      unfold execSt.
      rewrite H7.
      simpl. reflexivity.
      eassumption.
      subst.
      congruence.     
  -
    do_wf_pieces.
    df.
    repeat break_match;
      try solve_by_inversion.
    +
      df.
      annogo.
      simpl in *.
      assert (exists l, st_trace0 = (tr ++ [Term.split n p]) ++ l) as H00.
      { 
        eapply suffix_prop.
        apply H3.
        simpl.
        eassumption.
      }
      destruct_conjs.
      subst.
      assert (exists l, st_trace = ((tr ++ [Term.split n p]) ++ H00) ++ l) as H00'.
      {
        eapply suffix_prop.
        simpl.
        eassumption.
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
        eapply restl' with (x:= (tr ++ [Term.split n p])).
        eassumption.
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
        eapply restl' with (x:= ((tr ++ [Term.split n p]) ++ H00)).
        eassumption.
        eassumption.
      }
      
      econstructor.
      destruct s0.
      ++
        eapply IHt1.
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
        eassumption.
        eassumption.
        econstructor.
        reflexivity.
      ++
        destruct s1.
        +++
          simpl.
          eapply IHt2.
          eassumption.
          eassumption.
          destruct e;
            try (evShapeFacts;
                 econstructor; eauto).
          assert (st_pl0 = p).
          {
            erewrite <- pl_immut.
            unfold execSt.
            rewrite H0.
            simpl. reflexivity.
            eassumption.
          }
          subst.
          congruence.
        +++
          simpl.
          eapply IHt2.
          eassumption.
          eassumption.
          econstructor.
           assert (st_pl0 = p).
          {
            erewrite <- pl_immut.
            unfold execSt.
            rewrite H0.
            simpl. reflexivity.
            eassumption.
          }
          subst.
          congruence.        
    +
      repeat find_inversion. 
  -
    do_wf_pieces.
    df.
    unfold runParThreads, runParThread in *.
    repeat (df; dohtac).
    
    econstructor.
    destruct s0.
    +
      simpl.
      eapply IHt1.
      apply H3.     
      eapply build_comp_par.
      eassumption.
      eassumption.
      tauto.
    +
      simpl.
      eapply IHt1.
      eassumption.
      eapply build_comp_par.
      eassumption.
      econstructor.
      tauto.
    +
      destruct s1.
      ++
        simpl.
        eapply IHt2.
        eassumption.
        eapply build_comp_par.
        eassumption.
        eassumption.
        tauto.
      ++
        simpl.
        eapply IHt2.
        eassumption.
        eapply build_comp_par.
        eassumption.
        econstructor.
        eauto.
        Unshelve.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
Defined.
   
Lemma run_lstar : forall t tr et e e' p p' o o',
    well_formed t ->
    build_comp t (mk_st e [] p o) = (Some tt, (mk_st e' tr p' o')) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros t tr et e e' p p' o o' H.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    destruct a;
      df;
      econstructor; try (econstructor; reflexivity).
  - (* aatt case *)
    do_wf_pieces.
    destruct r.
    repeat (df; dohtac).
    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.
    eapply IHt; eauto.
    apply build_comp_at.
    eassumption.
    econstructor.
    apply stattstop.
    econstructor.
  -  
    do_wf_pieces.  
    edestruct alseq_decomp; eauto.
    destruct_conjs.         
    econstructor.
    econstructor.
    subst.
    eapply lstar_transitive.
    eapply lstar_stls.
    df.
    eapply IHt1.
    eassumption.
    eassumption.
    eapply lstar_silent_tran.
    apply stlseqstop.
    df.
    assert (H4 = p).
    {
      erewrite <- pl_immut.
      unfold execSt.
      rewrite Heqp0.
      tauto.
      eassumption.
    }
    subst.   
    eapply IHt2; eauto.    
  -    
    do_wf_pieces.
    destruct r; destruct s.
    df.
    vmsts.
    dosome.
    df.
    assert (exists l, st_trace1 = [Term.split n p] ++ l) as H00.
    eapply suffix_prop.
    apply H1.
    eassumption.
    destruct H00 as [H00 H11].
    subst'.
    
    assert (build_comp t1
                       {| st_ev := splitEv s e; st_trace := []; st_pl := p; st_store := o |} =
            (Some tt, {| st_ev := st_ev1; st_trace := H00; st_pl := st_pl1; st_store := st_store1 |})).
    {
      eapply restl'.    
      repeat dunit.
      eassumption.
      eassumption.
    }
    
    assert (exists l, st_trace = ([Term.split n p] ++ H00) ++ l) as H000.
    eapply suffix_prop.
    eassumption.
    eassumption.
    destruct H000 as [H000 HHH].
    subst'.

    assert (
        build_comp t2
                   {| st_ev := splitEv s0 e; st_trace := []; st_pl := st_pl1; st_store := st_store1 |} =
        (Some tt, {| st_ev := st_ev; st_trace := H000; st_pl := p'; st_store := o' |})).
    {
      repeat dunit.
      eapply restl'.
      repeat dunit.
      eassumption.
      eassumption.
    }

    assert (st_pl1 = p).
    {
      erewrite <- pl_immut.
      unfold execSt.
      rewrite H0.
      tauto.
      eassumption.
    }
    subst.

    assert (p' = p).
    {
      erewrite <- pl_immut.
      unfold execSt.
      rewrite H3.
      tauto.
      eassumption.
    }
    subst.

    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    eapply lstar_transitive.
    simpl.

    eapply lstar_stbsl.  
     
    eapply IHt1.
    eassumption.
    eassumption.
  
    unfold run_vm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.
    eassumption.

    econstructor.
    eapply stbsrstop.
    econstructor.
  -
    destruct s; destruct r.
    repeat (df; dohtac).
    econstructor.
    econstructor.
    eapply lstar_transitive.
    simpl.
    apply bpar_shuffle.
    econstructor.
    apply stbpstop.
    econstructor.     
    Unshelve.
    exact mtc.
    eauto. 
Defined.

Lemma run_lstar_corrolary : forall t tr et e e' p p' o o',
    well_formed t -> 
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
  apply run_lstar with (t:=t) (tr:=tr) (e:=e) (p:=p) (o:=o) (e':=st_ev) (p':=st_pl) (o':=st_store); eauto.
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

Theorem vm_ordered' : forall t tr ev0 ev1 e e' o o',
    well_formed t -> 
    build_comp 
      t
      (mk_st e [] 0 o) =
      (Some tt, (mk_st e' tr 0 o')) ->
    prec (ev_sys t 0) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  eapply ordered with (p:=0) (e:=mt); eauto.
  eapply run_lstar; eauto.
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
  assert (well_formed t).
  unfold annotated in H.
    subst.
    eapply anno_well_formed; eauto.
    eapply ordered with (p:=0) (e:=mt); eauto.
    eapply run_lstar; eauto.
Defined.

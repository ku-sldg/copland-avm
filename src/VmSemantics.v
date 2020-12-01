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

Lemma trace_irrel : forall t tr1 tr1' tr2 tr2' e e' e'' p p' p'' o o' o'',
    well_formed t ->
    build_comp t
           {| st_ev := e;  st_trace := tr1; st_pl := p;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p'; st_store := o' |}) ->

    build_comp t
           {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |} =
    (Some tt, {| st_ev := e''; st_trace := tr2'; st_pl := p''; st_store := o'' |}) ->
    
    e' = e'' /\ p' = p'' /\ o' = o''.
Proof.
  intros.

  assert (st_ev
      (execSt (build_comp t)
              {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |}) = e').
  eapply trace_irrel_ev'; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_pl
            (execSt (build_comp t)
                    {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |}) = p').
  eapply trace_irrel_pl'; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_store
            (execSt (build_comp t)
                    {| st_ev := e;  st_trace := tr2; st_pl := p;  st_store := o  |}) = o').
  eapply trace_irrel_store'; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.
  repeat split; congruence.
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
    do_asome.
    subst.
    df.
    dohi.
    assert (
        StVM.st_trace
          (snd (build_comp t1 {| st_ev := e; st_trace := m ++ k; st_pl := p; st_store := o |}))
        =
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
          StVM.st_trace
          (snd (build_comp t2
           {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0; st_store := st_store0 |}))) as HH.
    eapply IHt2; eauto.
    repeat (subst'; simpl in * ).
    eauto.
  - (* abseq case *)
    annogo.
        
    do_wf_pieces.
    df.
    dosome.

    do_asome.
    subst.
    df.
    annogo.
    df.
    dohi.

    assert (
        StVM.st_trace
           (snd (build_comp t1 {| st_ev := splitEv s0 e; st_trace := m ++ (k ++ [Term.split n p]); st_pl := p; st_store := o |})) =
         m ++
         StVM.st_trace
         (snd (build_comp t1 {| st_ev := splitEv s0 e; st_trace := k ++ [Term.split n p]; st_pl := p; st_store := o |}))).
    {
      rewrite <- app_assoc in *. (*Heqp4. *)
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
        assert (PeanoNat.Nat.eqb n3 n1 = false).
    {
      eapply hhh; eauto.
    }
    subst''.
    df.



    assert (PeanoNat.Nat.eqb n1 (n4 - 1) = false).
    {
      eapply hhhh; eauto.
    }
    subst''.
    repeat (df; dohtac).



    assert (PeanoNat.Nat.eqb (n4 - 1) (n2 - 1) = false).
    {
      eapply hhhhh; eauto.
    }
    subst''.
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
  df.
  congruence.
  simpl in H00.
  eexists.
  rewrite <- H00.
  erewrite foo.
  eauto.
  eauto.
  eauto.
Defined.

Ltac do_suffix name :=
  match goal with
  | [H': build_comp ?t
         {| st_ev := _;st_trace := ?tr; st_pl := _; st_store := _ |} =
         (Some tt,
          {| st_ev := _; st_trace := ?tr'; st_pl := _; st_store := _ |}),
         H2: well_formed ?t |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H2 | apply H'])
             name
  end.

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
  destruct
    (build_comp t2'
                {| st_ev := st_ev; st_trace := []; st_pl := st_pl; st_store := st_store |}) eqn:hey.
  vmsts.
  do_asome.
  subst.
  annogo.

  exists st_trace0.
  dohi.
  
  split.
  reflexivity.

  pose foo.
  specialize foo with (t:= t2') (m:=st_trace) (e:=st_ev) (p:= st_pl)
                      (o:=st_store)
                      (v:={| st_ev := st_ev0; st_trace := tr; st_pl := st_pl0; st_store := st_store0 |}).
  intros.
  repeat concludes.
  df.
  subst'.
  df.
  tauto. 
Defined.

Lemma restl : forall t e e' x tr p p' o o',
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
  do_asome.
  df.
  tauto.
Defined.

Ltac do_restl :=
  match goal with
  | [H: build_comp ?t
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_store := ?o |} =
        (Some tt,
         {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p'; st_store := ?o' |}),
        H2: well_formed ?t |- _] =>
    assert_new_proof_by
      (build_comp t {| st_ev := e; st_trace := []; st_pl := p; st_store := o |} =
       (Some tt,
        {| st_ev := e'; st_trace := x; st_pl := p'; st_store := o' |}))
      ltac:(eapply restl; [apply H2 | apply H])
  end.

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
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.
    destruct_conjs.
    df.
    dosome.
    
    eapply IHt2.
    + eassumption.
    + eassumption.
    + eapply IHt1.
      ++ eassumption.
      ++ eassumption.
      ++ eassumption.      
      ++ reflexivity.
    +
      repeat do_pl_immut.
      subst.
      congruence.     
  -
    do_wf_pieces.
    df.
    repeat break_match;
      try solve_by_inversion;
      try (df; tauto).
    +
      df.
      annogo.
      simpl in *.
      do_suffix blah.
      do_suffix blah'.
      destruct_conjs; subst.
      repeat do_restl.
      
      econstructor.
      destruct s0.
      ++
        eapply IHt1; eauto.
      ++
        simpl in *.
        eapply IHt1; eauto.
      ++
        destruct s1.
        +++
          simpl.
          repeat do_pl_immut.
          subst.
          eapply IHt2; eauto.
        +++
          simpl.
          repeat do_pl_immut.
          subst.
          eapply IHt2; eauto.      
  -
    do_wf_pieces.
    df.
    repeat (df; dohtac).
        assert (PeanoNat.Nat.eqb n3 n1 = false).
    {
      eapply hhh; eauto.
    }
    subst''.
    df.



    assert (PeanoNat.Nat.eqb n1 (n4 - 1) = false).
    {
      eapply hhhh; eauto.
    }
    subst''.
    repeat (df; dohtac).



    assert (PeanoNat.Nat.eqb (n4 - 1) (n2 - 1) = false).
    {
      eapply hhhhh; eauto.
    }
    subst''.
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
    repeat do_pl_immut.
    subst.   
    eapply IHt2; eauto.    
  -    
    do_wf_pieces.
    destruct r; destruct s.
    df.
    vmsts.
    dosome.
    df.

    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat do_pl_immut.
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
        assert (PeanoNat.Nat.eqb n3 n1 = false).
    {
      eapply hhh; eauto.
    }
    subst''.
    df.



    assert (PeanoNat.Nat.eqb n1 (n4 - 1) = false).
    {
      eapply hhhh; eauto.
    }
    subst''.
    repeat (df; dohtac).



    assert (PeanoNat.Nat.eqb (n4 - 1) (n2 - 1) = false).
    {
      eapply hhhhh; eauto.
    }
    subst''.
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

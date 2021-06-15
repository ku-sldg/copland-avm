(*
Proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Defs Term_Defs Term ConcreteEvidence LTS Event_system Term_system Main.
Require Import GenStMonad MonadVM Maps StructTactics Auto.
Require Import Axioms_Io Impl_vm External_Facts Helpers_VmSemantics.

Require Import List.
Import ListNotations.
Require Import Coq.Program.Tactics Coq.Program.Equality.
Require Import Coq.Arith.Peano_dec Lia.

Set Nested Proofs Allowed.

Lemma st_trace_irrel : forall t tr1 tr1' tr2 tr2' e e' e'' et et' et'' p p' p'',
    well_formed_r t ->
    copland_compile t
           {| st_ev := e; st_evT := et; st_trace := tr1; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_evT := et'; st_trace := tr1'; st_pl := p' |}) ->

    copland_compile t
           {| st_ev := e; st_evT := et; st_trace := tr2; st_pl := p |} =
    (Some tt, {| st_ev := e''; st_evT := et''; st_trace := tr2'; st_pl := p'' |}) ->
    
    e' = e'' /\ et' = et'' /\ p' = p''.
Proof.
  intros.

  assert (st_ev
      (execSt (copland_compile t)
              {| st_ev := e; st_evT := et; st_trace := tr2; st_pl := p |}) = e').
  eapply trace_irrel_ev; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_pl
            (execSt (copland_compile t)
                    {| st_ev := e; st_evT := et; st_trace := tr2; st_pl := p |}) = p').
  eapply trace_irrel_pl; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

   assert (st_evT
            (execSt (copland_compile t)
                    {| st_ev := e; st_evT := et; st_trace := tr2; st_pl := p |}) = et').
  eapply trace_irrel_evT; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.


  
  unfold execSt in *.
  subst''.
  simpl in *.
  repeat split; try congruence.
Defined.

Lemma st_trace_cumul' : forall t m k e et p v,
    well_formed_r t ->
    copland_compile t
               {| st_ev := e; st_evT := et; st_trace := m ++ k; st_pl := p |} =
    (Some tt, v) -> 
    st_trace
      ( execSt (copland_compile t)
               {| st_ev := e; st_evT := et; st_trace := m ++ k; st_pl := p |}) =
    m ++
      st_trace
          (execSt (copland_compile t)
                  {| st_ev := e; st_evT := et; st_trace := k; st_pl := p |}).
Proof.
  induction t; intros.
  -
    destruct r.
    destruct a;
      simpl;
      repeat rewrite app_assoc;
      reflexivity.
  -
    repeat (df; try dohtac; df).
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
          (snd (copland_compile t1 {| st_ev := e; st_evT := et; st_trace := m ++ k; st_pl := p |}))
        =
        m ++
          StVM.st_trace
          (snd (copland_compile t1 {| st_ev := e; st_evT := et; st_trace := k; st_pl := p |}))).
    eapply IHt1; eauto.
    repeat subst'.
    simpl in *.
    subst.
    assert (
        StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_evT := st_evT0; st_trace := m ++ st_trace0; st_pl := st_pl0 |})) =
        m ++
          StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_evT := st_evT0; st_trace := st_trace0; st_pl := st_pl0 |}))) as HH.
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
          (snd (copland_compile t1 {| st_ev := fst (splitEv_l s e et);
                                      st_evT := e1;
                                      st_trace := m ++ (k ++ [Term_Defs.split n p]);
                                      st_pl := p |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t1 {| st_ev := fst (splitEv_l s e et);
                                     st_evT := e1;
                                     st_trace := k ++ [Term_Defs.split n p];
                                     st_pl := p |}))).
    {
      rewrite <- app_assoc in *.
      subst'.
      simpl.
      eapply IHt1; eauto.
    }
    subst'.
    df.
    rewrite app_assoc in *.
    subst'.
    df.  
    subst.

    assert (
        StVM.st_trace (snd (copland_compile t2{| st_ev := fst (splitEv_r s e et);
                                                 st_evT := e3;
                                                 st_trace := m ++ st_trace0;
                                                 st_pl := st_pl0 |})) =
        m ++ StVM.st_trace (snd (copland_compile t2 {| st_ev := fst (splitEv_r s e et);
                                                       st_evT := e3;
                                                       st_trace := st_trace0;
                                                       st_pl := st_pl0 |}))
      ).
    subst'.
    simpl.

    
    eapply IHt2; eauto.
    subst'.
    df.
    subst.
    tauto.

  -
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
          (snd (copland_compile t1 {| st_ev := fst (splitEv_l s e et);
                                      st_evT := e1;
                                      st_trace := m ++ (k ++ [Term_Defs.split n p]);
                                      st_pl := p |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t1 {| st_ev := fst (splitEv_l s e et);
                                     st_evT := e1;
                                     st_trace := k ++ [Term_Defs.split n p];
                                     st_pl := p |}))).
    {
      subst'.
      simpl.
      rewrite <- app_assoc in *.
      eapply IHt1; eauto.
    }
    subst'.
    df.
    rewrite app_assoc in *.
    subst'.
    df.  
    subst.

    assert (
        StVM.st_trace (snd (copland_compile t2{| st_ev := fst (splitEv_r s e et);
                                                 st_evT := e3;
                                                 st_trace := m ++ st_trace0;
                                                 st_pl := st_pl0 |})) =
        m ++ StVM.st_trace (snd (copland_compile t2 {| st_ev := fst (splitEv_r s e et);
                                                       st_evT := e3;
                                                       st_trace := st_trace0;
                                                       st_pl := st_pl0 |}))
      ).
    subst'.
    simpl.
    eapply IHt2; eauto.
    subst'.
    df.
    subst.
    tauto.
Defined.

(* Instance of st_trace_cumul' where k=[] *)
Lemma st_trace_cumul : forall t m e et p v,
    well_formed_r t ->
    copland_compile t
               {| st_ev := e; st_evT := et; st_trace := m; st_pl := p |} =
    (Some tt, v) -> 
    
    st_trace
      (execSt (copland_compile t)
              {| st_ev := e; st_evT := et; st_trace := m; st_pl := p |}) =
    m ++
      st_trace
      (execSt (copland_compile t)
                     {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |}).
Proof.
  intros.
  assert (m = m ++ []) as HH by (rewrite app_nil_r; auto).
  rewrite HH at 1.
  eapply st_trace_cumul'; eauto.
  rewrite app_nil_r.
  eauto.
Defined.

Lemma suffix_prop : forall t e e' et et' tr tr' p p',
    well_formed_r t ->
    copland_compile t
           {|
             st_ev := e;
             st_evT := et;
             st_trace := tr;
             st_pl := p |} =
    (Some tt, {|
       st_ev := e';
       st_evT := et';
      st_trace := tr';
      st_pl := p' |}) ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace
            (execSt (copland_compile t)
           {|
             st_ev := e;
             st_evT := et;
             st_trace := tr;
             st_pl := p |}) =
    st_trace ({|
                 st_ev := e';
                 st_evT := et';
      st_trace := tr';
      st_pl := p' |})) as H00.
  df.
  congruence.
  simpl in H00.
  eexists.
  rewrite <- H00.
  erewrite st_trace_cumul.
  eauto.
  eauto.
  eauto.
Defined.

Ltac do_suffix name :=
  match goal with
  | [H': copland_compile ?t
         {| st_ev := _; st_evT := _; st_trace := ?tr; st_pl := _ |} =
         (Some tt,
          {| st_ev := _; st_evT := _; st_trace := ?tr'; st_pl := _ |}),
         H2: well_formed_r ?t |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H2 | apply H'])
             name
  end.

Lemma alseq_decomp_gen : forall r t1' t2' e e'' et et'' p p'' init_tr tr,
    well_formed_r (alseq r t1' t2') ->
    copland_compile (alseq r t1' t2') {| st_ev := e; st_evT := et; st_trace := init_tr; st_pl := p |} =
    (Some tt, {| st_ev := e''; st_evT := et''; st_trace := tr; st_pl := p'' |}) ->

    exists e' et' tr' p',
      copland_compile t1' {| st_ev := e; st_evT := et; st_trace := init_tr; st_pl := p |} =
      (Some  tt, {| st_ev := e'; st_evT := et'; st_trace := tr'; st_pl := p' |}) /\
        copland_compile t2' {| st_ev := e'; st_evT := et'; st_trace := tr'; st_pl := p' |} =
        (Some tt, {| st_ev := e''; st_evT := et''; st_trace := tr; st_pl := p'' |}).     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_evT. exists st_trace. exists st_pl.
  split.
  reflexivity.
  
  vmsts.
  do_asome.
  subst.
  annogo.
  
  do_suffix hi.
  do_suffix hey.
  eassumption.
Defined.

Lemma alseq_decomp : forall r t1' t2' e e'' et et'' p p'' tr,
    well_formed_r (alseq r t1' t2') ->
    copland_compile (alseq r t1' t2') {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |} =
    (Some tt, {| st_ev := e''; st_evT := et''; st_trace := tr; st_pl := p'' |}) ->

    exists e' et' tr' p',
      copland_compile t1' {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |} =
      (Some  tt, {| st_ev := e'; st_evT := et'; st_trace := tr'; st_pl := p' |}) /\
      exists tr'',
        copland_compile t2' {| st_ev := e'; st_evT := et'; st_trace := []; st_pl := p' |} =
        (Some tt, {| st_ev := e''; st_evT := et''; st_trace := tr''; st_pl := p'' |}) /\
        tr = tr' ++ tr''.     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_evT. exists st_trace. exists st_pl.
  split.
  reflexivity.
  destruct
    (copland_compile t2'
                {| st_ev := st_ev; st_evT := st_evT; st_trace := []; st_pl := st_pl |}) eqn:hey.
  vmsts.
  do_asome.
  subst.
  annogo.

  exists st_trace0.
  dohi.
  
  split.
  reflexivity.

  pose st_trace_cumul.
  specialize st_trace_cumul with (t:= t2') (m:=st_trace) (e:=st_ev) (et:=st_evT) (p:= st_pl)
                      (v:={| st_ev := st_ev0; st_evT := st_evT0; st_trace := tr; st_pl := st_pl0 |}).
  intros.
  repeat concludes.
  df.
  subst'.
  df.
  tauto. 
Defined.

Lemma restl : forall t e e' et et' x tr p p',
    well_formed_r t ->
    copland_compile t {| st_ev := e; st_evT := et; st_trace := x; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_evT := et'; st_trace := x ++ tr; st_pl := p' |}) ->

    copland_compile t {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_evT := et'; st_trace := tr; st_pl := p' |}).
Proof.
  intros.
  
  assert (
      st_trace (run_cvm t {| st_ev := e; st_evT := et; st_trace := x; st_pl := p |}) =
      st_trace ({| st_ev := e'; st_evT := et'; st_trace := x ++ tr; st_pl := p' |})).
  {
    unfold run_cvm. 
    monad_unfold.
    subst'.
    simpl.
    reflexivity.
  }
  
  unfold run_cvm in *.
  assert (
   st_ev
     (execSt
        (copland_compile t)
               {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |}) = e').
  eapply trace_irrel_ev; eauto.

  assert (
   st_pl
     (execSt
        (copland_compile t)
               {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |}) = p').
  eapply trace_irrel_pl; eauto.

    assert (
   st_evT
     (execSt
        (copland_compile t)
               {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |}) = et').
  eapply trace_irrel_evT; eauto.
  
  assert (
      (execSt
         (copland_compile t)
         {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |}) =
      {| st_ev := e'; st_evT := et'; st_trace := tr; st_pl := p' |}).
  {
    eapply st_congr; eauto.
    erewrite st_trace_cumul in H1.
    eapply app_inv_head.
    eauto.
    eauto.
    eauto.
  }
  
  destruct (copland_compile t {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |}) eqn:aa.
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
  | [H: copland_compile ?t
        {| st_ev := ?e; st_evT := ?et; st_trace := ?tr; st_pl := ?p |} =
        (Some tt,
         {| st_ev := ?e'; st_evT := ?et'; st_trace := ?tr ++ ?x; st_pl := ?p' |}),
        H2: well_formed_r ?t |- _] =>
    assert_new_proof_by
      (copland_compile t {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |} =
       (Some tt,
        {| st_ev := e'; st_evT := et'; st_trace := x; st_pl := p' |}))
      ltac:(eapply restl; [apply H2 | apply H])
  end.

Lemma splitEv_T_l_LEFT: forall e es et e0 e1,
    Ev_Shape e es ->
    splitEv_l LEFT e et = (e0, e1) ->
    Ev_Shape e0 (splitEv_T_l LEFT es).
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    ff.
Defined.

Axiom remote_Ev_Shape: forall e es t n,
    Ev_Shape e es ->
    Ev_Shape (toRemote t n e) (eval (unanno t) n es).

Lemma cvm_refines_lts_evidence : forall t tr tr' e e' et et' p p' es e's,
    well_formed_r t ->
    copland_compile t (mk_st e et tr p) = (Some tt, (mk_st e' et' tr' p')) ->
    Ev_Shape e es ->
    Term_Defs.eval (unanno t) p es = e's ->
    Ev_Shape e' e's.
Proof.
  induction t; intros.
  -
    destruct a;
      try (
          df;
          eauto).

    (*
    +
      assert (Ev_Shape e (et_fun e)).
      {
        eapply ev_evshape.
      }

      assert (es = (et_fun e)).
      {
        eapply evshape_determ.
        eauto.
        eauto.
      }
      subst.
      eauto. *)
      
      
      
  -
    repeat df. 
    annogo.

    apply remote_Ev_Shape; eauto.

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
      destruct s.
      ++
        eapply IHt1; eauto.

        eapply splitEv_T_l_LEFT; eauto.
        
      ++
        simpl in *.
        eapply IHt1; eauto.
        ff.
      ++
        ff.
        eauto.
      ++
        simpl in *.
        repeat do_pl_immut.
        subst.
        destruct s.
        +++
          ff.
          eauto.
        +++
          ff.
          eauto.
        +++
          ff.
          eauto.

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
      destruct s.
      ++
        eapply IHt1; eauto.

        eapply splitEv_T_l_LEFT; eauto.
        
      ++
        simpl in *.
        eapply IHt1; eauto.
        ff.
      ++
        ff.
        eauto.
      ++
        simpl in *.
        repeat do_pl_immut.
        subst.
        destruct s.
        +++
          ff.
          eauto.
        +++
          ff.
          eauto.
        +++
          ff.
          eauto.
Defined.

Axiom remote_LTS: forall t n et, 
    lstar (conf t n et) (remote_events t n) (stop n (aeval t n et)).

Lemma eval_aeval: forall t1 p et,
    eval (unanno t1) p et = aeval t1 p et.
Proof.
  induction t1; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    erewrite IHt1_1.
    eauto.
  -
    ff.
    erewrite IHt1_1.
    erewrite IHt1_2.
    eauto.
  -
    ff.
    erewrite IHt1_1.
    erewrite IHt1_2.
    eauto. 
Defined.

Lemma evshape_split_l: forall e et s,
    Ev_Shape e et ->
    Ev_Shape (fst (splitEv_l s e et)) (splitEv_T_l s et).
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    try (destruct s; ff; tauto).
Defined.

Lemma evshape_split_r: forall e et s,
    Ev_Shape e et ->
    Ev_Shape (fst (splitEv_r s e et)) (splitEv_T_r s et).
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    try (destruct s; ff; tauto).
Defined.

Lemma cvm_evT_aeval: forall t e e' et et' tr tr' p p',
    copland_compile t {| st_ev := e; st_evT := et; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_evT := et'; st_trace := tr'; st_pl := p' |}) ->
    et' = aeval t p et.
Proof.
Admitted.
   
Lemma cvm_refines_lts_event_ordering : forall t tr e e' et et' p p',
    well_formed_r t ->
    Ev_Shape e et ->
    copland_compile t (mk_st e et [] p) = (Some tt, (mk_st e' et' tr p')) ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros t tr e e' et et' p p' H H'.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    destruct a;
      df;
      econstructor; try (econstructor; reflexivity).
    (*
    +
      assert (et = et_fun e).
      {
        eapply evshape_determ; eauto.
        apply ev_evshape; eauto.
      }
      rewrite <- H0.
      econstructor; try (econstructor; reflexivity). *)
      
      
  - (* aatt case *)
    destruct r.
    repeat (df; try dohtac; df).
    
    assert (lstar (conf t n et) (remote_events t n) (stop n (aeval t n et))).
    {
      apply remote_LTS.
    }

    (*

    pose ev_evshape.
    pose (e0 e).
    
    assert (et_fun e = et).
    {
      pose ev_evshape.
      pose (e0 e).
      eapply evshape_determ.
      eassumption.
      eassumption.
    }
    rewrite H1.
     *)
    

    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.
    
    apply H0.

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
    eassumption.
    eapply lstar_silent_tran.
    apply stlseqstop.
    df.
    repeat do_pl_immut.
    subst.   
    eapply IHt2 with (e:= x).
    eassumption.
    eapply cvm_refines_lts_evidence.
    apply H1.
    eassumption.
    eassumption.

    eapply eval_aeval; eauto.
    assert (H3 = aeval t1 p et).
    {
      eapply cvm_evT_aeval; eauto.
    }
    subst.
    eassumption.
    
  -    
    do_wf_pieces.
    destruct r; destruct s.
    +
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
    2: {
      eassumption.
    }
    eassumption.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.
    2: {
      eassumption.
    }
    
    econstructor.
    econstructor.
    eapply stbsrstop.
    econstructor.
    +
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
    2: {
      eassumption.
    }

    econstructor.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.
    2: {
      eassumption.
    }   
    eassumption.

    econstructor.
    eapply stbsrstop.
    econstructor.

    +
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
    2: {
      eassumption.
    }

    eassumption.

    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_silent_tran.
    apply stbslstop.
    
    eapply lstar_transitive.
    eapply lstar_stbsr.
        
    eapply IHt2.
    eassumption.

    2: {
      eassumption.
    }

    eassumption.

    econstructor.
    eapply stbsrstop.
    econstructor.

  -    
    do_wf_pieces.
    destruct r; destruct s.
    +
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

    eapply lstar_stbparl.
     
    eapply IHt1.
    eassumption.

    2: {
      eassumption.
    }
    eassumption.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_transitive.

    eapply lstar_stbparr.
        
    eapply IHt2.
    eassumption.

    2: {
      eassumption.
    }

    econstructor.

    econstructor.

    eapply stbpstop.

    econstructor.

    +
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

    eapply lstar_stbparl.
     
    eapply IHt1.
    eassumption.
    2: {
      eassumption.
    }
    
    econstructor.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_transitive.

    eapply lstar_stbparr.
        
    eapply IHt2.
    eassumption.

    2: {
      eassumption.
    }

    eassumption.

    econstructor.

    eapply stbpstop.

    econstructor.

    +
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

    eapply lstar_stbparl.
     
    eapply IHt1.
    eassumption.
    2: {
      eassumption.
    }
    eassumption.
  
    unfold run_cvm in *.
    monad_unfold.

    eapply lstar_transitive.

    eapply lstar_stbparr.
        
    eapply IHt2.
    eassumption.
    2: {
      eassumption.
    }
    eassumption.

    econstructor.

    eapply stbpstop.

    econstructor.
Defined.

Lemma cvm_refines_lts_event_ordering_corrolary : forall t tr et e e' et' p p',
    well_formed_r t ->
    Ev_Shape e et ->
    copland_compile t (mk_st e et [] p) = (Some tt, (mk_st e' et' tr p')) ->
    st_trace (run_cvm t
                     (mk_st e et [] p)) = tr ->
    lstar (conf t p et) tr (stop p (aeval t p et)).
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_evT := et; st_trace := []; st_pl := p |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  apply cvm_refines_lts_event_ordering with (t:=t) (tr:=tr) (e:=e) (et':= st_evT) (p:=p) (e':=st_ev) (p':=st_pl); eauto.
  
  try dunit.
  rewrite hi.
  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.
  subst.
  solve_by_inversion.
Defined.

Theorem cvm_respects_event_system' : forall t tr ev0 ev1 e e' et et',
    well_formed_r t ->
    Ev_Shape e et ->
    copland_compile 
      t
      (mk_st e et [] 0) =
      (Some tt, (mk_st e' et' tr 0)) ->
    prec (ev_sys t 0 et) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  eapply ordered with (p:=0) (e:=et); eauto.
  eapply cvm_refines_lts_event_ordering; eauto.
Defined.

Theorem cvm_respects_event_system : forall t tr ev0 ev1 e e' t' (*i n*) et et',
    (*NoDup ls ->
    length ls = nss t' -> *)
    (*t = annotated t' ls -> *)
    (*
    anno t' i = (n, t) -> *)
    t = annotated t' ->
    Ev_Shape e et ->
    copland_compile
      t
      (mk_st e et [] 0) =
    (Some tt, (mk_st e' et' tr 0)) ->
    prec (ev_sys t 0 et) ev0 ev1 ->
    earlier tr ev0 ev1.
Proof.
  intros.
  assert (well_formed_r t).
  {
    unfold annotated in H.
    unfold snd in *.
    break_let.
    subst.
    eapply anno_well_formed_r.
    eassumption.
  }
  eapply ordered with (p:=0) (e:=et); eauto.
  eapply cvm_refines_lts_event_ordering; eauto.
Defined.

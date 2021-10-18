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

(*
Set Nested Proofs Allowed.
*)

Lemma st_trace_irrel : forall t tr1 tr1' tr2 tr2' e e' e'' p p' p'',
    well_formed_r t ->
    copland_compile t
           {| st_ev := e; st_trace := tr1; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p' |}) ->

    copland_compile t
           {| st_ev := e; st_trace := tr2; st_pl := p |} =
    (Some tt, {| st_ev := e''; st_trace := tr2'; st_pl := p'' |}) ->
    
    e' = e'' /\ p' = p''.
Proof.
  intros.

  assert (st_ev
      (execSt (copland_compile t)
              {| st_ev := e; st_trace := tr2; st_pl := p |}) = e').
  eapply trace_irrel_ev; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_pl
            (execSt (copland_compile t)
                    {| st_ev := e; st_trace := tr2; st_pl := p |}) = p').
  eapply trace_irrel_pl; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.
  
  subst''.
  simpl in *.
  repeat split; try congruence.
Defined.

Lemma st_trace_cumul' : forall t m k e p v,
    well_formed_r t ->
    copland_compile t
               {| st_ev := e; st_trace := m ++ k; st_pl := p |} =
    (Some tt, v) -> 
    st_trace
      ( execSt (copland_compile t)
               {| st_ev := e; st_trace := m ++ k; st_pl := p |}) =
    m ++
      st_trace
          (execSt (copland_compile t)
                  {| st_ev := e; st_trace := k; st_pl := p |}).
Proof.
  induction t; intros.
  -
    destruct r.
    destruct a;
      simpl;
      df;
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
          (snd (copland_compile t1 {| st_ev := e; st_trace := m ++ k; st_pl := p |}))
        =
        m ++
          StVM.st_trace
          (snd (copland_compile t1 {| st_ev := e; st_trace := k; st_pl := p |}))).
    eapply IHt1; eauto.
    repeat subst'.
    simpl in *.
    subst.
    assert (
        StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := m ++ st_trace0; st_pl := st_pl0 |})) =
        m ++
          StVM.st_trace
          (snd (copland_compile t2
           {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0 |}))) as HH.
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
          (snd (copland_compile t1 {| st_ev := (splitEv_l s e);
                                      st_trace := m ++ (k ++ [Term_Defs.split n p]);
                                      st_pl := p |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t1 {| st_ev := (splitEv_l s e);
                                     st_trace := k ++ [Term_Defs.split n p];
                                     st_pl := p |}))).
    {
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
        StVM.st_trace (snd (copland_compile t2{| st_ev := (splitEv_r s e);
                                                 st_trace := m ++ st_trace0;
                                                 st_pl := st_pl0 |})) =
        m ++ StVM.st_trace (snd (copland_compile t2 {| st_ev := (splitEv_r s e);
                                                       st_trace := st_trace0;
                                                       st_pl := st_pl0 |}))
      ).
    eapply IHt2; eauto.

    subst'.
    df.
    subst.
    tauto.

  - (* abpar case *)
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
          (snd (copland_compile t {| st_ev := (splitEv_l s e);
                                      st_trace := m ++ (k ++ [Term_Defs.split n p] ++ [cvm_thread_start n l p a (get_et (splitEv_r s e))]);
                                      st_pl := p |})) =
         m ++
         StVM.st_trace
         (snd (copland_compile t {| st_ev := (splitEv_l s e);
                                     st_trace := k ++ [Term_Defs.split n p] ++ [cvm_thread_start n l p a (get_et (splitEv_r s e))];
                                     st_pl := p |}))).
    {
      repeat rewrite <- app_assoc in *.
      eapply IHt; eauto.
    }
    subst'.

    rewrite app_assoc in *.
    subst'.
    df.
    assert (
        ((k ++ [Term_Defs.split n p]) ++
                                      [cvm_thread_start n l p a (get_et (splitEv_r s e))]) =
        ( k ++ [Term_Defs.split n p; cvm_thread_start n l p a (get_et (splitEv_r s e))])
      ).
    {
      rewrite <- app_assoc.
      tauto.
    }
    rewrite H0 in *; clear H0.
    rewrite Heqp1 in *; clear Heqp1.
    df.
    repeat rewrite <- app_assoc in *.
    df.
    subst'.
    df.
    subst.
    rewrite <- app_assoc.
    tauto.
Defined.


(* Instance of st_trace_cumul' where k=[] *)
Lemma st_trace_cumul : forall t m e p v,
    well_formed_r t ->
    copland_compile t
               {| st_ev := e; st_trace := m; st_pl := p |} =
    (Some tt, v) -> 
    
    st_trace
      (execSt (copland_compile t)
              {| st_ev := e; st_trace := m; st_pl := p |}) =
    m ++
      st_trace
      (execSt (copland_compile t)
                     {| st_ev := e; st_trace := []; st_pl := p |}).
Proof.
  intros.
  assert (m = m ++ []) as HH by (rewrite app_nil_r; auto).
  rewrite HH at 1.
  eapply st_trace_cumul'; eauto.
  rewrite app_nil_r.
  eauto.
Defined.

Lemma suffix_prop : forall t e e' tr tr' p p',
    well_formed_r t ->
    copland_compile t
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p |} =
    (Some tt, {|
       st_ev := e';
      st_trace := tr';
      st_pl := p' |}) ->
    exists l, tr' = tr ++ l.
Proof.
  intros.
  assert (st_trace
            (execSt (copland_compile t)
           {|
             st_ev := e;
             st_trace := tr;
             st_pl := p |}) =
    st_trace ({|
                 st_ev := e';
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
         {| st_ev := _; st_trace := ?tr; st_pl := _ |} =
         (Some tt,
          {| st_ev := _; st_trace := ?tr'; st_pl := _ |}),
         H2: well_formed_r ?t |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H2 | apply H'])
             name
  end.

Lemma alseq_decomp_gen : forall r t1' t2' e e'' p p'' init_tr tr,
    well_formed_r (alseq_par r t1' t2') ->
    copland_compile (alseq_par r t1' t2') {| st_ev := e; st_trace := init_tr; st_pl := p |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p'' |}) ->

    exists e' tr' p',
      copland_compile t1' {| st_ev := e; st_trace := init_tr; st_pl := p |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p' |}) /\
        copland_compile t2' {| st_ev := e'; st_trace := tr'; st_pl := p' |} =
        (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p'' |}).     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl.
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

Lemma alseq_decomp : forall r t1' t2' e e'' p p'' tr,
    well_formed_r (alseq_par r t1' t2') ->
    copland_compile (alseq_par r t1' t2') {| st_ev := e; st_trace := []; st_pl := p |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p'' |}) ->

    exists e' tr' p',
      copland_compile t1' {| st_ev := e; st_trace := []; st_pl := p |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p' |}) /\
      exists tr'',
        copland_compile t2' {| st_ev := e'; st_trace := []; st_pl := p' |} =
        (Some tt, {| st_ev := e''; st_trace := tr''; st_pl := p'' |}) /\
        tr = tr' ++ tr''.     
Proof.
  intros.  
  do_wf_pieces.
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl.
  split.
  reflexivity.
  destruct
    (copland_compile t2'
                {| st_ev := st_ev; st_trace := []; st_pl := st_pl |}) eqn:hey.
  vmsts.
  do_asome.
  subst.
  annogo.

  exists st_trace0.
  dohi.
  
  split.
  reflexivity.

  pose st_trace_cumul.
  specialize st_trace_cumul with (t:= t2') (m:=st_trace) (e:=st_ev) (p:= st_pl)
                      (v:={| st_ev := st_ev0; st_trace := tr; st_pl := st_pl0 |}).
  intros.
  repeat concludes.
  df.
  subst'.
  df.
  tauto. 
Defined.

Lemma restl : forall t e e' x tr p p',
    well_formed_r t ->
    copland_compile t {| st_ev := e; st_trace := x; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_trace := x ++ tr; st_pl := p' |}) ->

    copland_compile t {| st_ev := e; st_trace := []; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_trace := tr; st_pl := p' |}).
Proof.
  intros.
  
  assert (
      st_trace (run_cvm t {| st_ev := e; st_trace := x; st_pl := p |}) =
      st_trace ({| st_ev := e'; st_trace := x ++ tr; st_pl := p' |})).
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
               {| st_ev := e; st_trace := []; st_pl := p |}) = e').
  eapply trace_irrel_ev; eauto.

  assert (
   st_pl
     (execSt
        (copland_compile t)
               {| st_ev := e; st_trace := []; st_pl := p |}) = p').
  eapply trace_irrel_pl; eauto.
  
  assert (
      (execSt
         (copland_compile t)
         {| st_ev := e; st_trace := []; st_pl := p |}) =
      {| st_ev := e'; st_trace := tr; st_pl := p' |}).
  {
    eapply st_congr; eauto.
    erewrite st_trace_cumul in H1.
    eapply app_inv_head.
    eauto.
    eauto.
    eauto.
  }
  
  destruct (copland_compile t {| st_ev := e; st_trace := []; st_pl := p |}) eqn:aa.
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
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p |} =
        (Some tt,
         {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p' |}),
        H2: well_formed_r ?t |- _] =>
    assert_new_proof_by
      (copland_compile t {| st_ev := e; st_trace := []; st_pl := p |} =
       (Some tt,
        {| st_ev := e'; st_trace := x; st_pl := p' |}))
      ltac:(eapply restl; [apply H2 | apply H])
  end.

Lemma splitEv_T_l_LEFT: forall e bits bits' es e0 sp,
    et_size e = es ->
    splitEv_l (ALL,sp) (evc bits e) = (evc bits' e0) ->
    et_size e0 = es. (* (splitEv_T_l LEFT es). *)
Proof.
  intros.
  ff.
Defined.

Lemma aeval_anno: forall a i n e0,
    (aeval (snd (anno (unanno a) i)) n e0 = aeval a n e0).
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    ff.
  -
    ff.
    eauto.
    simpl.
    erewrite <- IHa.
    rewrite Heqp.
    simpl.
    tauto.
  -
    ff.
    erewrite <- IHa1.
    erewrite <- IHa2.
    rewrite Heqp0.
    rewrite Heqp.
    simpl.
    tauto.
  -
    ff.
    erewrite <- IHa1.
    erewrite <- IHa2.
    rewrite Heqp0.
    rewrite Heqp.
    simpl.
    tauto.
  -
    ff.
    erewrite <- IHa1.
    erewrite <- IHa2.
    rewrite Heqp0.
    rewrite Heqp.
    simpl.
    tauto.
Defined.

Lemma evc_inv: forall e,
    e = evc (get_bits e) (get_et e).
Proof.
  destruct e; eauto.
Defined.

Lemma front_app{A} :
  forall (x:A) xs ys,
    
    x :: xs ++ ys = [x] ++ xs ++ ys.
Proof.
  intros.
  tauto.
Defined.


Lemma cvm_refines_lts_evidence' : forall t tr tr' e e' p p',
    well_formed_r t ->
    copland_compile t (mk_st e tr p) = (Some tt, (mk_st e' tr' p')) ->
    get_et e' = (Term_Defs.eval (unanno (unannoPar t)) p (get_et e)).

Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
    
  - (* aasp case *)
    destruct a;
      try (
          try unfold get_et;
          df;
          eauto).

  - (* at case *)
    repeat df. 
    annogo.
    do_wf_pieces.
    destruct e.
    ff.
    erewrite eval_aeval.
    simpl.
        
    rewrite aeval_anno.
    eapply remote_Evidence_Type_Axiom.

  - (* alseq case *)
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

    destruct x.
    destruct e'.
    vmsts.

    repeat do_pl_immut; subst.

    assert (e3 = get_et (evc e2 e3)) by tauto.
    repeat jkjke'.
    
  - (* abseq case *)
    do_wf_pieces.
    df.
    repeat break_match;
      try solve_by_inversion;
      try (df; tauto).
    
      df.
      
      annogo.
      simpl in *.
      do_suffix blah.
      do_suffix blah'.
      destruct_conjs; subst.
      repeat do_restl.

      assert (e1 = get_et (evc e0 e1)) by tauto.
      jkjke.
      assert (e3 = get_et (evc e2 e3)) by tauto.
      jkjke.

      assert (get_et (evc e0 e1) = (eval (unanno (unannoPar t1)) p (splitEv_T_l s (get_et e)))).
      {
        destruct s; destruct s.
        ++
          eapply IHt1;
          eassumption.
        ++
          unfold splitEv_T_l.
          assert (mt = get_et (evc [] mt)) by tauto.
          jkjke.
      }
      ff.
      rewrite H6.
      

      assert (get_et (evc e2 e3) = (eval (unanno (unannoPar t2)) p (splitEv_T_r s (get_et e)))).
      {
        repeat do_pl_immut; subst.
        destruct s.
        destruct s0.
        ++
          unfold splitEv_T_r.
          eauto.
        ++
          assert (mt = get_et (evc [] mt)) by tauto.
          jkjke.
          ff.
      }
      ff.

  - (* abpar case *)
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
      (* do_suffix blah'. *)
      destruct_conjs; subst.
      repeat do_restl.

      assert (e1 = get_et (evc e0 e1)) by tauto.
      jkjke.
      assert (e3 = get_et (evc e2 e3)) by tauto.
      jkjke.

      assert (get_et (evc e0 e1) = (eval (unanno (unannoPar t)) p (splitEv_T_l s (get_et e)))).
      {
        destruct s; destruct s.
        ++
          eapply IHt;
          eassumption.
        ++
          unfold splitEv_T_l.
          assert (mt = get_et (evc [] mt)) by tauto.
          jkjke.
      }
      ff.
      rewrite H5.

      do_pl_immut.
      subst.


      assert (e3 = (eval (unanno a) p (splitEv_T_r s (get_et e)))).
      {
        rewrite par_evidence in *.
         destruct s.
         destruct s; destruct s0;
           simpl in *.
         +
           rewrite eval_aeval with (i:=0).
           rewrite aeval_anno.
           erewrite <- remote_Evidence_Type_Axiom. (*with (bits:=[]). *)
           rewrite at_evidence.
           erewrite <- evc_inv.
           rewrite Heqe2.
           ff.
         +
           rewrite eval_aeval with (i:=0).
           rewrite aeval_anno.
           unfold mt_evc in *.
           erewrite <- remote_Evidence_Type_Axiom. (*with (bits:=[]). *)
           rewrite at_evidence.
          (* erewrite <- evc_inv. *)
           rewrite Heqe2.
           ff.
         +
           rewrite eval_aeval with (i:=0).
           rewrite aeval_anno.
           unfold mt_evc in *.
           erewrite <- remote_Evidence_Type_Axiom. (*with (bits:=[]). *)
           rewrite at_evidence.
           erewrite <- evc_inv.
           rewrite Heqe2.
           ff.
         +
           rewrite eval_aeval with (i:=0).
           rewrite aeval_anno.
           unfold mt_evc in *.
           erewrite <- remote_Evidence_Type_Axiom. (*with (bits:=[]). *)
           rewrite at_evidence.
          (* erewrite <- evc_inv. *)
           rewrite Heqe2.
           ff.
      }
      rewrite H5.
      tauto.
      Unshelve.
      eauto.
Defined.

Lemma cvm_refines_lts_evidence : forall t tr tr' bits bits' et et' p p',
    well_formed_r t ->
    copland_compile t (mk_st (evc bits et) tr p) = (Some tt, (mk_st (evc bits' et') tr' p')) ->
    et' = (Term_Defs.eval (unanno (unannoPar t)) p et).
Proof.
  intros.
  assert (et = get_et (evc bits et)) by tauto.
  assert (et' = get_et (evc bits' et')) by tauto.
  rewrite H1; rewrite H2.
  eapply cvm_refines_lts_evidence'; eauto.
Defined.

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

Axiom thread_bookend_peel: forall t p et etr n l a n0 tr,
    lstar (conf (unannoPar t) p et) tr (stop p (aeval (unannoPar t) p et)) ->
    ([cvm_thread_start n l p a etr] ++ tr ++ [cvm_thread_end (Nat.pred n0) l p a] =
     (shuffled_events tr (remote_events a p))
    ).

Lemma cvm_refines_lts_event_ordering : forall t cvm_tr bits bits' et et' p p',
    well_formed_r t ->
    copland_compile t (mk_st (evc bits et) [] p) = (Some tt, (mk_st (evc bits' et') cvm_tr p')) ->
    lstar (conf (unannoPar t) p et) cvm_tr (stop p (aeval (unannoPar t) p et)).
Proof.
  intros t cvm_tr bits bits' et et' p p' H H'.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
     destruct a;
      df;
      econstructor; try (econstructor; reflexivity).
    
  - (* aatt case *)
    destruct r.
    repeat (df; try dohtac; df).
    
    assert (lstar (conf a n et) (remote_events a n) (stop n (aeval a n et))).
    {
      apply remote_LTS.
    }
    
    eapply lstar_tran.
    econstructor.
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    cbn.
    
    apply H0.
    jkjke.
    ff.
    assert (et' = (aeval a n et)).
    {
      erewrite <- remote_Evidence_Type_Axiom.
      jkjke.
    }
    subst.
    
    econstructor.
    apply stattstop.
    econstructor.

  -  (* alseq case *)
    do_wf_pieces.
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    destruct x.
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
    eapply IHt2. (*with (e:= x). *)
    eassumption.
    assert (e0 = Term_Defs.eval (unanno (unannoPar t1)) p et).
    eapply cvm_refines_lts_evidence; eauto.

    subst.
    rewrite <- eval_aeval.
    
    eassumption.


  -    (* abseq case *)
    do_wf_pieces.
    destruct r; destruct s; destruct s; destruct s0.
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

      eassumption.
      
      unfold run_cvm in *.
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

      eassumption.
      
      unfold run_cvm in *.
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

      eassumption.
      
      unfold run_cvm in *.
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

      eassumption.
      
      unfold run_cvm in *.
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


  - (* abpar case *)
    do_wf_pieces.
    destruct r; destruct s; destruct s; destruct s0.
    +
      df.
      vmsts.
      dosome.
      df.

      do_suffix blah.
      
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.

      assert (lstar (conf (unannoPar t) p et) blah (stop p (aeval (unannoPar t) p et))).
      eauto.

      eapply lstar_tran.
      econstructor.
      simpl.

      assert (
          (cvm_thread_start n l p a et
                            :: blah ++ [cvm_thread_end (Nat.pred n0) l p a; join (Nat.pred n0) p]) =
          (([cvm_thread_start n l p a et] ++
                                         blah ++ [cvm_thread_end (Nat.pred n0) l p a]) ++ [join (Nat.pred n0) p])).
      { rewrite front_app.
        repeat rewrite <- app_assoc.
        tauto.
      }
      subst'.
      
      erewrite thread_bookend_peel.

      eapply lstar_transitive.

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      apply stbpstop.
      econstructor.
      eassumption.

    +
      df.
      vmsts.
      dosome.
      df.

      do_suffix blah.

      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.

      assert (lstar (conf (unannoPar t) p et) blah (stop p (aeval (unannoPar t) p et))).
      eauto.

      eapply lstar_tran.
      econstructor.
      simpl.

      assert (
          (cvm_thread_start n l p a mt
                            :: blah ++ [cvm_thread_end (Nat.pred n0) l p a; join (Nat.pred n0) p]) =
          (([cvm_thread_start n l p a mt] ++
                                         blah ++ [cvm_thread_end (Nat.pred n0) l p a]) ++ [join (Nat.pred n0) p])).
      { rewrite front_app.
        repeat rewrite <- app_assoc.
        tauto.
      }
      subst'.
      
      erewrite thread_bookend_peel.

      eapply lstar_transitive.

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      apply stbpstop.
      econstructor.
      eassumption.

    +
      df.
      vmsts.
      dosome.
      df.

      do_suffix blah.
      
      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.

      assert (lstar (conf (unannoPar t) p mt) blah (stop p (aeval (unannoPar t) p mt))).
      eauto.

      eapply lstar_tran.
      econstructor.
      simpl.

      assert (
          (cvm_thread_start n l p a et
                            :: blah ++ [cvm_thread_end (Nat.pred n0) l p a; join (Nat.pred n0) p]) =
          (([cvm_thread_start n l p a et] ++
                                         blah ++ [cvm_thread_end (Nat.pred n0) l p a]) ++ [join (Nat.pred n0) p])).
      { rewrite front_app.
        repeat rewrite <- app_assoc.
        tauto.
      }
      subst'.
      
      erewrite thread_bookend_peel.

      eapply lstar_transitive.

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      apply stbpstop.
      econstructor.
      eassumption.

    +
      df.
      vmsts.
      dosome.
      df.

      do_suffix blah.

      destruct_conjs; subst.
      repeat do_restl.
      
      repeat do_pl_immut.
      subst.
      repeat rewrite <- app_assoc.

      assert (lstar (conf (unannoPar t) p mt) blah (stop p (aeval (unannoPar t) p mt))).
      eauto.

      eapply lstar_tran.
      econstructor.
      simpl.

      assert (
          (cvm_thread_start n l p a mt
                            :: blah ++ [cvm_thread_end (Nat.pred n0) l p a; join (Nat.pred n0) p]) =
          (([cvm_thread_start n l p a mt] ++
                                         blah ++ [cvm_thread_end (Nat.pred n0) l p a]) ++ [join (Nat.pred n0) p])).
      { rewrite front_app.
        repeat rewrite <- app_assoc.
        tauto.
      }
      subst'.
      
      erewrite thread_bookend_peel.

      eapply lstar_transitive.

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      apply stbpstop.
      econstructor.
      eassumption.
Defined.


Lemma cvm_refines_lts_event_ordering_corrolary : forall t cvm_tr bits (*bits'*) et (*et'*) p (*p'*),
    well_formed_r t ->
    st_trace (run_cvm t
                      (mk_st (evc bits et) [] p)) = cvm_tr ->
    lstar (conf (unannoPar t) p et) cvm_tr (stop p (aeval (unannoPar t) p et)).
Proof.
  intros.
  destruct (copland_compile t {| st_ev := (evc bits et); st_trace := []; st_pl := p |}) eqn:hi.
  simpl in *.
  vmsts.
  simpl in *.
  Check cvm_refines_lts_event_ordering.
  simpl.
  assert (o = Some tt).
  {
    eapply always_some.
    eassumption.
    eassumption.
  }
  subst.
  destruct st_ev.

  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.

  eapply cvm_refines_lts_event_ordering with (t:=t) (cvm_tr:=st_trace) (bits:=bits) (et:=et) (bits':=e) (et':=e0) (p:=p) (p':=st_pl); eauto.
Defined.

Lemma range_par: forall t,
    range_par t = range (unannoPar t).
Proof.
  destruct t; eauto.
Defined.

Lemma wfr_implies_wfrannt :
  forall t,
    well_formed_r t ->
    well_formed_r_annt (unannoPar t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros;
        invc H;
    repeat find_apply_hyp_hyp;
    repeat rewrite range_par in *;
    econstructor; eauto.
Defined.

Theorem cvm_respects_event_system' : forall t cvm_tr ev0 ev1 bits bits' et et',
    well_formed_r t ->
    (*Ev_Shape e et -> *)
    copland_compile 
      t
      (mk_st (evc bits et) [] 0) =
    (Some tt, (mk_st (evc bits' et') cvm_tr 0)) ->
    (*cvm_to_lts_trace cvm_tr tr -> *)
    prec (ev_sys (unannoPar t) 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  eapply ordered.
  eapply wfr_implies_wfrannt; eauto.
  eapply cvm_refines_lts_event_ordering; eauto.
  eassumption.
Defined.

Lemma anno_unanno_par: forall a l l' annt,
    anno_par a l = (l', annt) ->
    unannoPar annt = a.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    assert (unannoPar a0 = a2) by eauto.
    congruence.
  -
    ff.
    assert (unannoPar a = a1) by eauto.
    congruence.
Defined.

Lemma fst_annopar: forall a a' l l',
    anno_par a l = (l', a') ->
    fst (range a) = fst (Term_Defs.range_par a').
Proof.
  intros.
  generalizeEverythingElse a.
  destruct a; intros; ff.
Defined.

Lemma snd_annopar_snd: forall a a' l l',
    anno_par a l = (l', a') ->
    Term_Defs.range_par a' = range a.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros; ff.
Defined.

Lemma wfr_par_irrel: forall a2 l l' l0 l0' a0 a0',
    well_formed_r_annt a2 ->
    anno_par a2 l' = (l0', a0') ->
    anno_par a2 l = (l0, a0) ->
    well_formed_r a0 ->
    well_formed_r a0'.
Proof.
  intros.
  unfold annotated_par in *.
  generalizeEverythingElse a2.
  induction a2; intros.
  -
    ff.
  -
    ff.
  -
    ff.
    invc H2.
    invc H.
    
    assert (well_formed_r a2).
    {
      eauto.
    }
    assert (well_formed_r a3).
    {
      eauto.
    }
    
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    erewrite <- fst_annopar.
    erewrite <- fst_annopar.
    reflexivity.
    eassumption.
    eassumption.
    erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    subst'.
    congruence.

    assert (
        Term_Defs.range_par a1 =
        Term_Defs.range_par a3).
    {
      rewrite range_par.
      rewrite range_par.
      erewrite anno_unanno_par.
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
      eassumption.
    }
    congruence.
  -
    ff.
    invc H2.
    invc H.
    
    assert (well_formed_r a2).
    {
      eauto.
    }
    assert (well_formed_r a3).
    {
      eauto.
    }
    
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    subst'.
    erewrite <- fst_annopar.
    erewrite <- fst_annopar.
    reflexivity.
    eassumption.
    eassumption.

    erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    subst'.
    congruence.

    assert (
        Term_Defs.range_par a1 =
        Term_Defs.range_par a3).
    {
      rewrite range_par.
      rewrite range_par.
      erewrite anno_unanno_par.
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
      eassumption.
    }
    congruence.
  -
    ff.
    invc H2.
    
    invc H.
    
    assert (well_formed_r a1).
    {
      eauto.
    }
    
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    subst'.
    erewrite <- fst_annopar.
    erewrite <- fst_annopar.
    reflexivity.
    eassumption.
    eassumption.
    subst'.
    subst'.
    rewrite <- H9.

    assert (
        Term_Defs.range_par a1 =
        Term_Defs.range_par a).
    {
      rewrite range_par.
      rewrite range_par.
      erewrite anno_unanno_par.
      erewrite anno_unanno_par.
      reflexivity.
      eassumption.
      eassumption.
    }
    congruence.
    congruence.
Defined.

Lemma wfr_annt_implies_wfr_par: forall a l l' a0,
    well_formed_r_annt a ->
    anno_par a l = (l', a0) ->
    well_formed_r a0.
Proof.

  
  intros.
  generalizeEverythingElse a.
  induction a; intros;
    invc H.
  -
    try econstructor;
      ff.
  -
    ff.
  -

    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    invc H0.
    simpl.

    assert (well_formed_r a) by eauto.
    assert (well_formed_r a3) by eauto.
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.

    eapply fst_annopar; eauto.

    erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    congruence.
    
    subst'.

    rewrite range_par.

    assert (unannoPar a3 = a2).
    {
      eapply anno_unanno_par.
      eassumption.
    }
    congruence.
  -

    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    invc H0.
    simpl.

    assert (well_formed_r a) by eauto.
    assert (well_formed_r a3) by eauto.
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    rewrite H7.
    
    eapply fst_annopar; eauto.

    erewrite snd_annopar_snd.
    erewrite snd_annopar_snd.
    2: { eassumption. }
    2: { eassumption. }
    subst'.
    congruence.

    subst'.

    rewrite range_par.

    assert (unannoPar a3 = a2).
    {
      eapply anno_unanno_par.
      eassumption.
    }
    congruence.
  -
    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    invc H0.
    simpl.

    assert (well_formed_r a) by eauto.
    
    econstructor.
    eassumption.
    eassumption.
    destruct r.
    simpl in *.
    subst.
    rewrite H7.

    eapply fst_annopar; eauto.
    rewrite <- H8.

    erewrite snd_annopar_snd; eauto.

    eassumption.
Defined.

Theorem cvm_respects_event_system : forall t cvm_tr ev0 ev1 bits bits' et et' t',
    t = annotated_par (annotated t') ->
    copland_compile
      t
      (mk_st (evc bits et) [] 0) =
    (Some tt, (mk_st (evc bits' et') cvm_tr 0)) ->

    prec (ev_sys (unannoPar t) 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  assert (well_formed_r t).
  {
    unfold annotated in H.
    unfold snd in *.
    break_let.
    subst.
    assert (well_formed_r_annt (annotated t')).
    {
      unfold annotated.
      unfold snd in *.
      eapply anno_well_formed_r.
      rewrite Heqp.
      reflexivity.
    }
    unfold annotated in *.
    unfold snd in *.
    rewrite Heqp in *.

    unfold annotated_par.
    assert (exists a', (annotated_par a) = a').
    {
      eexists.
      reflexivity.
    }
    destruct_conjs.
    unfold annotated_par in H3.
    rewrite H3.
   
    
    eapply wfr_annt_implies_wfr_par with (l:= 0).
    eassumption.
    assert (anno_par a 0 = (fst (anno_par a 0), snd (anno_par a 0))).
    {
      destruct (anno_par a 0); tauto.
    }
    rewrite H4.
    rewrite H3.
    reflexivity.
  }

  eapply ordered with (p:=0) (e:=et); eauto.
  eapply wfr_implies_wfrannt; eauto.
  eapply cvm_refines_lts_event_ordering; eauto.
  
Defined.

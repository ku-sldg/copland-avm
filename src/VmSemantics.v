(*
Proofs about the Copland Virtual Machine implementation, linking it to the Copland reference semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import More_lists Defs Term_Defs Term ConcreteEvidence LTS Event_system Term_system Main Appraisal_Evidence.
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

  eassumption.
Defined.

Ltac do_st_trace :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p |}]
     |- context[?tr]] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p |} )
      tauto
  end.

Ltac do_st_trace_assumps :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p |}]
     |- _] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p |} )
      tauto
  end.

Ltac find_rw_in_goal :=
  match goal with
  | [H': context[?x = _]
     |- context[?x]] =>
    rewrite H'; clear H'
  end.

Ltac cumul_ih :=
  match goal with
  | [H: context[(st_trace _ = _ ++ st_trace _)],
        H': copland_compileP ?t1 {| st_ev := _; st_trace := ?m ++ ?k; st_pl := _ |}
                             (Some tt)
                             ?v_full,
            H'': copland_compileP ?t1 {| st_ev := _; st_trace := ?k; st_pl := _ |}
                                  (Some tt)
                                  ?v_suffix
     |- _] =>
    assert_new_proof_by (st_trace v_full = m ++ st_trace v_suffix) eauto
  end.

Ltac wrap_ccp_dohi :=
  do_wf_pieces;
  rewrite <- ccp_iff_cc in *;
  dd;
  dohi;
  rewrite ccp_iff_cc in *.

Lemma st_trace_cumul' : forall t m k e p v_full v_suffix o_suffix,
    well_formed_r t ->

    copland_compileP t
               {| st_ev := e; st_trace := m ++ k; st_pl := p |}
               (Some tt) v_full ->
    
    copland_compileP t
                     {| st_ev := e; st_trace := k; st_pl := p |}
                     o_suffix v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  induction t; intros.
  -
    destruct r.
    wrap_ccp.
    
    destruct a; (* asp *)
      try destruct a; (* asp params *)
      simpl;
      df;
      repeat rewrite app_assoc;
      reflexivity.
  -
    wrap_ccp.
    repeat rewrite app_assoc.
    reflexivity.

  - (* alseq case *)
    wrap_ccp_dohi.
     
    cumul_ih.
    dd.
    repeat do_st_trace.
    repeat find_rw_in_goal.
    eauto.

  - (* abseq case *)
    wrap_ccp_dohi.
    
    repeat rewrite <- app_assoc in *.

    cumul_ih.
    dd.
    cumul_ih.
    dd.
    rewrite app_assoc.
    eauto.
    
  - (* abpar case *)
    wrap_ccp_dohi.

    repeat rewrite <- app_assoc in *.

    cumul_ih.
    dd.
    repeat rewrite app_assoc.
    eauto.
Defined.

(* Instance of st_trace_cumul' where k=[] *)
Lemma st_trace_cumul : forall t m e p v_full v_suffix o_suffix,
    well_formed_r t ->

    copland_compileP t
               {| st_ev := e; st_trace := m; st_pl := p |}
               (Some tt) v_full ->
    
    copland_compileP t
                     {| st_ev := e; st_trace := []; st_pl := p |}
                     o_suffix v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  intros.
  eapply st_trace_cumul'; eauto.
  repeat rewrite app_nil_r.
  eauto.
Defined.

Lemma exists_some_cc: forall t st,
    well_formed_r t ->
    exists st',
      copland_compile t st = (Some tt, st').
Proof.
  intros.
  destruct (copland_compile t st) eqn:ee.
  do_asome.
  subst.
  eauto.
Defined.

Ltac do_exists_some_cc t st :=
  match goal with
  | [H: well_formed_r t  |- _] =>
    assert_new_proof_by
      (exists st', copland_compile t st = (Some tt, st') )
      ltac:(eapply exists_some_cc; [apply H])
  end;
  destruct_conjs.

Lemma suffix_prop : forall t e e' tr tr' p p',
    well_formed_r t ->
    copland_compileP t
           {| st_ev := e;
              st_trace := tr;
              st_pl := p |}
           (Some tt)
           {|
             st_ev := e';
             st_trace := tr';
             st_pl := p' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.

  do_exists_some_cc t {| st_ev := e; st_trace := []; st_pl := p |}.

  rewrite ccp_iff_cc in *.

  repeat do_st_trace_assumps.
  repeat find_rw_in_goal.
  eexists.
  unfold st_trace at 2.
  erewrite st_trace_cumul'.
  2: {
    eassumption.
  }
  3: {
    apply H2.
  }
  simpl.
  tauto.
  rewrite app_nil_r.
  eassumption.
Defined.

Ltac do_suffix name :=
  match goal with
  | [H': copland_compileP ?t
         {| st_ev := _; st_trace := ?tr; st_pl := _ |}
         (Some tt)
         {| st_ev := _; st_trace := ?tr'; st_pl := _ |},
         H2: well_formed_r ?t |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H2 | apply H'])
             name
  end.

Lemma alseq_decomp : forall r t1' t2' e e'' p p'' tr,
    well_formed_r (alseq_par r t1' t2') ->
    copland_compileP (alseq_par r t1' t2')
                     {| st_ev := e; st_trace := []; st_pl := p |}
                     (Some tt)
                     {| st_ev := e''; st_trace := tr; st_pl := p'' |} ->

    exists e' tr' p',
      copland_compileP t1'
                       {| st_ev := e; st_trace := []; st_pl := p |}
                       (Some  tt)
                       {| st_ev := e'; st_trace := tr'; st_pl := p' |} /\
      exists tr'',
        copland_compileP t2'
                         {| st_ev := e'; st_trace := []; st_pl := p' |}
                         (Some tt)
                         {| st_ev := e''; st_trace := tr''; st_pl := p'' |} /\
        tr = tr' ++ tr''.     
Proof.
  intros.
  wrap_ccp_dohi.
  
  eexists.
  eexists.
  eexists.

  split.
  +
    eassumption.
  +
    do_exists_some_cc t2' {| st_ev := st_ev0; st_trace := []; st_pl := st_pl0 |}.
    vmsts.

    eexists.

    wrap_ccp_dohi.

    split.
    ++
      eassumption.
    ++
      repeat do_st_trace.
      repeat find_rw_in_goal.
      eapply st_trace_cumul; 
        eassumption.
Defined.

Lemma restl : forall t e e' x tr p p',
    well_formed_r t ->
    copland_compileP t
                     {| st_ev := e; st_trace := x; st_pl := p |}
                     (Some tt)
                     {| st_ev := e'; st_trace := x ++ tr; st_pl := p' |} ->

    copland_compileP t
                     {| st_ev := e; st_trace := []; st_pl := p |}
                     (Some tt)
                     {| st_ev := e'; st_trace := tr; st_pl := p' |}.
Proof.
  intros.

  do_exists_some_cc t  {| st_ev := e; st_trace := []; st_pl := p |}.
  wrap_ccp_dohi.

  assert (st_trace = tr).
  {
    do_st_trace.
    rewrite H1; clear H1.
    assert (tr = st_trace).
    {
      assert (StVM.st_trace {| st_ev := st_ev; st_trace := x ++ tr; st_pl := st_pl |} =
              x ++ StVM.st_trace {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl |}).
      {
        eapply st_trace_cumul;
        eassumption.
      }
      simpl in *.
      eapply app_inv_head; eauto.
    }
    rewrite H1; clear H1.
    simpl.
    tauto.
  }
  congruence.
Defined.

Ltac do_restl :=
  match goal with
  | [H: copland_compileP ?t
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p |}
        (Some tt)
        {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p' |},
        H2: well_formed_r ?t |- _] =>
    assert_new_proof_by
      (copland_compileP t
                        {| st_ev := e; st_trace := []; st_pl := p |}
                        (Some tt)
                        {| st_ev := e'; st_trace := x; st_pl := p' |})
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

Lemma back_app{A:Type}: forall (x y:A),
    [x; y] = [x] ++ [y].
Proof.
  intros.
  tauto.
Defined.

Lemma par_evidence_r: forall a p s e e2 e3,
    parallel_vm_thread a p (splitEv_r s e) = evc e2 e3 ->
    e3 = (eval (unanno a) p (splitEv_T_r s (get_et e))).
Proof.
  intros.

  rewrite par_evidence in *.
  destruct s.
  destruct s; destruct s0;
    simpl in *;
    
    erewrite eval_aeval with (i:=0);
    rewrite aeval_anno;
    try (unfold mt_evc in * );
    erewrite <- remote_Evidence_Type_Axiom;
    rewrite at_evidence;
    try (erewrite <- evc_inv);
    jkjke.
Defined.

Lemma cvm_refines_lts_evidence' : forall t tr tr' e e' p p',
    well_formed_r t ->
    copland_compileP t
                     (mk_st e tr p)
                     (Some tt)
                     (mk_st e' tr' p') ->
    get_et e' = (Term_Defs.eval (unanno (unannoPar t)) p (get_et e)).

Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.
    destruct a;
      try (
          try unfold get_et;
          dd;
          eauto).

  - (* at case *)
    rewrite <- ccp_iff_cc in *.
    destruct e.
    dd.
    
    erewrite eval_aeval.
    
    rewrite aeval_anno.
    eapply remote_Evidence_Type_Axiom.

  - (* alseq case *)
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    eassumption.
    eapply restl.
    eassumption.
    eassumption.
    destruct_conjs.

    wrap_ccp.
    
    destruct x.
    destruct e'.

    assert (e3 = get_et (evc e2 e3)) by tauto.
    repeat jkjke'.
    
  - (* abseq case *)

    wrap_ccp.
    
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
    dd.
    
    assert (get_et (evc e2 e3) = (eval (unanno (unannoPar t2)) p (splitEv_T_r s (get_et e)))).
    {
      destruct s.
      destruct s0.
      ++
        unfold splitEv_T_r.
        eauto.
      ++
        assert (mt = get_et (evc [] mt)) by tauto.
        jkjke.
        eauto.
    }
    simpl in *; subst.
    tauto.

  - (* abpar case *)
    wrap_ccp.

    do_suffix blah.

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
    dd.

    assert (e3 = (eval (unanno a) p (splitEv_T_r s (get_et e)))).
    {
      eapply par_evidence_r; eauto.
    }

    find_rw_in_goal.
    tauto.
    Unshelve.
    eauto.
Defined.

Lemma cvm_refines_lts_evidence : forall t tr tr' bits bits' et et' p p',
    well_formed_r t ->
    copland_compileP t
                     (mk_st (evc bits et) tr p)
                     (Some tt)
                     (mk_st (evc bits' et') tr' p') ->
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

Lemma cvm_refines_lts_event_ordering : forall t cvm_tr bits bits' et et' p p',
    well_formed_r t ->
    copland_compileP t
                     (mk_st (evc bits et) [] p)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr p') ->
    lstar (conf (unannoPar t) p et) cvm_tr (stop p (aeval (unannoPar t) p et)).
Proof.
  intros t cvm_tr bits bits' et et' p p' H H'.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.
    destruct a; (* asp *)
      try destruct a; (* asp params *)
      df;
      econstructor; try (econstructor; reflexivity).
    
  - (* aatt case *)
    rewrite <- ccp_iff_cc in *.
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
    eassumption.

    jkjke.
    simpl.
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

    wrap_ccp.
 
    econstructor.
    econstructor.
    subst.
    eapply lstar_transitive.
    eapply lstar_stls.
    
    eapply IHt1.
    eassumption.
    eassumption.

    eapply lstar_silent_tran.
    apply stlseqstop.

    eapply IHt2. (*with (e:= x). *)
    eassumption.
    assert (e0 = Term_Defs.eval (unanno (unannoPar t1)) p et).
    eapply cvm_refines_lts_evidence; eauto.

    subst.
    rewrite <- eval_aeval.
    
    eassumption.

  - (* abseq case *)
    wrap_ccp.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    assert (
        lstar (conf (unannoPar t1) p (splitEv_T_l s et)) blah' (stop p (aeval (unannoPar t1) p (splitEv_T_l s et)))
      ).
    {
      destruct s; destruct s; destruct s0;
        eauto.
    }

    assert (
      lstar (conf (unannoPar t2) p  (splitEv_T_r s et)) blah (stop p (aeval (unannoPar t2) p  (splitEv_T_r s et)))
    ).
    {
      destruct s; destruct s; destruct s0;
        eauto.
    }


    eapply lstar_transitive.
      simpl.

      eapply lstar_stbsl.
      eassumption.

      eapply lstar_silent_tran.
      apply stbslstop.
      
      eapply lstar_transitive.
      eapply lstar_stbsr.
      eassumption.
           
      econstructor.

      eapply stbsrstop.
      econstructor.

  - (* abpar case *)

    wrap_ccp.
    
    do_suffix blah.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf (unannoPar t) p (splitEv_T_l s et)) blah (stop p (aeval (unannoPar t) p (splitEv_T_l s et)))
      ).
    {
      destruct s; destruct s; destruct s0;
        eauto.
    }

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start n l p a (get_et (splitEv_r s (evc bits et)))]
                ++
                blah ++
                [cvm_thread_end (Nat.pred n0) l p a] =
              shuffled_events blah (remote_events a p)).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      jkjke.

      eapply lstar_transitive.

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      apply stbpstop.
      econstructor.
Defined.

Lemma cvm_refines_lts_event_ordering_corrolary : forall t cvm_tr bits et p,
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
  do_asome.
  subst.
  
  destruct st_ev.

  unfold run_cvm in *.
  monad_unfold.
  rewrite hi in *.
  simpl in *.

  eapply cvm_refines_lts_event_ordering with (t:=t) (cvm_tr:=st_trace) (bits:=bits) (et:=et) (bits':=e) (et':=e0) (p:=p) (p':=st_pl); eauto.
  econstructor; eauto.
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
    copland_compileP t
                     (mk_st (evc bits et) [] 0)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr 0) ->
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

Lemma wfr_annt_implies_wfr_par: forall a l a0,
    well_formed_r_annt a ->
    anno_parP a0 a l ->
    well_formed_r a0.
Proof.
  intros.
  generalizeEverythingElse a.
  induction a; intros;
    invc H.
  -
    invc H0.
    try econstructor;
      ff.
  -
    invc H0.
    ff.
  -
    invc H0.

    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.

    simpl.
    assert (anno_parP a a1 l).
    {
      econstructor.
      jkjke.
    }
    assert (anno_parP a0 a2 l0).
    {
      econstructor.
      jkjke.
    }

    assert (well_formed_r a) by eauto.
    assert (well_formed_r a0) by eauto.
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

    assert (unannoPar a0 = a2).
    {
      eapply anno_unanno_par.
      eassumption.
    }
    congruence.
  -

    invc H0.

    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    (*
    invc H0. *)
    simpl.

    assert (anno_parP a a1 l).
    {
      econstructor.
      jkjke.
    }
    assert (anno_parP a0 a2 l0).
    {
      econstructor.
      jkjke.
    }

    assert (well_formed_r a) by eauto.
    assert (well_formed_r a0) by eauto.
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

    assert (unannoPar a0 = a2).
    {
      eapply anno_unanno_par.
      eassumption.
    }
    congruence.
  -
    invc H0.
    unfold anno_par in *.
    repeat break_let.
    fold anno_par in *.
    (*
    invc H0. *)
    simpl.

    assert (anno_parP a a1 (S l)).
    {
      econstructor.
      jkjke.
    }
    (*
    assert (anno_parP a0 a2 l0).
    {
      econstructor.
      jkjke.
    }
     *)
    

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

Lemma annopar_well_formed_r: forall t t',
    t = annotated_par (annotated t') ->
    well_formed_r t.
Proof.
  intros.
  rewrite H in *.
  eapply wfr_annt_implies_wfr_par.
  2: {
    econstructor.
    unfold annotated_par in *.
    unfold annotated in *.
    assert (anno_par (snd (anno t' 0)) 0 = (fst (anno_par (snd (anno t' 0)) 0), snd (anno_par (snd (anno t' 0)) 0))).
    {
      destruct (anno_par (snd (anno t' 0)) 0); tauto.
    }
    reflexivity.
    (*
    jkjke.
    simpl. *)

  }
  eapply anno_well_formed_r.
  assert (anno t' 0 = (fst (anno t' 0), snd (anno t' 0))).
  {
    destruct (anno t' 0); tauto.
  }
  jkjke.
Defined.

Theorem cvm_respects_event_system : forall pt t cvm_tr ev0 ev1 bits bits' et et' anno_t,
    annoP anno_t t 0 ->
    anno_parP pt anno_t 0 ->
    copland_compileP pt
                     (mk_st (evc bits et) [] 0)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr 0) ->

    prec (ev_sys anno_t 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.

  assert (well_formed_r pt).
  {
    inversion H0.
    inversion H.
    eapply annopar_well_formed_r.
    unfold annotated.
    rewrite <- H7.
    unfold annotated_par.
    rewrite H3.
    tauto.
  }


  assert (well_formed_r_annt anno_t(*(unannoPar t)*)).
  {
    destruct (anno_par anno_t 0) eqn: hi.
    inversion H0.
    rewrite <- anno_unanno_par with (l:=0) (l':=l) (annt:=pt).
    2: {
      assert (a = pt).
      {
        subst.
        jkjke.
      }
      congruence.
    }
    eapply wfr_implies_wfrannt.
    eassumption.
  }
  eapply ordered; try eassumption.
  assert (anno_t = unannoPar pt).
  {
    destruct (anno_par anno_t 0) eqn: hi.
    inversion H0.
    erewrite anno_unanno_par.
    reflexivity.
    rewrite H5.
    rewrite hi.
    reflexivity.
  }
  rewrite H5.
  eapply cvm_refines_lts_event_ordering; eauto.
Defined.

Print run_cvm.
Check st_trace.

Theorem cvm_respects_event_system_run : forall pt t cvm_tr ev0 ev1 bits (*bits' et' *)et  anno_t,
    annoP anno_t t 0 ->
    anno_parP pt anno_t 0 ->
    st_trace (run_cvm pt (mk_st (evc bits et) [] 0)) = cvm_tr ->

    (*
    =
    (mk_st (evc bits' et') cvm_tr 0) ->
     *)
    

    prec (ev_sys anno_t 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  assert (well_formed_r pt).
  {
    inversion H0.
    inversion H.
    subst.
    eapply annopar_well_formed_r.
    unfold annotated_par.
    unfold annotated.
    reflexivity.
  }

  destruct ((copland_compile pt {| st_ev := evc bits et; st_trace := []; st_pl := 0 |})) eqn:hi.
  do_somett.
  subst.

  simpl in *. destruct c.
  simpl in *.
  unfold run_cvm in *.
  unfold execSt in *.
  rewrite hi.
  simpl.
  destruct st_ev.
  do_pl_immut.
  subst.
  
  eapply cvm_respects_event_system.
  eassumption.
  eassumption.
  econstructor.
  eassumption.
  eassumption.
Defined.

Theorem cvm_respects_event_system_run' : forall pt t cvm_tr ev0 ev1 bits (*bits' et' *)et  anno_t,
    anno_t = annotated t ->
    pt = annotated_par anno_t ->
    (*
    annoP anno_t t 0 ->
    anno_parP pt anno_t 0 -> *)
    st_trace (run_cvm pt (mk_st (evc bits et) [] 0)) = cvm_tr ->

    (*
    =
    (mk_st (evc bits' et') cvm_tr 0) ->
     *)
    

    prec (ev_sys anno_t 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  eapply cvm_respects_event_system_run.
  econstructor.
  eassumption.
  econstructor.
  eassumption.
  eassumption.
  eassumption.
Defined.
  

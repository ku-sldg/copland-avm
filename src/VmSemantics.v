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


Set Nested Proofs Allowed.

(*
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
*)

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

(*
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
*)

Lemma st_trace_irrel : forall t tr1 tr1' tr2 tr2' e e' e'' p p' p'' i i' i'',
    (*well_formed_r t -> *)
    copland_compile t
           {| st_ev := e; st_trace := tr1; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p'; st_evid := i' |}) ->

    copland_compile t
           {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := e''; st_trace := tr2'; st_pl := p''; st_evid := i'' |}) ->
    
    e' = e'' /\ p' = p'' /\ i' = i''.
Proof.
  intros.

  assert (st_ev
      (execSt (copland_compile t)
              {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i |}) = e').
  eapply trace_irrel_ev; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_pl
            (execSt (copland_compile t)
                    {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i |}) = p').
  eapply trace_irrel_pl; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.

  assert (st_evid
            (execSt (copland_compile t)
                    {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i |}) = i').
  eapply trace_irrel_evid; eauto.
  unfold execSt in *.
  subst''.
  simpl in *.
  
  subst''.
  simpl in *.
  repeat split; try congruence.
Defined.

Lemma alseq_decomp_gen : forall t1' t2' e e'' p p'' init_tr tr i i'',
    (*well_formed_r (alseq_par r t1' t2') -> *)
    copland_compile (alseq_par t1' t2') {| st_ev := e; st_trace := init_tr; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''; st_evid := i'' |}) ->

    exists e' tr' p' i',
      copland_compile t1' {| st_ev := e; st_trace := init_tr; st_pl := p; st_evid := i |} =
      (Some  tt, {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |}) /\
        copland_compile t2' {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |} =
        (Some tt, {| st_ev := e''; st_trace := tr; st_pl := p''; st_evid := i'' |}).     
Proof.
  intros.
  (*
  do_wf_pieces. *)
  df.
  dosome.
  annogo.
  exists st_ev. exists st_trace. exists st_pl. exists st_evid.
  split.
  reflexivity.

  eassumption.
Defined.

Ltac do_st_trace :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i |}]
     |- context[?tr]] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |} )
      tauto
  end.

Ltac do_st_trace_assumps :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i |}]
     |- _] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |} )
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
        H': copland_compileP ?t1 {| st_ev := _; st_trace := ?m ++ ?k; st_pl := _; st_evid := _ |}
                             (Some tt)
                             ?v_full,
            H'': copland_compileP ?t1 {| st_ev := _; st_trace := ?k; st_pl := _; st_evid := _ |}
                                  (Some tt)
                                  ?v_suffix
     |- _] =>
    assert_new_proof_by (st_trace v_full = m ++ st_trace v_suffix) eauto
  end.

Ltac wrap_ccp_dohi :=
  (*do_wf_pieces; *)
  rewrite <- ccp_iff_cc in *;
  dd;
  dohi;
  rewrite ccp_iff_cc in *.

Lemma st_trace_cumul' : forall t m k e p v_full v_suffix o_suffix i,
    (*well_formed_r t -> *)

    copland_compileP t
               {| st_ev := e; st_trace := m ++ k; st_pl := p; st_evid := i |}
               (Some tt) v_full ->
    
    copland_compileP t
                     {| st_ev := e; st_trace := k; st_pl := p; st_evid := i |}
                     o_suffix v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  induction t; intros.
  -
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
Lemma st_trace_cumul : forall t m e p v_full v_suffix o_suffix i,
    (*well_formed_r t -> *)

    copland_compileP t
               {| st_ev := e; st_trace := m; st_pl := p; st_evid := i |}
               (Some tt) v_full ->
    
    copland_compileP t
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}
                     o_suffix v_suffix ->

    st_trace v_full = m ++ st_trace v_suffix.
Proof.
  intros.
  eapply st_trace_cumul'; eauto.
  repeat rewrite app_nil_r.
  eauto.
Defined.

Lemma exists_some_cc: forall t st,
    (*well_formed_r t -> *)
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
    assert_new_proof_by
      (exists st', copland_compile t st = (Some tt, st') )
      ltac:(eapply exists_some_cc);
    destruct_conjs.

(*
Ltac do_exists_some_cc t st :=
  match goal with
  | [H: well_formed_r t  |- _] =>
    assert_new_proof_by
      (exists st', copland_compile t st = (Some tt, st') )
      ltac:(eapply exists_some_cc; [apply H])
  end;
  destruct_conjs.
*)

Lemma suffix_prop : forall t e e' tr tr' p p' i i',
    (*well_formed_r t -> *)
    copland_compileP t
           {| st_ev := e;
              st_trace := tr;
              st_pl := p;
              st_evid := i |}
           (Some tt)
           {|
             st_ev := e';
             st_trace := tr';
             st_pl := p';
             st_evid := i' |} ->
    exists l, tr' = tr ++ l.
Proof.
  intros.

  do_exists_some_cc t {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}.

  rewrite ccp_iff_cc in *.

  repeat do_st_trace_assumps.
  repeat find_rw_in_goal.
  eexists.
  unfold st_trace at 2.
  erewrite st_trace_cumul'.
  3: {
    apply H1.
  }
  simpl.
  tauto.
  rewrite app_nil_r.
  eassumption.
Defined.

Ltac do_suffix name :=
  match goal with
  | [H': copland_compileP ?t
         {| st_ev := _; st_trace := ?tr; st_pl := _; st_evid := _ |}
         (Some tt)
         {| st_ev := _; st_trace := ?tr'; st_pl := _; st_evid := _ |}
         (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_as_by
      (exists l, tr' = tr ++ l)
      ltac:(eapply suffix_prop; [apply H'])
             name
  end.

Lemma alseq_decomp : forall t1' t2' e e'' p p'' tr i i'',
    (*well_formed_r (alseq_par r t1' t2') -> *)
    copland_compileP (alseq_par t1' t2')
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := e''; st_trace := tr; st_pl := p''; st_evid := i'' |} ->

    exists e' tr' p' i',
      copland_compileP t1'
                       {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}
                       (Some  tt)
                       {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |} /\
      exists tr'',
        copland_compileP t2'
                         {| st_ev := e'; st_trace := []; st_pl := p'; st_evid := i' |}
                         (Some tt)
                         {| st_ev := e''; st_trace := tr''; st_pl := p''; st_evid := i'' |} /\
        tr = tr' ++ tr''.     
Proof.
  intros.
  wrap_ccp_dohi.
  
  eexists.
  eexists.
  eexists.
  eexists.

  split.
  +
    eassumption.
  +
    do_exists_some_cc t2' {| st_ev := st_ev0; st_trace := []; st_pl := st_pl0; st_evid := st_evid0 |}.
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

Lemma restl : forall t e e' x tr p p' i i',
    (*well_formed_r t -> *)
    copland_compileP t
                     {| st_ev := e; st_trace := x; st_pl := p; st_evid := i|}
                     (Some tt)
                     {| st_ev := e'; st_trace := x ++ tr; st_pl := p'; st_evid := i' |} ->

    copland_compileP t
                     {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}
                     (Some tt)
                     {| st_ev := e'; st_trace := tr; st_pl := p'; st_evid := i' |}.
Proof.
  intros.

  do_exists_some_cc t  {| st_ev := e; st_trace := []; st_pl := p; st_evid := i |}.
  wrap_ccp_dohi.

  assert (st_trace = tr).
  {
    do_st_trace.
    rewrite H0; clear H0.
    assert (tr = st_trace).
    {
      assert (StVM.st_trace {| st_ev := st_ev; st_trace := x ++ tr; st_pl := st_pl; st_evid := st_evid|} =
              x ++ StVM.st_trace {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl; st_evid := st_evid |}).
      {
        eapply st_trace_cumul; 
        eassumption.
      }
      simpl in *.
      eapply app_inv_head; eauto.
    }
    rewrite H0; clear H0.
    simpl.
    tauto.
  }
  congruence.
Defined.

Ltac do_restl :=
  match goal with
  | [H: copland_compileP ?t
        {| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i |}
        (Some tt)
        {| st_ev := ?e'; st_trace := ?tr ++ ?x; st_pl := ?p'; st_evid := ?i' |}
        (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_by
      (copland_compileP t
                        {| st_ev := e; st_trace := []; st_pl := p; st_evid := i|}
                        (Some tt)
                        {| st_ev := e'; st_trace := x; st_pl := p'; st_evid := i' |})
      ltac:(eapply restl; [apply H])
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

Ltac do_t_at_zero t x :=
  let y := fresh in
  assert (exists l' t', anno_par t 0 = (l',t')) as y by
        (destruct (anno_par t 0); repeat eexists);
  destruct y;
  destruct y as [x].

Ltac do_assert_remote t e p i :=
  assert (
      copland_compile t
                      {| st_ev := e; st_trace := []; st_pl := p; st_evid := i|} =
      (Some tt,
       {| st_ev := doRemote_session (unannoPar t) p e;
                   st_trace := cvm_events (unannoPar t) p (get_et e);
                               st_pl := p;
                                        st_evid := (i + event_id_span (unannoPar t))
       |})
    ) by
    (eapply copland_compile_at).
     (*eapply wfr_annt_implies_wfr_par; 
     [eassumption | econstructor; jkjke]). *)

Ltac do_assert_unannoPar t x :=
  assert (t = unannoPar x) by
    (erewrite anno_unanno_par;
     [reflexivity | eassumption]).

Ltac do_assume_remote t e p x :=
  do_t_at_zero t x;
  do_assert_remote x e p;
  do_assert_unannoPar t x.

(*
Lemma par_evidence_r: forall a p s e e2 e3 l,
    (*well_formed_r_annt a -> *)
    parallel_vm_thread l a p (splitEv_r s e) = evc e2 e3 ->
    e3 = (eval (unanno a) p (splitEv_T_r s (get_et e))).
Proof.
  intros.


  (*
  do_assume_remote a (splitEv_r s e) p XX.

  rewrite par_evidence in *.
  rewrite <- H3 in *.
  rewrite at_evidence in *.
  rewrite H0 in *.
  erewrite eval_aeval.

  rewrite aeval_anno.
  try (erewrite <- remote_Evidence_Type_Axiom).
  rewrite at_evidence in *.
  destruct s; destruct s; destruct s0;
        simpl in *;

        (*
    erewrite eval_aeval with (i:=0);
    rewrite aeval_anno; *)
        try (unfold mt_evc in * );
        (*
    try (erewrite <- remote_Evidence_Type_Axiom); *)
    (*rewrite at_evidence; *)
    try (erewrite <- evc_inv);
    jkjke.
    
  simpl in *.
  rewrite <- evc_inv.
  repeat jkjke.
  rewrite <- H3.
  
  rewrite H0.
  tauto.
  rewrite <- H0.
  jkjke.
  rewrite H3.


  
  assert (evc e2 e3 = evc (get_bits (evc e2 e3)) (get_et (evc e2 e3))).

  {
    admit.
  }
  rewrite <- H0 in H4.
  rewrite H4.
  
  Check evc_inv.
  erewrite evc_inv.
  
  Check evc_inv.
  

  
    rewrite at_evidence;
    try (erewrite <- evc_inv);
    jkjke.

  eapply cvm_

  rewrite anno_unanno.
   *)
  

  
  destruct s.
  destruct s; destruct s0;

  simpl in *;

    (*
    erewrite eval_aeval with (i:=0);
    rewrite aeval_anno;
    try (unfold mt_evc in * );
  

  
  
    try (erewrite <- remote_Evidence_Type_Axiom);
    rewrite at_evidence;
    try (erewrite <- evc_inv);
    jkjke.




  
    simpl in *;
     *)
    
    
    erewrite eval_aeval with (i:=0);
    rewrite aeval_anno;
    try (unfold mt_evc in * );
    try (erewrite <- remote_Evidence_Type_Axiom);
    rewrite at_evidence;
    try (erewrite <- evc_inv);
    jkjke.
Defined.
 *)

Lemma par_evidence_r: forall a p s e et e2 e3 l,
    parallel_vm_thread l a p (splitEv_r s (evc e et)) = evc e2 e3 ->
    e3 = (eval a p (splitEv_T_r s et)).
Proof.
  intros.

  rewrite par_evidence in *.
  destruct s.
  destruct s; destruct s0;
    simpl in *;

    (*
    erewrite eval_aeval with (i:=0);
    rewrite aeval_anno; *)
    try (unfold mt_evc in * );
    erewrite <- remote_Evidence_Type_Axiom;
    rewrite at_evidence;
    try (erewrite <- evc_inv);
    jkjke.
Defined.

Lemma cvm_refines_lts_evidence : forall t tr tr' bits bits' et et' p p' i i',
    (*well_formed_r t -> *)
    copland_compileP t
                     (mk_st (evc bits et) tr p i)
                     (Some tt)
                     (mk_st (evc bits' et') tr' p' i') ->
    et' = (Term_Defs.eval (unannoPar t) p et).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    rewrite <- ccp_iff_cc in *.
    destruct a;
      try (
          (*try unfold get_et; *)
          dd;
          eauto).

  - (* at case *)
    rewrite <- ccp_iff_cc in *.
    (*
    destruct e. *)
    dd.

    (*
    
    erewrite eval_aeval.
    
    
    rewrite aeval_anno. *)
    erewrite <- remote_Evidence_Type_Axiom.
    jkjke.

  - (* alseq case *)
    do_suffix blah.
    destruct_conjs.
    subst.

    edestruct alseq_decomp.
    (*
    eassumption. *)
    eapply restl.
    eassumption.
    destruct_conjs.

    wrap_ccp.
    
    destruct x.
    (*
    destruct e. *)
    repeat jkjke'.

    (*

    
    assert (e3 = get_et (evc e2 e3)) by tauto.
    repeat jkjke'. *)
    
  - (* abseq case *)

    wrap_ccp.
    
    do_suffix blah.
    do_suffix blah'.
    
    destruct_conjs; subst.
    repeat do_restl.

    assert (e = (eval (unannoPar t1) p (splitEv_T_l s et))).
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

    assert (e0 = (eval (unannoPar t2)) p (splitEv_T_r s et)).
    {
      destruct s.
      destruct s0.
      ++
        unfold splitEv_T_r.
        eauto.
      ++
        simpl.
        eauto.
    }
    
    simpl in *; subst.
    tauto.

  - (* abpar case *)
    wrap_ccp.

    do_suffix blah.

    destruct_conjs; subst.
    repeat do_restl.

    assert (e = (eval (unannoPar t)) p (splitEv_T_l s et)).
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

    assert (e0 = (eval t0 p (splitEv_T_r s et))).
    {
      eapply par_evidence_r; eauto.
    }

    find_rw_in_goal.
    tauto.
Defined.

(*
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
    destruct e.

    
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
*)

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

Lemma cvm_spans: forall t e tr p i e' tr' p' i',
    copland_compileP t
                     {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |}
                     (Some tt)
                     {|
                       st_ev := e';
                       st_trace := tr';
                       st_pl := p';
                       st_evid := i'
                     |} ->
    i' = i + event_id_span (unannoPar t).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a.
    +
      wrap_ccp.
      tauto.
    +
      wrap_ccp.
      unfold tag_ASP in *.
      destruct a.
      ff.
    +
      wrap_ccp.
      tauto.
    +
      wrap_ccp.
      tauto.
  -
    wrap_ccp.
    simpl.
    lia.
  -
    wrap_ccp.
    assert (st_evid0 = i + event_id_span (unannoPar t1)) by eauto.
    assert (i' = st_evid0 + event_id_span (unannoPar t2)) by eauto.
    subst.
    lia.
  -
    wrap_ccp.
    assert (st_evid1 = (i + 1) + event_id_span (unannoPar t1)) by eauto.
    assert (st_evid = st_evid1 + event_id_span (unannoPar t2)) by eauto.
    subst.
    lia.
  -
    wrap_ccp.
    assert (st_evid = (i + 1) + event_id_span (unannoPar t)) by eauto.
    subst.
    lia.
Defined.

Lemma span_cvm: forall atp t annt loc i j e e' tr tr' p p' i',
    copland_compileP atp
                     {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |} 
                     (Some tt)
                     {| st_ev := e'; st_trace := tr'; st_pl := p'; st_evid := i' |} ->
    
    anno_parP atp t loc ->
    anno t i = (j, annt) ->
    j = i'.

Proof.
  intros.
  assert (j = i + event_id_span t).
  {
    assert (j - i = event_id_span t).
    {
      symmetry.
      eapply span_range.
      eauto.
    }
    rewrite <- H2.
    assert (j > i).
    {
      eapply anno_mono; eauto.
    }
    
    lia.
  }
  subst.
  symmetry.
  assert (t = unannoPar atp).
  {
    destruct (anno_par t loc) eqn: hi.
    
    inversion H0.
    erewrite anno_unanno_par.
    reflexivity.
    rewrite hi.
    subst.
    rewrite hi.
    tauto.
  }
  rewrite H2.

  
  eapply cvm_spans.
  eassumption.
Defined.

Lemma cvm_refines_lts_event_ordering : forall t atp annt cvm_tr bits bits' et et' p p' i i' loc,
    anno_parP atp t loc ->
    annoP annt t i ->
    (*
    well_formed_r_annt annt -> *)
    copland_compileP atp
                     (mk_st (evc bits et) [] p i)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr p' i') ->
    lstar (conf annt p et) cvm_tr (stop p (aeval annt p et)).
Proof.
  intros t atp annt cvm_tr bits bits' et et' p p' i i' loc annoParPH annPH H'.
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
    wrap_ccp.
    invc annPH;
      destruct a; df;   
        repeat break_match; try solve_by_inversion;
          try unfold tag_ASP in *;
          df;
          
          econstructor; try (econstructor; reflexivity).
    
  - (* aatt case *)
    wrap_ccp.

    (*
    rewrite <- ccp_iff_cc in *.
    destruct r. 
     *)
    
    repeat (df; try dohtac; df).

    inv_annoparP.
    invc annPH.
    cbn in *.
    repeat break_let.
    assert (annoP a t (S i)).
    {
      econstructor.
      jkjke.
    }
    dd.

    assert (t = unanno a) as H3.
    {
      invc H1.
      rewrite anno_unanno.
      tauto.
    }
    
    assert (lstar (conf a n et) (cvm_events t n et) (stop n (aeval a n et))).
    {
      rewrite H3.

      apply remote_LTS.
    }

    
    assert (i = fst (i, S n0)) as H2 by tauto.
    

    rewrite H2 at 2.
    rewrite H3.


                                
    
    eapply lstar_tran.
    econstructor.
    (*econstructor. *)
    simpl.
    eapply lstar_transitive.
    eapply lstar_strem.
    rewrite <- H3.
    cbn.
    eassumption.

    
    jkjke.
    simpl.
    assert (et' = (aeval a n et)).
    {
      rewrite <- eval_aeval.
      erewrite <- remote_Evidence_Type_Axiom.
      rewrite <- H3.
      rewrite H0.
      tauto.
    }
    rewrite <- H4.
    rewrite <- H3.

    assert ((S i) + event_id_span t = n0).
    {
      assert (event_id_span t = n0 - (S i)).
      {
        eapply span_range.
        eassumption.
      }
      rewrite H5.
      assert (n0 > (S i)).
      {
        eapply anno_mono.
        eassumption.
      }
      lia.
    }

    assert ((i + 1 + event_id_span t) = (S i) + event_id_span t).
    {
      lia.
    }
    rewrite H6.
    rewrite H5.
    rewrite H0.
    simpl.
    
    

    
    econstructor.

    apply stattstop.
    econstructor.

  -  (* alseq case *)
    (*
    do_wf_pieces. *)

    invc annoParPH.
    invc annPH.
    dd.
    do_annopar_redo.
    do_annopar_redo.

    
    edestruct alseq_decomp; eauto.
    destruct_conjs.
    destruct x.

    
 
    econstructor.
    econstructor.
    subst.
    eapply lstar_transitive.
    eapply lstar_stls.
    
    eapply IHt1.
    eassumption.
    econstructor; jkjke.
    eassumption.

    eapply lstar_silent_tran.
    apply stlseqstop.

    eapply IHt2. (*with (e:= x). *)
    eassumption.
    econstructor; jkjke.
    assert (e = Term_Defs.eval (unannoPar a) p et).
    eapply cvm_refines_lts_evidence; eauto.


    subst.
    rewrite <- eval_aeval.
    assert (unannoPar a = unanno a1).
    {
      assert (unannoPar a = t1).
      {
        inversion Heqp0.
        destruct (anno_par t1 loc) eqn: hi.
        eapply anno_unanno_par.
        rewrite H5.
        simpl.
        eassumption.
      }
      assert (unanno a1 = t1).
      {
        
        erewrite <- anno_unanno.
        rewrite Heqp2.
        simpl.
        tauto.
      }
      congruence.
    }
    rewrite <- H5.
    assert (H0 = p).
    { wrap_ccp.
      tauto.
    }
    subst.
    assert (H1 = i + event_id_span t1).
    {

      assert (t1 = unannoPar a).
      {
        destruct (anno_par t1 loc) eqn: hi.
        erewrite anno_unanno_par.
        reflexivity.
        inversion Heqp0.
        rewrite H0.
        rewrite hi.
        
        simpl.
        
        tauto.
      }
     
      rewrite H0.
      eapply cvm_spans; eauto.

    }
    assert (n = i + event_id_span t1).
    {
      
      Check span_range.
      (*
     : forall (t : Term) (i j : nat) (t' : AnnoTerm),
       anno t i = (j, t') -> event_id_span t = j - i
       *)
      assert (event_id_span t1 = n - i).
      {
      
        eapply span_range.
        eassumption.
      }
      rewrite H6.
      assert (n > i).
      {
        eapply anno_mono.
        eassumption.
      }
      lia.

    }
    assert (n = H1) by congruence.
    subst.
    
    eassumption.

  - (* abseq case *)


    inversion annoParPH.
    inversion annPH.
    subst.

    
    wrap_ccp.

    assert (n = st_evid1).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      
      eapply span_cvm; eauto.
    }

    assert (n0 = st_evid).
    {
      subst.
      eapply span_cvm; eauto.
    }
    
    repeat do_anno_redo.
    
    do_suffix blah.
    do_suffix blah'.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    eapply lstar_tran.
    econstructor.
    simpl.

    assert (
        lstar (conf a1 p (splitEv_T_l s et)) blah' (stop p (aeval a1 p (splitEv_T_l s et)))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      destruct s; destruct s; destruct s0;
        simpl in *;
        eauto.
    }

    assert (
      lstar (conf a2 p  (splitEv_T_r s et)) blah (stop p (aeval a2 p  (splitEv_T_r s et)))
    ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.

      subst.
      destruct s; destruct s; destruct s0;
        simpl in *; eauto.

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


(*
    

    wrap_ccp.
    
    do_suffix blah.
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.
 *)
    inversion annoParPH.
    inversion annPH.
    subst.

    
    wrap_ccp.

    assert (n = st_evid).
    {
      assert (i+1 = S i) by lia.
      find_rewrite.
      
      eapply span_cvm; eauto.
    }

    assert (n0 = n + event_id_span t2).
    {
      Check span_range.
      assert (event_id_span t2 = n0 - n).
      {
        eapply span_range.
        eauto.
      }
      assert (n0 > n).
      {
        eapply anno_mono; eauto.
      }
      lia.
    }
    

    (*
    assert (n0 = st_evid).
    {
      subst.
      eapply span_cvm; eauto.
    } *)
    
    repeat do_anno_redo.
    
    do_suffix blah.
    (*
    do_suffix blah'. *)
    destruct_conjs; subst.
    repeat do_restl.
    
    repeat rewrite <- app_assoc.

    assert (
        lstar (conf a0 p (splitEv_T_l s et)) blah (stop p (aeval a0 p (splitEv_T_l s et)))
      ).
    {
      assert (i + 1 = S i) by lia.
      find_rewrite.
      destruct s; destruct s; destruct s0; simpl in *;
        eauto.
    }
    (*
    
      eapply IHt1. apply Heqp0. apply Heqp1.
      eapply IHt1; eauto.
      eapply IHt; eauto.
      eapply IHt; eauto.
    } *)

      eapply lstar_tran.
      econstructor.
      simpl.

      rewrite front_app.
      rewrite back_app.

      assert ([cvm_thread_start loc p t2 (get_et (splitEv_r s (evc bits et)))]
                ++
                blah ++
                [cvm_thread_end loc] =
              shuffled_events blah (cvm_events t2 p (get_et (splitEv_r s (evc bits et))))).
      {
        eapply thread_bookend_peel.
        eassumption.
      }

      repeat rewrite app_assoc in *.
      jkjke.

      assert (
          (splitEv_T_r s et) =
          (get_et (splitEv_r s (evc bits et)))).
      {
        destruct s; destruct s; destruct s0; ff.
      }
      jkjke.

      assert (t2 = unanno a1).
      {
        invc Heqp2.
        erewrite anno_unanno.
        tauto.
      }
      subst.
      

      eapply lstar_transitive.
      

      eapply bpar_shuffle.
      eassumption.

      eapply lstar_tran.
      (*
      assert (n0 = st_evid).
      {
        eapply span_cvm.
        


        admit. }
      find_rw_in_goal. *)


      apply stbpstop.
      econstructor.
Defined.
Print anno_parP.

Lemma cvm_refines_lts_event_ordering_corrolary : forall t annt atp cvm_tr bits et p loc i,
    (*well_formed_r_annt t -> *)
    annoP annt t i ->
    anno_parP atp t loc ->
    st_trace (run_cvm atp
                      (mk_st (evc bits et) [] p i)) = cvm_tr ->
    lstar (conf annt p et) cvm_tr (stop p (aeval annt p et)).
Proof.
  intros.
  destruct (copland_compile atp {| st_ev := (evc bits et); st_trace := []; st_pl := p; st_evid := i |}) eqn:hi.
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
  Check cvm_refines_lts_event_ordering.

  eapply cvm_refines_lts_event_ordering; eauto.
  econstructor; eauto.
Defined.

Theorem cvm_respects_event_system : forall atp annt t cvm_tr ev0 ev1 bits bits' et et' i i' loc,
    (*well_formed_r t -> *)
    annoP annt t i ->
    anno_parP atp t loc ->
    copland_compileP atp
                     (mk_st (evc bits et) [] 0 i)
                     (Some tt)
                     (mk_st (evc bits' et') cvm_tr 0 i') ->
    prec (ev_sys annt 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  Lemma anno_redo: forall t i annt,
    annoP annt t i ->
    exists i', anno t i = (i', annt).
  Proof.
    intros.
    destruct (anno t i) eqn:hi.
    invc H.
    eexists.
    rewrite hi.
    tauto.
  Defined.

  edestruct anno_redo; eauto.
    

    
  assert (well_formed_r_annt annt).
  eapply anno_well_formed_r.
  eassumption.

  
  eapply ordered.
  eapply anno_well_formed_r.
  eassumption.

  eapply cvm_refines_lts_event_ordering; eauto.
  eassumption.
Defined.


(*
Theorem cvm_respects_event_system : forall pt t cvm_tr ev0 ev1 bits bits' et et' anno_t,
    annoP annt t 0 ->
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
*)

Theorem cvm_respects_event_system_run : forall atp annt t cvm_tr ev0 ev1 bits (*bits' et' *)et i loc,
    annoP annt t i ->
    anno_parP atp t loc ->
    st_trace (run_cvm atp (mk_st (evc bits et) [] 0 i)) = cvm_tr ->

    (*
    =
    (mk_st (evc bits' et') cvm_tr 0) ->
     *)
    

    prec (ev_sys annt 0 et) ev0 ev1 ->
    earlier cvm_tr ev0 ev1.
Proof.
  intros.
  assert (well_formed_r_annt annt).
  {
    edestruct anno_redo.
    eassumption.
    eapply anno_well_formed_r.
    eassumption.
  }

  destruct ((copland_compile atp {| st_ev := evc bits et; st_trace := []; st_pl := 0; st_evid := i |})) eqn:hi.
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

Theorem cvm_respects_event_system_run' : forall atp annt t cvm_tr ev0 ev1 bits (*bits' et' *)et,
    annt = annotated t ->
    atp = annotated_par t ->
    (*
    annoP anno_t t 0 ->
    anno_parP pt anno_t 0 -> *)
    st_trace (run_cvm atp (mk_st (evc bits et) [] 0 0)) = cvm_tr ->

    (*
    =
    (mk_st (evc bits' et') cvm_tr 0) ->
     *)
    

    prec (ev_sys annt 0 et) ev0 ev1 ->
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
  

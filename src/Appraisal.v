Require Import GenStMonad MonadVM MonadAM ConcreteEvidence MonadVMFacts.
Require Import StAM Axioms_Io Impl_vm Impl_appraisal Maps VmSemantics Event_system Term_system External_Facts.
Require Import Auto AutoApp AllMapped.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

Lemma ba_const : forall e a_st a_st' o,
    build_app_comp_ev e a_st = (o, a_st') ->
    a_st = a_st'.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros.
  -
    ff; eauto.
  -
    repeat ff; eauto.
  (*
    edestruct IHa.
    eassumption.
    destruct_conjs.
    simpl in *.
    subst.
    tauto. *)
  -
    repeat ff; eauto.
  -
    repeat ff; eauto.
    
Defined.

Ltac do_ba_st_const :=
  let tac := (eapply ba_const; eauto) in
  repeat (
      match goal with
      | [H: build_app_comp_ev _ ?a_st = (_, ?a0) |- _] =>
        assert_new_proof_by (a_st = a0) tac
      end);
  subst.

Lemma build_app_some' : forall e a_st,
    (exists o, build_app_comp_ev e a_st = (Some o, a_st)) ->
    evMapped e a_st.
Proof.
  induction e; intros.
  -
    econstructor.
  -
    repeat ff.
    +
      destruct_conjs.
      ff.
      econstructor.
      tauto.
      eauto.
      eexists.
      econstructor.
      eassumption.
    +
      destruct_conjs.
      solve_by_inversion.
    +
      destruct_conjs.
      solve_by_inversion.
  -
    repeat ff.
    +
      destruct_conjs.
      ff.
      econstructor.
      tauto.
      eauto.
      eexists.
      econstructor.
      eassumption.
    +
      destruct_conjs.
      solve_by_inversion.
    +
      destruct_conjs.
      solve_by_inversion.
  -
    repeat ff.
    +
      destruct_conjs.
      ff.
      econstructor.
      eauto.
    +
      destruct_conjs.
      solve_by_inversion.
Defined.
    
Lemma build_app_some : forall e a_st,
    evMapped e a_st ->
    (*Ev_Shape e -> *)
    exists o, build_app_comp_ev e a_st = (Some o, a_st).
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros.
  -
    repeat ff; eauto.
    (*
    destruct ec;
      try (cbn; df; eauto; tauto). 
    +
      evShapeFacts.
    +
      cbn.
      evShapeFacts.
     *)
    
  -
    cbn.
    evMappedFacts.
    ff.
    subst'.
    df.
    edestruct IHe.
    eassumption.
    subst'.
    df.
    eauto.
  -
    cbn.
    evMappedFacts.
    df.
    subst'.
    df.
    edestruct IHe.
    eassumption.
    subst'.
    df.
    eauto.
  -
    cbn.
    evMappedFacts.
    df.
    
    edestruct IHe.
    eassumption.
    subst'.
    df.
    eauto.
Defined.

Lemma same_ev_shape: forall e et a_st ecomp new_vmst ec_res,
    Ev_Shape e et -> 
    build_app_comp_ev e a_st = (Some ecomp, a_st) ->
    runSt ecomp empty_vmst  = (Some ec_res, new_vmst) ->
    Ev_Shape ec_res et.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros.
  -
    repeat ff.
  -
    evShapeFacts.
    unfold empty_vmst in *.
    repeat ff.
    econstructor.
    eauto.
  -
    evShapeFacts.
    repeat ff.
    econstructor.
    eauto.
  -
    evShapeFacts.
    repeat ff.
    econstructor.
    eauto.  
Defined.

(*
Lemma trace_cumul : forall  t e a_st a_st' v tr tr' p n n' o o' e' o0,
    build_app_comp t p a_st = (Some v, a_st') ->
    v    {| st_ev := e;  st_trace := tr;  st_pl := n;  st_store := o |} =
    (Some o0, {| st_ev := e'; st_trace := tr'; st_pl := n'; st_store := o'|}) ->
    exists tr'', tr' = tr ++ tr''.
Proof.
  induction t; intros.
  -
    destruct a.
    +
      df.
      exists [].
      rewrite app_nil_r.
      eauto.
    +
      
      df.
      doit.
      unfold extractUev in *.
   
      dosome_eq' hi.
      df.
      eexists.
      reflexivity.
    +
      df.
      doit.
      unfold extractSig in *.
      dosome_eq' hi.
      df.
      eexists.
      reflexivity.
  -
    df.
    do_ba_st_const.
    eauto.
  -
    df.
    do_ba_st_const.
    destruct t2.
    +
      destruct a.
      ++
        doit.
        amsts.
        edestruct IHt1.
        eassumption.
        eassumption.
        subst.
        edestruct IHt2.
        eassumption.
        eassumption.
        subst.
        rewrite <- app_assoc.
        eexists.
        eauto.
      ++
        doit.
        amsts.
        edestruct IHt1.
        eassumption.
        eassumption.
        subst.
        edestruct IHt2.
        eassumption.
        eassumption.
        subst.
        rewrite <- app_assoc.
        eexists.
        eauto.
      ++
        doit.
        doex.
        dothat.

        edestruct IHt1.
        eassumption.
        eassumption.
        subst.
        eexists.
        rewrite app_assoc.
        reflexivity.
    +
      doit.
      amsts.
      edestruct IHt1.
      eassumption.
      eassumption.
      subst.
      edestruct IHt2.
      eassumption.
      eassumption.
      subst.
      rewrite <- app_assoc.
      eexists.
      eauto.
    +
      doit.
      amsts.
      edestruct IHt1.
      eassumption.
      eassumption.
      subst.
      edestruct IHt2.
      eassumption.
      eassumption.
      subst.
      rewrite <- app_assoc.
      eexists.
      eauto.
Defined.

Ltac do_cumul2 :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _),

     H': ?v2 {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr2'; st_pl := _; st_store := _ |}),
    H'2: build_app_comp _ _ _ = (Some ?v2, _) |- _] =>

      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H]) ;
      assert (exists tr'' : list Ev, tr2' = tr2 ++ tr'')by (eapply trace_cumul; [apply H'2 | apply H'])
    end.


Ltac do_cumul4 :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _),
             
     H'': ?v {| st_ev := _; st_trace := ?tr3; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr3'; st_pl := _; st_store := _ |}),
     H''': ?v2 {| st_ev := _; st_trace := ?tr31; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr31'; st_pl := _; st_store := _ |}),

     H': ?v2 {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr2'; st_pl := _; st_store := _ |}),
    H'2: build_app_comp _ _ _ = (Some ?v2, _) |- _] =>

      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H]) ;
      assert (exists tr'' : list Ev, tr2' = tr2 ++ tr'')by (eapply trace_cumul; [apply H'2 | apply H']);
      assert (exists tr'' : list Ev, tr3' = tr3 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H'']) ;
      assert (exists tr'' : list Ev, tr31' = tr31 ++ tr'')by (eapply trace_cumul; [apply H'2 | apply H'''])
    end.

Ltac do_cumul2' :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _),
     H': ?v {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
           (_, {| st_ev := _; st_trace := ?tr2'; st_pl := _; st_store := _ |}) |- _] =>

      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H]) ;
      assert (exists tr'' : list Ev, tr2' = tr2 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H'])
    end.

Ltac do_cumul1 :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := ?tr1; st_pl := _; st_store := _ |} =
         (_, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _) |- _] =>

      assert (exists tr'' : list Ev, tr1' = tr1 ++ tr'')by (eapply trace_cumul; [apply H2 | apply H])
    end.

Ltac do_cumul := first [do_cumul4 | do_cumul2 | do_cumul2' | do_cumul1]; destruct_conjs.

Lemma dood : forall t vm_st vm_st' e e'' e' p a_st x0 x1 new_vmst new_vmst',
    build_comp t vm_st = (Some tt, vm_st') ->
    e = st_ev vm_st ->
    e' = st_ev vm_st' ->
    build_app_comp t p a_st = (Some x0, a_st) ->
    x0 new_vmst = (Some x1, new_vmst') ->
    e' = st_ev new_vmst ->  (* repeated e' eqality NOT a typo here *)
    e'' = st_ev new_vmst' ->
    e = e''.
Proof.
  induction t; intros.
  -
    destruct a.
    +
      subst.
      amsts.
      df.
      reflexivity.
    +
      subst.
      amsts.
      df.
      dosome.
      reflexivity.
    +
      subst.
      amsts.
      df.
      dosome.
      reflexivity.
  -
    subst.
    amsts.
    df.
    dohtac.
    df.
    eapply IHt.
    apply build_comp_at.
    reflexivity.
    reflexivity.
    eassumption.
    eassumption.
    tauto.
    tauto.
  -
    subst.
    amsts.
    df.    
    dosome. 
    destruct t2.
    +
      destruct a eqn:aeq.
      ++
        doit.
        cbn in Heqp2.
        doex.
        amsts.
        cbn in Heqp1.
        doit.
        eauto.
      ++
        clear IHt2.
        df.
        dosome.
        haaa.
      ++
        clear IHt2.
        df.
        dosome.
        haaa.
    +
      doit.

      amsts.
      do_ba_st_const.
      do_pl_immut.

      assert (st_ev3 = st_ev1).
      eapply IHt2.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.
      subst.

      eapply IHt1.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.
    +
      doit.

      amsts.
      do_ba_st_const.
      do_pl_immut.

      assert (st_ev3 = st_ev1).
      eapply IHt2.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.
      subst.

      eapply IHt1.
      eassumption.
      tauto.
      tauto.
      eassumption.
      eassumption.
      tauto.
      tauto.
      Unshelve.
      eauto.
      eauto.
      exact (aasp (0,0) (ASPC 1 [])).
      exact mtc.
      eauto.
      eauto.
      exact (aasp (0,0) (ASPC 1 [])).
      exact mtc.
      eauto.
      eauto.
Defined.
*)

Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args, evidenceEvent (umeas n p i args)
(*| sev: forall n p, evidenceEvent (sign n p) *)
(*
| hev: forall n p, evidenceEvent (hash n p)*). 


Definition measEvent (t:AnnoTerm) (p:Plc) (ev:Ev) : Prop :=
  events t p ev /\ evidenceEvent ev.

Inductive appEvent : Ev -> AM_St -> Ev -> Prop :=
| aeu : forall p p' i i' n n' m args st,
    m = st_aspmap st ->
    bound_to m (p,i) i' ->
    appEvent (umeas n p i args) st (umeas n' p' i' ([n] ++ args)).
(*| asu : forall p q i' n n' m  args st,
    m = st_sigmap st ->
    bound_to m p i' ->
    appEvent (sign n p) st (umeas n' q i' ([n] ++ args)). *)

Ltac measEventFacts :=
  match goal with
  | [H: measEvent _ _ _ |- _] => invc H
  end.

Ltac evEventFacts :=
  match goal with
  | [H: evidenceEvent _ |- _] => invc H
  end.

Ltac invEvents :=
  match goal with
  | [H: events _ _ _  |- _] => invc H
  end.

Lemma mt_sub_all: forall e,
    EvSub mtc e.
Proof.
  induction e; intros;
    (econstructor; eauto; tauto).
Defined.
    

Print EvSub.

Ltac do_evsub :=
  match goal with
  | [H: EvSub _ (?C) |- _] => invc H
  end.
    

Lemma evSub_trans: forall e' e e'',
  EvSub e e' ->
  EvSub e' e'' ->
  EvSub e e''.
Proof.
  induction e''; intros;
    do_evsub;
    try solve_by_inversion;
    try (econstructor; eauto).
Defined.

Lemma evAccum: forall t vmst vmst' e e',
  well_formed_r t -> 
  copland_compile t vmst = (Some tt, vmst') ->
  e = st_ev vmst ->
  e' = st_ev vmst' ->
  EvSub e e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; repeat ff;
      try (repeat econstructor; eauto; tauto).
  -
    do_wf_pieces.
    repeat ff.
    eapply IHt.
    eassumption.
    eapply copland_compile_at.
    eassumption.
    tauto.
    tauto.
  -
    do_wf_pieces.
    vmsts.
    edestruct alseq_decomp_gen.
    eassumption.
    eassumption.
    destruct_conjs.

    assert (EvSub st_ev0 x) by eauto.
    
    assert (EvSub x st_ev) by eauto.
    eapply evSub_trans; eauto.
Defined.

Lemma evMappedSome: forall e1 e2 a_st,
  EvSub e1 e2 ->
  evMapped e2 a_st ->
  evMapped e1 a_st.
Proof.
  induction e2; intros.
  -
    invc H.
    econstructor.
  -
    invc H0.
    destruct_conjs.
    invc H.
    +
      econstructor.
      tauto.
      eassumption.
      eauto.
    +
      eauto.
  -
    invc H0.
    destruct_conjs.
    invc H.
    +
      econstructor.
      tauto.
      eassumption.
      eauto.
    +
      eauto.
  -
    invc H0.
    destruct_conjs.
    invc H.
    +
      econstructor.
      tauto.
    +
      eauto.
Defined.

Lemma subSome: forall e1 e2 x a_st,
  EvSub e1 e2 ->
  build_app_comp_ev e2 a_st = (Some x, a_st) ->
  exists x', build_app_comp_ev e1 a_st = (Some x', a_st).
Proof.
  intros.
  assert (evMapped e1 a_st).
  {
    eapply evMappedSome.
    eassumption.
    eapply build_app_some'; eauto.
  }
  eapply build_app_some; eauto.
Defined.

Lemma app_always_some: forall e a_st x0 vmst,
    build_app_comp_ev e a_st = (Some x0, a_st) ->
    exists app_ev vmst',
      x0 vmst = (Some app_ev, vmst').
Proof.
  induction e; intros.
  -
    ff.
    eauto.
  -
    ff.
    ff.
    edestruct IHe.
    eassumption.
    destruct_conjs.
    rewrite H0 in *.
    
    ff.
    eauto.
  -
    ff.
    ff.
    edestruct IHe.
    eassumption.
    destruct_conjs.
    rewrite H0 in *.
    
    ff.
    eauto.
  -
    ff.
    ff.
    edestruct IHe.
    eassumption.
    destruct_conjs.
    rewrite H0 in *.
    
    ff.
    eauto.
Defined.

Lemma app_lseq_decomp': forall (*t1*) e1 e2 (*vmst vmst'*) a_st x
                         app_res init_vmst new_vmst,
    (*copland_compile t1 vmst = (Some tt, vmst') ->
    e1 = st_ev vmst' -> *)
    EvSub e1 e2 ->
    (*
    copland_compile t2 vmst' = (Some tt, vmst'') ->
    e2 = st_ev vmst'' -> *)
    build_app_comp_ev e2 a_st = (Some x, a_st) ->
    runSt x init_vmst = (Some app_res, new_vmst) ->


    
    exists x' app_ev1 new_vmst1,
      build_app_comp_ev e1 a_st = (Some x', a_st) /\
      runSt x' init_vmst = (Some app_ev1, new_vmst1) /\

      (*
      exists x'' app_ev2 new_vmst2,
        build_app_comp_ev e2 a_st = (Some x'', a_st) /\
        runSt x'' init_vmst = (Some app_ev2, new_vmst2) /\ *)
        (forall ev1, In ev1 (st_trace new_vmst1) -> In ev1 (st_trace new_vmst)) (*/\
        (forall ev1, In ev1 (st_trace new_vmst2) -> In ev1 (st_trace new_vmst)) *) .


Proof.
  intros.
  edestruct subSome.
  eassumption.
  eassumption.
  exists x0.

  edestruct app_always_some.
  apply H2.
  destruct_conjs.
  exists x1.
  exists H3.
  split.
  eassumption.
  split.
  eassumption.
  subst.
  vmsts.
  amsts.
  ff.
  generalizeEverythingElse e2.
  induction e2; intros.
  -
    invc H.
    ff.
    eassumption.
  -
    invc H.
    +
      ff.
      ff.
      ff.
      eassumption.
    +
      ff.
      ff.
      ff.
      assert (forall ev1:Ev, In ev1 st_trace -> In ev1 st_trace2).
      {
        eauto.
      }
      pose (H ev1).
      concludes.
      apply in_or_app.
      eauto.
  -
    invc H.
    +
      ff.
      ff.
      ff.
      eassumption.
    +
      ff.
      ff.
      ff.
      assert (forall ev1:Ev, In ev1 st_trace -> In ev1 st_trace2).
      {
        eauto.
      }
      pose (H ev1).
      concludes.
      apply in_or_app.
      eauto.
  -
    invc H.
    +
      ff.
      ff.
      ff.
      eassumption.
    +
      ff.
      ff.
      ff.
      assert (forall ev1:Ev, In ev1 st_trace -> In ev1 st_trace0).
      {
        eauto.
      }
      pose (H ev1).
      concludes.
      eassumption.
Defined.

Lemma app_lseq_decomp: forall t1 t2 e1 e2 vmst vmst' vmst'' a_st x
                         app_res init_vmst new_vmst,
    well_formed_r t1 ->
    well_formed_r t2 ->
    copland_compile t1 vmst = (Some tt, vmst') ->
    e1 = st_ev vmst' ->
    copland_compile t2 vmst' = (Some tt, vmst'') ->
    e2 = st_ev vmst'' ->
    build_app_comp_ev e2 a_st = (Some x, a_st) ->
    runSt x init_vmst = (Some app_res, new_vmst) ->


    
    exists x' app_ev1 new_vmst1,
      build_app_comp_ev e1 a_st = (Some x', a_st) /\
      runSt x' init_vmst = (Some app_ev1, new_vmst1) /\

      (*
      exists x'' app_ev2 new_vmst2,
        build_app_comp_ev e2 a_st = (Some x'', a_st) /\
        runSt x'' init_vmst = (Some app_ev2, new_vmst2) /\ *)
        (forall ev1, In ev1 (st_trace new_vmst1) -> In ev1 (st_trace new_vmst)) (*/\
        (forall ev1, In ev1 (st_trace new_vmst2) -> In ev1 (st_trace new_vmst)) *) .


Proof.
  intros.
  eapply app_lseq_decomp'.
  (*apply H1.
  eassumption. *)
  eapply evAccum.
  apply H0.
  eassumption.
  eassumption.
  tauto.
  subst.
  eassumption.
  eassumption.
Defined.

Lemma appraisal_correct : forall t vmst vmst' p e_res init_vmst new_vmst a_st x app_res (*tr_app*) ev,
    well_formed_r t ->
    copland_compile t vmst = (Some tt, vmst') ->
    p = st_pl vmst ->
    (*e = st_ev vmst -> *)
    e_res = st_ev vmst' ->
    (*e_res = st_ev new_vmst -> *)

    (*
    Ev_Shape e etype ->
    et = Term.eval (unanno t) p etype -> 
     *)
    build_app_comp_ev e_res a_st = (Some x, a_st) ->
    runSt x init_vmst = (Some app_res, new_vmst) ->
    (*tr_app = st_trace new_vmst -> *)
    measEvent t p ev ->
    exists ev', In ev' (st_trace new_vmst) /\ appEvent ev a_st ev'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    measEventFacts.
    evEventFacts.
    invEvents.
    unfold empty_vmst in *.
    amsts.
    vmsts.
    repeat ff.
    eexists.
    split.
    eapply in_or_app.
    right.
    econstructor.
    tauto.
    econstructor.
    tauto.
    econstructor.
    eassumption.
  -
    measEventFacts.
    evEventFacts.
    invEvents.
    unfold empty_vmst in *.
    amsts.
    vmsts.
    ff.
    try dohtac.
    ff.
    Print dohtac.
    Check PeanoNat.Nat.eqb_eq.
    do_wf_pieces.
    edestruct IHt.
    eassumption.
    eapply copland_compile_at.
    eassumption.
    tauto.
    tauto.
    eassumption.
    eassumption.
    simpl.
    econstructor.
    eassumption.
    econstructor.
    simpl in *.
    eauto.

  -
    do_wf_pieces.
    vmsts.
    Check alseq_decomp_gen.
    edestruct alseq_decomp_gen. (*with (r:=r) (t1':=t1) (t2':=t2) (e:=st_ev2) (e'':=st_ev1) (p:=st_pl2) (p'':=st_pl1) (init_tr:=st_trace2) (tr:=st_trace1). *)
    eassumption.
    eassumption.

    destruct_conjs.
    
    
    



    edestruct app_lseq_decomp. (*with
        (t1:= t1) (t2:=t2) (e1:=x0) (e2:=st_ev1)
        (vmst:={| st_ev := st_ev2; st_trace := st_trace2; st_pl := st_pl2 |})
        (vmst':= {| st_ev := x0; st_trace := H6; st_pl := H7 |})
        (vmst'':={| st_ev := st_ev1; st_trace := st_trace1; st_pl := st_pl1 |})
        (a_st:=a_st)
        (x:=x)
        (app_res:=app_res)
        (init_vmst:={| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0 |})
        (new_vmst:={| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl |}). *)
        
                                  

    
    apply H6.
    apply H7.

    eassumption.
    tauto.
    simpl in *.
    subst.
    eassumption.
    tauto.
    eassumption.
    eassumption.

  
    
    destruct_conjs.

    vmsts.
    amsts.
    simpl in *.

    do_wf_pieces.

    Print measEventFacts.

    inversion H5; clear H5.
    inversion H19; clear H19.

    (*
    measEventFacts.
    evEventFacts. *)

    inversion H18; clear H18.

    (*
    invEvents. *)
    +
      
      vmsts.
      assert (st_pl2 = p) by congruence.
      subst.
      (*
      rewrite <- H21 in H27. clear H21.
      rewrite <- H5 in H27; clear H5. *)
      (*
      repeat ff. *)

      edestruct IHt1.
      eassumption.
      eassumption.
      Focus 3.
      apply H14.
      tauto.
      tauto.
      eassumption.
      simpl.
      
      econstructor.
      eassumption.
      econstructor.

      
      destruct_conjs.
      simpl in *.

      exists x2.
      split;
      eauto.

    +
      vmsts.
      subst.
      Require Import Helpers_VmSemantics.
      repeat do_pl_immut.
      subst.

      (*
      
      assert (H7 = p).
      {
        subst.
        Require Import Helpers_VmSemantics.

        repeat do_pl_immut.
        subst.
        tauto.
      } *)
      
      edestruct IHt2.
      eassumption.
      eassumption.
      Focus 3.
      apply H3.
      tauto.
      tauto.
      eassumption.
      simpl.
      econstructor.
      subst.
      eassumption.
      (*
      rewrite H21.
      eassumption.
      rewrite <- H5. *)
      econstructor.
      destruct_conjs.
      simpl in *.
      exists x2.
      split; eauto.
Defined.


     
    
    
    
HERE
  







Lemma appraisal_correct : forall t vmst vmst' p e_res e new_vmst a_st et x app_res tr_app ev,
    build_comp t vmst = (Some tt, vmst') ->
    p = st_pl vmst ->
    e = st_ev vmst ->
    e_res = st_ev vmst' ->
    (*e_res = st_ev new_vmst -> *)

    (*
    Ev_Shape e etype ->
    et = Term.eval (unanno t) p etype -> 
     *)
    build_app_comp_ev et e_res a_st = (Some x, a_st) ->
    runSt empty_vmst x = (Some app_res, new_vmst) ->
    tr_app = st_trace new_vmst ->
    measEvent t p ev ->
    exists ev', In ev' tr_app /\ appEvent ev a_st ev'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    measEventFacts.
    evEventFacts.
    invEvents.
    unfold empty_vmst in *.
    amsts.
    vmsts.
    repeat ff.
    
    assert (exists ix p et' i', et = (uu ix args p et') /\
           map_get (st_aspmap a_st) (p,ix) = Some i' ). (*/\ Ev_Shape st_ev1 et'). *)
    {
      admit.
    }
    destruct_conjs.
    subst'.
    
    repeat ff.
    exists (umeas 0 st_pl H2 (n :: args)).
    split.
    eapply in_or_app.
    right.
    econstructor.
    tauto.
    econstructor.
    reflexivity.
    econstructor.
    eassumption.
  -
    measEventFacts.
    evEventFacts.
    invEvents.
    unfold empty_vmst in *.
    amsts.
    vmsts.
    repeat ff.

    edestruct IHt.
    eapply build_comp_at.
    tauto.
    tauto.
    tauto.
    simpl.
    eassumption.
    tauto.
    simpl.
    eassumption.
    eassumption.
    tauto.
    simpl.
    econstructor.
    eassumption.
    econstructor.
    eexists; eauto.

    dohtac.
    solve_by_inversion.
  -
    unfold empty_vmst in *.
    amsts.
    vmsts.
    measEventFacts.
    evEventFacts.
    invEvents.
    +
      repeat ff.
      vmsts.
      (*
      assert (Ev_Shape st_ev2 (eval (unanno t1) st_pl1 etype)).
      {
        admit.
      } *)
      do_pl_immut.
      do_pl_immut.
      subst.

      

      (*
      assert (Ev_Shape st_ev2 (eval (unanno t1) st_pl0 etype)).
      {
        eapply multi_ev_eval.
        admit.
        eassumption.
        eassumption.
        tauto.
      }

      edestruct build_app_some.
      admit.
      apply H0. *)

      Lemma evcomp_decomp: forall t1 t2 st_pl0 etype a_st x st_ev0 st_ev2,
        build_app_comp_ev
          (eval (unanno t2) st_pl0 (eval (unanno t1) st_pl0 etype)) st_ev0 a_st = (Some x, a_st) ->
        exists x',
          build_app_comp_ev (eval (unanno t1) st_pl0 etype) st_ev2 a_st = (Some x', a_st).
      Proof.
      Admitted.

      edestruct evcomp_decomp.
      eassumption.
      
      
      eapply IHt1.
      eassumption.
      tauto.
      tauto.
      tauto.
      simpl.
      eassumption.
      tauto.
      simpl.



      


      
      eassumption.
      Check build_app_some.
      edestruct build_app_some.
      admit.
      admit.
      simpl.
      econstructor.
      eassumption.
      econstructor.
    +
      repeat ff.
      vmsts.
      assert (Ev_Shape st_ev2 (eval (unanno t1) st_pl1 etype)).
      {
        admit.
      }
      do_pl_immut.
      do_pl_immut.
      subst.
      
      
      eapply IHt2.
      eassumption.
      tauto.
      tauto.
      tauto.
      simpl.
      eassumption.
      tauto.
      simpl.
      eassumption.
      eassumption.
      simpl.
      tauto.
      simpl.
      econstructor.
      eassumption.
      econstructor.
      Unshelve.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
    






  

Lemma appraisal_correct : forall t vmst vmst' p e_res new_vmst new_vmst' a_st x f tr_app ev,
    build_comp t vmst = (Some tt, vmst') ->
    p = st_pl vmst ->
    e_res = st_ev vmst' ->
    e_res = st_ev new_vmst ->
    build_app_comp t p a_st = (Some x, a_st) -> (* x : VM (EvidenceC -> EvidenceC) *)
    runSt new_vmst x = (Some f, new_vmst') ->
    tr_app = st_trace new_vmst' ->
    measEvent t p ev ->
    exists ev', In ev' tr_app /\ appEvent ev a_st ev'.
Proof.
  induction t; intros.
  -
    destruct a.
    +
      measEventFacts.
      evEventFacts;
        try
      solve_by_inversion.
    +
      measEventFacts.
      evEventFacts;
        try solve_by_inversion.
      invEvents.
      destruct r.
      simpl.
          
      amsts.
      dothat.
      subst.
      df.
      doit.
      doex.
      df.

      exists (umeas n2 st_pl n1 (n2 :: args)).
      split.
      ++
        eapply in_or_app.
        right.
        econstructor. reflexivity.
      ++
        assert (n2::args = [n2] ++ args).
        reflexivity.
        rewrite H.
        econstructor.
        reflexivity.
        econstructor.
        eassumption.
    +
      measEventFacts.
      evEventFacts;
        try solve_by_inversion.

            invEvents.
      destruct r.
      simpl.
          
      amsts.
      dothat.
      subst.
      df.
      doit.
      doex.
      df.
      exists (umeas n2 st_pl n1 [n2 ; encodeEv st_ev]).

      (*

      exists (umeas n2 st_pl n1 (n2 :: args)). *)
      split.
      ++
        eapply in_or_app.
        right.
        econstructor. reflexivity.
      ++
        econstructor.
        reflexivity.
        econstructor.
        eassumption.
      
  -
    amsts.
    subst.
    df.
    dohtac.
    df.

    measEventFacts.

    (*
    evEventFacts;
      try solve_by_inversion. *)
    invEvents;
      try solve_by_inversion.

    edestruct IHt with
        (vmst:=
           {| st_ev := st_ev3; st_trace := []; st_pl := n; st_store := [] |})
        (new_vmst:=
           {| st_ev := toRemote (unanno t) st_ev3;
              st_trace := st_trace0;
              st_pl := st_pl0;
              st_store := st_store0 |}).
    
    apply build_comp_at.
    reflexivity.
    reflexivity.
    tauto.
    eassumption.
    eassumption.
    reflexivity.
    simpl.
    econstructor.
    eassumption.
    eassumption.

    simpl in H.
    

    eexists x0.
    eassumption.

  - (* alseq case *)

    (*
    df.
    dosome_eq hi.
    do_pair.
    amsts.
    df.
    subst.
    destruct t2.
    +
      destruct a eqn:aeq.
      ++
        doit.
        amsts.
        doex.
        
        simpl in Heqp.
        doex. 
        measEventFacts.
        (*
        evEventFacts; try solve_by_inversion. *)
        invEvents; try solve_by_inversion.
        +++
          do_pl_immut.
          cbn in Heqp1.
          do_pair.

          eapply IHt1 with
              (vmst:= {| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
              (new_vmst := {| st_ev := st_ev2; st_trace := st_trace4; st_pl := st_pl4; st_store := st_store4 |}).
          eassumption.
          tauto.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          econstructor.
          eassumption.
          eassumption.
        +++
          invc H7.
          solve_by_inversion.
      ++

        doit.
        amsts.
        measEventFacts.
        (* evEventFacts; try solve_by_inversion. *)
        invEvents.
        +++
          do_pl_immut.
          do_ba_st_const.
          df.
          dosome.
          haaa.
          
          eapply IHt1 with
              
              
              
              (vmst:={| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
              (new_vmst:= {|
                  st_ev := st_ev2;
                  st_trace := st_trace1 ++ [umeas n2 st_pl4 n4 (n2 :: l)];
                  st_pl := st_pl4;
                  st_store := st_store4 |}).
               
              
          eassumption.
          tauto.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          econstructor.
          eassumption.
          eassumption.
          
          
        +++
          do_pl_immut.
          do_ba_st_const.
          invEvents.
          
          edestruct IHt2 with
              (vmst := {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl2; st_store := st_store |})
              (new_vmst := {| st_ev := st_ev1; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}).
                    


          (*with
              (vmst:={| st_ev := st_ev; st_trace := st_trace; st_pl := p; st_store := st_store |})
              (new_vmst:={| st_ev := st_ev1; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}). *)
          eassumption.
          tauto.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          econstructor.
          econstructor.
          reflexivity.
          econstructor.
          simpl in H0.
          destruct_conjs.
          destruct r.
          simpl in H1.
          simpl.
          exists x.
          do_cumul.
          subst.
          split.
          apply in_or_app.
          eauto.
          eauto.
      ++
        doit.
        doex.
        dothat.
        
        amsts.
        do_ba_st_const.
        do_pl_immut.
        measEventFacts.
        (*evEventFacts; try solve_by_inversion. *)
        invEvents.
        +++
          clear IHt2.
          df.
          
          eapply IHt1 with
              (vmst:= {| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
              (new_vmst:= {| st_ev := e; st_trace := st_trace4 ++ [umeas n st_pl4 n1 [n2; encodeEv e]]; st_pl := st_pl4; st_store := st_store4 |}).

            (*with
              (vmst:=
                 {| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
              (new_vmst:= {|
                  st_ev := e;
                  st_trace := st_trace4 ++ [umeas n st_pl4 n1 [encodeEv e; n2]];
                  st_pl := st_pl4;
                  st_store := st_store4 |}).
*)
          eassumption.
          tauto.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          econstructor.
          eassumption.
          eassumption.
          
        +++
          invEvents.
          clear IHt1.
          repeat break_let.
          
          
          eapply IHt2. with
              (vmst:= {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl2; st_store := st_store |})
              (new_vmst:= {| st_ev := e; st_trace := st_trace4 ++ [umeas n st_pl4 n1 [n2; encodeEv e]]; st_pl := st_pl4; st_store := st_store4 |} )
              (vmst':= {| st_ev := ggc n2 e; st_trace := st_trace2; st_pl := st_pl2; st_store := st_store2 |}).
          eassumption.
          reflexivity.
          reflexivity.
          break_let.
          reflexivity.
          tauto.
          tauto.
          tauto.
          

  (*with
              (vmst:= {| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
              (new_vmst:= {| st_ev := e; st_trace := st_trace4 ++ [umeas n st_pl4 n1 [n2; encodeEv e]]; st_pl := st_pl4; st_store := st_store4 |}). *)

            (*with
              (vmst:=
                 {| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
              (new_vmst:= {|
                  st_ev := e;
                  st_trace := st_trace4 ++ [umeas n st_pl4 n1 [encodeEv e; n2]];
                  st_pl := st_pl4;
                  st_store := st_store4 |}).
*)
          eassumption.
          tauto.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          econstructor.
          eassumption.
          eassumption.
          

    +
      doit.
      amsts.
      measEventFacts.
      evEventFacts.
      invEvents.
      ++
        clear IHt2.
        df.
        dohtac.
        df.
        do_pl_immut.
        do_ba_st_const.
        eapply IHt1 with (vmst:={| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |}) (new_vmst:={| st_ev := st_ev2; st_trace := st_trace4; st_pl := st_pl4; st_store := st_store4 |}).
        eassumption.
        tauto.
        tauto.

        simpl.
        assert (st_ev4 = st_ev2).
        { 
          eapply dood with (vm_st0 := {| st_ev := st_ev4; st_trace := []; st_pl := n1; st_store := [] |}).
          apply build_comp_at.
          tauto.
          tauto.
          apply Heqp.
          eassumption.
          tauto.
          tauto.
        }
        subst.
        tauto.
        eassumption.
        eassumption.
        tauto.
        econstructor.
        eassumption.
        econstructor.
      ++
        do_pl_immut.
        do_ba_st_const.
        cbn in Heqp1.
        repeat break_let.
        df.
        dohtac.
        dosome.
        do_pl_immut.
        do_ba_st_const.
        amsts.
        df.
        invEvents.
        edestruct IHt2 with (vmst:={| st_ev := st_ev; st_trace := []; st_pl := n1; st_store := [] |}) (new_vmst:={| st_ev := toRemote (unanno t2) st_ev; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}).
        tauto.
        tauto.

        tauto.
        tauto.
        eassumption.
        eassumption.
        tauto.
        econstructor.
        apply evtsatt.
        eassumption.
        econstructor.
   
        destruct_conjs.
        simpl in H1.
        do_cumul.
        subst.

        exists x.
        split.
        +++
          eapply in_or_app.
          eauto.
        +++
          eauto.
    +
      doit.
      amsts.
      measEventFacts.
      evEventFacts.
      invEvents.
      ++
        clear IHt2.
        do_pl_immut.
        do_ba_st_const.
        eapply IHt1 with
            (vmst:={| st_ev := st_ev3; st_trace := st_trace3; st_pl := st_pl2; st_store := st_store3 |})
            (new_vmst:={| st_ev := st_ev2; st_trace := st_trace4; st_pl := st_pl4; st_store := st_store4 |}).
        eassumption.
        tauto.
        tauto.

        simpl.
        assert (st_ev = st_ev2).
        {
          eapply dood.
          apply Heqp1.
          tauto.
          tauto.
          eassumption.
          eassumption.
          tauto.
          tauto.
        }
        subst.
        tauto.
        eassumption.
        eassumption.
        tauto.
        econstructor.
        eassumption.
        econstructor.
      ++
        do_pl_immut.
        do_ba_st_const.
        
        edestruct IHt2 with
            (vmst:={| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl2; st_store := st_store |})
            (new_vmst:={| st_ev := st_ev1; st_trace := st_trace1; st_pl := st_pl1; st_store := st_store1 |}).
        eassumption.
        tauto.
        tauto.
        tauto.
        eassumption.
        eassumption.
        tauto.
        econstructor.
        eassumption.
        econstructor.
        destruct_conjs.

        do_cumul.
        subst.
        eexists.
        split.
        +++
          apply in_or_app.
          eauto.
        +++
          eauto.
          
          Unshelve.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          exact (aasp (0,0) (ASPC 1 [])).
          exact mtc.
          eauto.
          eauto.
          Defined.
     *)
Abort.

HERE.










(*
(***** Potentially-failing appraisal functions ******) 


Definition fromOpt{A:Type} (o:option A) (a:A) : A :=
  match o with
  | Some t => t
  | None => a
  end.

Definition run_app_comp (t:AnnoTerm) (p:Plc) (a_st:AM_St) (e_in:EvidenceC) : (EvidenceC -> EvidenceC) :=
  let acomp := build_app_comp t p in (* AM (VM (EvidenceC -> EvidenceC)) *)
  let vcomp_opt := runSt a_st acomp in (* (option (VM (EvidenceC -> EvidenceC)) * AM_St) *)
  let vcomp := fromOpt (fst vcomp_opt) (ret (fun _ => mtc)) in (* (VM (EvidenceC -> EvidenceC)) *)
  let vres_opt := runSt (mk_st e_in [] 0 []) vcomp in (* (option (EvidenceC -> EvidenceC) * VM_St) *)
  fromOpt (fst vres_opt) ((fun _ => mtc)).

Definition run_app_comp' (t:AnnoTerm) (p:Plc) (st:AM_St) (e_in:EvidenceC) : ((option (EvidenceC -> EvidenceC)) * vm_st) :=
  let acomp := build_app_comp t p in (* AM (VM (EvidenceC -> EvidenceC)) *)
  let vcomp_opt := runSt st acomp in (* (option (VM (EvidenceC -> EvidenceC)) * AM_St) *)
  let vcomp := fromOpt (fst vcomp_opt) (ret (fun _ => mtc)) in (* (VM (EvidenceC -> EvidenceC)) *)
  let vres_opt := runSt (mk_st e_in [] 0 []) vcomp in
  vres_opt.


Definition at1 := (asp (ASPC 11 [])).
(*Definition at2 := (asp (ASPC 22 [])). *)
Definition term := lseq at1 (asp SIG).
Definition aterm := annotated term.
Compute aterm.

Check run_vm.

Definition aterm_vm_st := run_vm aterm empty_vmst.
Compute aterm_vm_st.
Definition aterm_ev := st_ev aterm_vm_st.
Compute aterm_ev.

Definition ast :=
  mkAM_St [] 0 [((0,11),34); ((0,22),45)] [(0,42)].

Compute run_app_comp' aterm 0 ast aterm_ev.

Compute run_app_comp aterm 0 ast aterm_ev.
*)





(*
Definition run_app_comp (t:AnnoTerm) (p:Plc) (a_st:AM_St) (e_in:EvidenceC) : (EvidenceC -> EvidenceC) :=
  let acomp := build_app_comp t p in (* AM (VM (EvidenceC -> EvidenceC)) *)
  let vcomp_opt := runSt a_st acomp in (* (option (VM (EvidenceC -> EvidenceC)) * AM_St) *)
  let vcomp := fromOpt (fst vcomp_opt) (ret (fun _ => mtc)) in (* (VM (EvidenceC -> EvidenceC)) *)
  let vres_opt := runSt (mk_st e_in [] 0 []) vcomp in (* (option (EvidenceC -> EvidenceC) * VM_St) *)
  fromOpt (fst vres_opt) ((fun _ => mtc)).

Definition run_app_comp' (t:AnnoTerm) (p:Plc) (st:AM_St) (e_in:EvidenceC) : ((option (EvidenceC -> EvidenceC)) * vm_st) :=
  let acomp := build_app_comp t p in (* AM (VM (EvidenceC -> EvidenceC)) *)
  let vcomp_opt := runSt st acomp in (* (option (VM (EvidenceC -> EvidenceC)) * AM_St) *)
  let vcomp := fromOpt (fst vcomp_opt) (ret (fun _ => mtc)) in (* (VM (EvidenceC -> EvidenceC)) *)
  let vres_opt := runSt (mk_st e_in [] 0 []) vcomp in
  vres_opt.
 *)

(*
Lemma measEventAt' : forall t n p q ev,
    measEvent (snd (anno (att n t) q)) p ev ->
    measEvent (snd (anno t (S q))) n ev.
Proof.

  induction t; intros;
    try (
      df;
      measEventFacts;
      evEventFacts;
      invEvents;
      invEvents;
      try (repeat econstructor; eauto; tauto)).
Defined.
*)





(*
(***** Old Proofs, potentially-failing appraisal *****)

Lemma isnil{A:Type} : forall (ls xs : list A),
    ls = ls ++ xs ->
    xs = [].
Proof.
  intros.
  assert (ls = ls ++ []).
  {
    rewrite app_nil_r.
    tauto.
  }
  rewrite H0 in H at 1.
  eapply app_inv_head; eauto.
Defined.

Lemma gogo' : forall t p a a' o_res o_res' v1 e1' p1 p1' o1 o1' e2 e2' tr2 p2 p2' o2 o2' tr1 x0 x1,
    build_app_comp t p a = (Some v1, a') ->
    v1 {| st_ev := e2; st_trace := tr1; st_pl := p1; st_store := o1 |} =
    (Some o_res, {| st_ev := e1'; st_trace := tr1 ++ x1; st_pl := p1'; st_store := o1' |}) ->
    v1 {| st_ev := e2; st_trace := tr2; st_pl := p2; st_store := o2 |} =
    (Some o_res', {| st_ev := e2'; st_trace := tr2 ++ x0; st_pl := p2'; st_store := o2' |}) ->
    x0 = x1.
Proof.
  induction t; intros.
  -
    destruct r; destruct a.
    +
      df. 
      assert (x1 = []) by (eapply isnil; eauto).
      assert (x0 = []) by (eapply isnil; eauto).
      congruence.
    +
      df.
      doit.
      domap.
      doit.
      dothat.
      doex.
      do_inv_head.
      congruence.
    +
      df.
      doit.
      domap.
      doit.
      dothat.
      doex.
      do_inv_head.
      congruence.
  -
    df.
    eauto.
  -
    df.
    destruct r.
    subst.
    destruct t2.
    +
      doit.
      destruct a0.
      ++
        doit.

        cbn in Heqp0.
        repeat break_let.
        doex.
        eauto.
      ++
        doit.
        cbn in Heqp0.
        df.
        doit.
        domap.
        doit.
        doex.
        
        repeat break_let.
        doex.
        doit.
        df.
        doit.
        subst.
        invc Heqe.
        eauto.
        do_cumul.
        assert (x0 = [umeas n4 0 n1 (b :: l)] ++ H0).
        {
          admit.
        }

        assert (x1 = [umeas n4 0 n1 (b :: l)] ++ H1).
        {
          admit.
        }
        assert (H0 = H1).
        {
          admit.
        }
        subst.
        congruence.
      ++
        doit.
        doex.
        dothat.
        subst.
        invc Heqe4.

        do_cumul.
        assert (x0 = [umeas n 0 n3 [encodeEv e; b]] ++ H).
        {
          admit.
        }

        assert (x1 = [umeas n 0 n3 [encodeEv e; b]] ++ H0).
        {
          admit.
        }
        assert (H = H0).
        {
          admit.
        }
        subst.
        congruence.
    +
      doit.
      cbn in Heqp0.
      amsts.
      do_cumul.
      subst.
      assert (x0 = H3 ++ H).
      {
        admit.
      }
      subst.
      assert (x1 = H0 ++ H4).
      {
        admit.
      }
      subst.
      assert (H = H4).
      eapply IHt1.
      eassumption.
      rewrite app_assoc in *.
      eassumption.
      repeat rewrite app_assoc in *.
      assert (st_ev = st_ev0).
      {
        admit.
      }
      subst.
      eassumption.
      subst.
      assert (H3 = H0) by eauto.
      subst.
      reflexivity.
   +
      doit.
      
      (*cbn in Heqp0. *)
      amsts.
      do_cumul.
      subst.
      assert (x0 = H3 ++ H).
      {
        admit.
      }
      subst.
      assert (x1 = H0 ++ H4).
      {
        admit.
      }
      subst.
      assert (H = H4).
      eapply IHt1.
      eassumption.
      rewrite app_assoc in *.
      eassumption.
      repeat rewrite app_assoc in *.
      assert (st_ev = st_ev0).
      {
        admit.
      }
      subst.
      eassumption.
      subst.
      assert (H3 = H0) by eauto.
      subst.
      reflexivity.
      Unshelve.
      eauto.
        
    
    
      
      
      

      
      
      

      
      











(*

  
  assert (Ev_Shape e et).
  eapply gen_ev_shape; eauto.
  generalizeEverythingElse e.

  induction e;
    intros;
    evShapeFacts;
    try
      ( df;
        dosome;
        haaa;
        do_cumul;
        repeat subst'';                                                           
        repeat dof;
        assert (H0 = H1) by ( eapply IHe; eauto);
        congruence);
    try
      ( df;
        dosome;
        repeat break_match; try solve_by_inversion;
        df;
        eauto).
  -
    df.
    assert (x0 = []).
    eapply lista; eauto.
    assert (x1 = []).
    eapply lista; eauto.
    congruence.
  -
    df.
    dosome.
    repeat break_match; try solve_by_inversion.
    vmsts.

    edestruct trace_cumul.
    apply Heqp.
    apply Heqp1.
    subst.

    edestruct trace_cumul.
    apply Heqp.
    apply Heqp3.
    subst.

    assert (x = x2).
    eauto.
    subst.

    edestruct trace_cumul.
    apply Heqp0.
    apply Heqp4.
    rewrite H in *.

    edestruct trace_cumul.
    apply Heqp0.
    apply Heqp2.
    rewrite H0 in *.

    assert (x = x3).
    eauto.
    subst.

    assert (x0 = x2 ++ x3).
    {
      assert ((tr2 ++ x2) ++ x3 = tr2 ++ (x2 ++ x3)).
      {
        rewrite app_assoc.
        reflexivity.
      }
      rewrite H1 in H.
      eapply app_inv_head.
      eassumption.
    }

    assert (x1 = x2 ++ x3).
    {
      assert ((tr1 ++ x2) ++ x3 = tr1 ++ (x2 ++ x3)).
      {
        rewrite app_assoc.
        reflexivity.
      }
      rewrite H2 in H0.
      eapply app_inv_head.
      eassumption.
    }
    congruence.
    
  -
    df.
    dosome.
    repeat break_match; try solve_by_inversion.
    vmsts.

    edestruct trace_cumul.
    apply Heqp.
    apply Heqp1.
    subst.

    edestruct trace_cumul.
    apply Heqp.
    apply Heqp3.
    subst.

    assert (x = x2).
    eauto.
    subst.

    edestruct trace_cumul.
    apply Heqp0.
    apply Heqp4.
    rewrite H in *.

    edestruct trace_cumul.
    apply Heqp0.
    apply Heqp2.
    rewrite H0 in *.

    assert (x = x3).
    eauto.
    subst.

    assert (x0 = x2 ++ x3).
    {
      assert ((tr2 ++ x2) ++ x3 = tr2 ++ (x2 ++ x3)).
      {
        rewrite app_assoc.
        reflexivity.
      }
      rewrite H1 in H.
      eapply app_inv_head.
      eassumption.
    }

    assert (x1 = x2 ++ x3).
    {
      assert ((tr1 ++ x2) ++ x3 = tr1 ++ (x2 ++ x3)).
      {
        rewrite app_assoc.
        reflexivity.
      }
      rewrite H2 in H0.
      eapply app_inv_head.
      eassumption.
    }
    congruence.
Defined.
   *)
Admitted.


Lemma gogo : forall t p a a' o_res o_res' v1 e1' p1 p1' o1 o1' e2 e2' tr2 p2 p2' o2 o2' tr1 x0,
    build_app_comp t p a = (Some v1, a') ->
    v1 {| st_ev := e2; st_trace := []; st_pl := p1; st_store := o1 |} =
    (Some o_res, {| st_ev := e1'; st_trace := tr1; st_pl := p1'; st_store := o1' |}) ->
    v1 {| st_ev := e2; st_trace := tr2; st_pl := p2; st_store := o2 |} =
    (Some o_res', {| st_ev := e2'; st_trace := tr2 ++ x0; st_pl := p2'; st_store := o2' |}) ->
    x0 = tr1.
Proof.
  intros.
  eapply gogo'.
  eassumption.
  assert (tr1 = [] ++ tr1).
  simpl.
  reflexivity.
  subst''.
  eassumption.
  eassumption.
Defined.

Ltac do_gogo :=
    match goal with
    | [
      H: ?v {| st_ev := _; st_trace := []; st_pl := _; st_store := _ |} =
         (Some _, {| st_ev := _; st_trace := ?tr1'; st_pl := _; st_store := _ |}),
     H2: build_app_comp _ _ _ = (Some ?v, _),
     H': ?v {| st_ev := _; st_trace := ?tr2; st_pl := _; st_store := _ |} =
           (Some _, {| st_ev := _; st_trace := ?tr2 ++ ?tr2'; st_pl := _; st_store := _ |}) |- _] =>

      assert (tr2' = tr1')by (eapply gogo; [apply H2 | apply H | apply H'])
    end.
*)

(*
Lemma foofoo : forall t f p tr_n p_n o_n a0 a' v e' tr' p' o' e'' tr'' p'' o'',
    build_app_comp t p a0 = (Some v, a') ->
    v {| st_ev := e'; st_trace := tr'; st_pl := p'; st_store := o' |} =
    (Some f, {| st_ev := e''; st_trace := tr''; st_pl := p''; st_store := o'' |}) ->
    (exists g e3 tr3 p3 o3,
        v {| st_ev := e'; st_trace := tr_n; st_pl := p_n; st_store := o_n |} =
        (Some g, {| st_ev := e3; st_trace := tr3; st_pl := p3; st_store := o3 |})).
Proof.
Admitted.

*)

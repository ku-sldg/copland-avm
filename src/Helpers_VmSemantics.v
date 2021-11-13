(*
Helper lemmas for proofs about the VM semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import MonadVM Impl_vm Term_Defs Term Auto StructTactics Maps GenStMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Set Nested Proofs Allowed.

Lemma pl_immut : forall t e tr p i,
    (*well_formed_r t -> *)
    st_pl
      (execSt
         (copland_compile t)
         {|
           st_ev := e;
           st_trace := tr;
           st_pl := p;
           st_evid := i|}) = p.
Proof.
  induction t; intros.
  -
    destruct a; (* asp *)
      try destruct a; (* asp params *)
      df;
      try reflexivity.
  -
    (*
    do_wf_pieces. *)
    repeat (df; try dohtac; df).   
    reflexivity.
  -
    (*
    do_wf_pieces. *)
    simpl in *.
    monad_unfold.
    repeat break_match;
      try solve_by_inversion.
    df.
    annogo.
    simpl.  
    assert (p = st_pl0).
    {
      edestruct IHt1.
      jkjk'.
    }
    assert (st_pl0 = st_pl).
    {
      edestruct IHt2.
      jkjk'.
    }
    congruence.
  -
    (*
    do_wf_pieces. *)
    annogo.
    df.
    
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
    }

    assert (st_pl0 = st_pl).
    {     
      edestruct IHt2.

      jkjk'; eauto.
    }

    congruence.
    +
      assert (p = st_pl).
      {
        edestruct IHt1.
          jkjk'; eauto.
      }

      assert (st_pl = st_pl0).
      {
        edestruct IHt2.
          jkjk'; eauto.
      }

      congruence.
    +
      symmetry.
      edestruct IHt1.
      jkjk'; eauto.
    +
      symmetry.
      edestruct IHt1.
      jkjk'; eauto.

  -
    annogo.
    df.

    repeat break_let.

    repeat break_match;
      try solve_by_inversion;
    repeat find_inversion;
    repeat dunit;
    simpl in * ; vmsts; simpl in *.
    +
    assert (p = st_pl).
    {
      edestruct IHt.
      jkjk'; eauto.     
    }
    congruence.   

    +
    assert (p = st_pl).
    {
      edestruct IHt.
      jkjk'; eauto.     
    }
    congruence. 
Defined.

Ltac do_pl_immut :=
  let tac H :=
       erewrite <- pl_immut;
        [ unfold execSt;
          rewrite H;
          reflexivity (*| 
          apply H2*)] in
      match goal with
      | [H: copland_compile ?t
                            {| st_ev := _;
                        st_trace := _;
                                    st_pl := ?p;
                            st_evid := _|} =
            (_,
             {| st_ev := _;
                         st_trace := _;
                         st_pl := ?p'; st_evid := _ |})
         (*H2: well_formed_r ?t*) |- _] =>
        assert_new_proof_by (p' = p) ltac:(tac H)  
      end.

Lemma st_congr :
  forall st tr e p i,
    st_ev st = e ->
    st_trace st = tr ->
    st_pl st = p ->
    st_evid st = i ->
    st =  {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i |}.
Proof.
  intros.
  subst; destruct st; auto.
Defined.

Ltac anhl :=
  annogo;
  match goal with
  | [(*H: well_formed_r ?a, *)
     H2: copland_compile ?a _ = _,
     H3: copland_compile ?a _ = _,
     IH: context[(*well_formed_r ?a*) _ -> _] |- _] =>
    edestruct IH;
    [(*apply H | *)
     apply H2 | apply H3 | idtac]; clear H2; clear H3;
    destruct_conjs; subst
  end.

Lemma hihi : forall t e e' e'' x x' y y' p p' p'' i i' i'',
    (*well_formed_r t -> *)
    copland_compile t {| st_ev := e; st_trace := x; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := e'; st_trace := x'; st_pl := p'; st_evid := i' |}) ->
    copland_compile t {| st_ev := e; st_trace := y; st_pl := p; st_evid := i |} =
    (Some tt, {| st_ev := e''; st_trace := y'; st_pl := p''; st_evid := i'' |}) ->
    (e' = e'' /\ p' = p'' /\ i' = i'').
Proof.
  induction t; intros.
  - destruct a; (* asp *)
      try destruct a; (* asp params *)
      df; eauto.
  -
    repeat (df; try dohtac; df).
    tauto.
  -
    (*do_wf_pieces. *)
    df;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.
    df.
    anhl.
    eauto. 
  -
    (*
    do_wf_pieces. *)
    df;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.
    df.
    repeat anhl.
    repeat find_inversion.
    eauto.
  -
    (*
    do_wf_pieces. *)
    cbn in *.
    monad_unfold.
    repeat break_let.
    simpl in *.

    dosome.
    df.
    dosome.
    dosome.
    df.

    annogo.
    simpl in *.

    repeat anhl.
    repeat (find_inversion).
    repeat find_rewrite.
    df.
    tauto.
Defined.

Ltac clear_triv :=
  match goal with
  | [H: ?x = ?x |- _] => clear H
  end.

Ltac dohi'' :=
  annogo;
  let tac H H' := eapply hihi; [apply H | apply H'] in
  match goal with
  | [H : copland_compile ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_evid := ?i |} =
         (?opt, {| st_ev := ?e'; st_trace := _; st_pl := ?p'; st_evid := ?i' |}),
         H' : copland_compile ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_evid := ?i |} =
              (?opt, {| st_ev := ?e''; st_trace := _; st_pl := ?p''; st_evid := ?i'' |})
                (*Hwf : well_formed_r ?t1*)  |- _] =>
    assert_new_proof_by (e' = e'' /\ p' = p'' /\ i' = i'') ltac:(tac H H')
  end.

Ltac dohi :=
  do 2 (repeat dohi''; destruct_conjs; subst);
  repeat clear_triv.

Lemma always_some : forall t vm_st vm_st' op,
    (*well_formed_r t -> *)
    copland_compile 
      t
      vm_st =
    (op, vm_st') ->
    op = Some tt.
Proof.
  induction t; intros.
  -
    destruct a; (* asp *)
      try destruct a; (* asp params *)
      try (df; tauto).
  -
    repeat (df; try dohtac; df).
    tauto.
  -
    df.
    (*
    do_wf_pieces. *)
    
    destruct o eqn:hhh;
      try (df; eauto).
  -
    df.
    (*
    do_wf_pieces. *)

    repeat break_match;
      try (
          df; eauto).
  -
    (*
    do_wf_pieces. *)
    df.
    dohtac.
    df.
    simpl.

    assert (o = Some tt) by eauto.
    subst.
    vmsts.
    df.
    tauto.
Defined.

Ltac do_somett :=
  match goal with
  | [H: copland_compile ?t _ = (?o, _)
        (*H2: well_formed_r ?t*) |- _] =>
    assert_new_proof_by (o = Some tt) ltac:(eapply always_some; [apply H])
  end.


Ltac do_asome := repeat do_somett; repeat clear_triv.

Lemma trace_irrel_pl : forall t tr1 tr1' tr2 e e' p1' p1 i i',
    (*well_formed_r t -> *)
    copland_compile t
           {| st_ev := e; st_trace := tr1; st_pl := p1; st_evid := i |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_evid := i' |}) ->
    
    st_pl
      (execSt (copland_compile t)
           {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i |}) = p1'.
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  do_asome.
  subst.
  dohi.
  df.
  tauto.
Defined.

Lemma trace_irrel_ev : forall t tr1 tr1' tr2 e e' p1' p1 i i',
    (*well_formed_r t -> *)
    copland_compile t
           {| st_ev := e; st_trace := tr1; st_pl := p1; st_evid := i|} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_evid := i' |}) ->
    
    st_ev
      (execSt (copland_compile t)
           {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i |}) = e'.
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  do_asome.
  subst.
  dohi.
  df.
  tauto.
Defined.

Lemma trace_irrel_evid : forall t tr1 tr1' tr2 e e' p1' p1 i i',
    (*well_formed_r t -> *)
    copland_compile t
           {| st_ev := e; st_trace := tr1; st_pl := p1; st_evid := i|} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_evid := i' |}) ->
    
    st_evid
      (execSt (copland_compile t)
           {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i |}) = i'.
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  do_asome.
  subst.
  dohi.
  df.
  tauto.
Defined.

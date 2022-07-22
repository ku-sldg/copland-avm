(*
Helper lemmas for proofs about the CVM semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Cvm_Monad Cvm_Impl Term_Defs Auto StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

(*
Set Nested Proofs Allowed.
*)

(* Lemma stating the CVM st_pl parameter ends up where it started execuiton *)
Lemma pl_immut : forall t e tr p i,
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
      try reflexivity.
  -
    df.
    reflexivity.
  -
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
      jkjke.
    }
    assert (st_pl0 = st_pl).
    {
      edestruct IHt2.
      jkjk_s.
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
      jkjk_s; eauto.     
    }

    assert (st_pl0 = st_pl).
    {     
      edestruct IHt2.
      jkjk_s; eauto.
    }

    congruence.
    +
      assert (p = st_pl).
      {
        edestruct IHt1.
        jkjk_s; eauto.
      }

      assert (st_pl = st_pl0).
      {
        edestruct IHt2.
        jkjk_s; eauto.
      }

      congruence.
    +
      symmetry.
      edestruct IHt1.
      jkjk_s; eauto.
    +
      symmetry.
      edestruct IHt1.
      jkjk_s; eauto.

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
      edestruct IHt1.
      jkjke. 
    }
    congruence.   

    +
    assert (p = st_pl).
    {
      edestruct IHt1.
      jkjke.    
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

(* Hack to apply a specific induction hypothesis in some proofs *)
Ltac anhl :=
  annogo;
  match goal with
  | [H2: copland_compile ?a _ = _,
     H3: copland_compile ?a _ = _,
     IH: context[ _ -> _] |- _] =>
    edestruct IH;
    [ apply H2 | apply H3 | idtac]; clear H2; clear H3;
    destruct_conjs; subst
  end.

(* Lemma stating the following:  If all starting parameters to the cvm_st are the same, except 
   for possibly the trace, then all of those final parameters should also be equal. *)
Lemma hihi : forall t e e' e'' x x' y y' p p' p'' i i' i'',
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
    df;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.
    df.
    anhl.
    eauto. 
  -
    df;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.
    df.
    repeat anhl.
    repeat find_inversion.
    eauto.
  -
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
     |- _] =>
    assert_new_proof_by (e' = e'' /\ p' = p'' /\ i' = i'') ltac:(tac H H')
  end.

Ltac dohi :=
  do 2 (repeat dohi''; destruct_conjs; subst);
  repeat clear_triv.


(* CVM execution always succeeds.  
   Note:  This may need revisiting if we consider more robust models of CVM failure. *)
Lemma always_some : forall t vm_st vm_st' op,
    copland_compile t vm_st = (op, vm_st') ->
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
    
    destruct o eqn:hhh;
      try (df; eauto).
  -
    df.

    repeat break_match;
      try (
          df; eauto).
  -
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
     |- _] =>
    assert_new_proof_by (o = Some tt) ltac:(eapply always_some; [apply H])
  end.

Ltac do_asome := repeat do_somett; repeat clear_triv.

(* States that the resulting place (st_pl) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_pl : forall t tr1 tr1' tr2 e e' p1' p1 i i',
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

(* States that the resulting evidence (st_ev) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_ev : forall t tr1 tr1' tr2 e e' p1' p1 i i',
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

(* States that the resulting event id counter (st_evid) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_evid : forall t tr1 tr1' tr2 e e' p1' p1 i i',
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

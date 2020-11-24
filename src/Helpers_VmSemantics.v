Require Import MonadVM Impl_vm Term Auto StructTactics MonadVMFacts Maps GenStMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Lemma pl_immut : forall t e tr p o,
    well_formed t ->
    st_pl
      (execSt
         (build_comp t)
         {|
           st_ev := e;
           st_trace := tr;
           st_pl := p;
           st_store := o |}) = p.
Proof.
  induction t; intros.
  -
    destruct r.
    destruct a;
      reflexivity.
  -
    repeat (df; dohtac).
    reflexivity.
  -
    do_wf_pieces.
    
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
      eassumption.
      jkjk'.
    }

    assert (st_pl0 = st_pl).
    {
      edestruct IHt2.
      eassumption.
      jkjk'.
    }

    congruence.   
  -
    do_wf_pieces.
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
      eassumption.
      jkjk'; eauto.     
    }

    assert (st_pl0 = st_pl).
    {     
      edestruct IHt2.
      eassumption.
      jkjk'; eauto.
    }

    congruence.
    +
      assert (p = st_pl).
      {
        edestruct IHt1.
        eassumption.
          jkjk'; eauto.
      }

      assert (st_pl = st_pl0).
      {
        edestruct IHt2.
        eassumption.
          jkjk'; eauto.
      }

      congruence.
    +
      symmetry.
      edestruct IHt1.
      eassumption.
      jkjk'; eauto.
    +
      symmetry.
      edestruct IHt1.
      eassumption.
        jkjk'; eauto.     
  -
    df.
    unfold runParThreads, runParThread in *.
    repeat (df; dohtac).
    reflexivity.
Defined.

Ltac do_pl_immut :=
  let tac :=
      (symmetry;
       erewrite <- pl_immut in *;
       jkjk'
      ) in
  repeat (
      match goal with
      | [H: build_comp _ {| st_ev := _; st_trace := _;
                                                    st_pl := ?p;
                                                             st_store := _ |} =
            (_,
             {| st_ev := _; st_trace := _;
                                        st_pl := ?p';
                                                 st_store := _ |}) |- _] =>
        assert_new_proof_by (p = p') (tac)     
      end); subst.


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

Ltac allss :=
  repeat find_inversion;
  try bogus;
  repeat (do_get_store_at_facts; subst; eauto);
  repeat (do_get_store_at_facts_fail; subst; eauto);
  repeat get_store_at_bogus;
  try do_bd;
  subst; eauto.



Ltac anhl :=
  annogo;
  match goal with
  | [H: well_formed ?a,
     H2: build_comp ?a _ = _,
     H3: build_comp ?a _ = _,
     IH: context[well_formed ?a (*build_comp ?a _ = _ *) -> _] |- _] =>
    edestruct IH;
    [apply H | 
     apply H2 | apply H3 | idtac]; clear H2; clear H3;
    destruct_conjs; subst
  end.

Lemma hihi : forall t e e' e'' x x' y y' p p' p'' o o' o'',
    well_formed t ->
    build_comp t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x'; st_pl := p'; st_store := o' |}) ->
    build_comp t {| st_ev := e; st_trace := y; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := y'; st_pl := p''; st_store := o'' |}) ->
    (e' = e'' /\ p' = p'' /\ o' = o'').
Proof.
  induction t; intros.
  - destruct a;
      df; eauto.
  -
    do_wf_pieces.
    repeat (df; dohtac).
    tauto.
  -
    do_wf_pieces.
    df;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.
    df.
    anhl.
    eauto.   
  -
    do_wf_pieces.
    df;
    repeat break_match;
    try (repeat find_inversion);
    simpl in *.
    df.
    repeat anhl.
    eauto.   
  -
    do_wf_pieces.
    df.
    repeat (
        df;
        dohtac).
    tauto.
Defined.

(*
Ltac tacc Hwf H H' := (eapply hihi; [apply Hwf | apply H | apply H']).
*)

Ltac dohi :=
  annogo;
  let tac := (eapply hihi; eauto) in
  match goal with
  | [H : build_comp ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_store := ?o |} =
         (?opt, {| st_ev := ?e'; st_trace := _; st_pl := ?p'; st_store := ?o' |}),
         H' : build_comp ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_store := ?o |} =
              (?opt, {| st_ev := ?e''; st_trace := _; st_pl := ?p''; st_store := ?o'' |}) (*,
                Hwf : well_formed ?t1*)  |- _] =>
    assert_new_proof_by (e' = e'' /\ p' = p'' /\ o' = o'') tac
  end.

Ltac dohi' :=
  annogo;
  match goal with
  | [H: well_formed ?a, 
        H2: build_comp ?a _ = _,
            H3: build_comp ?a _ = _ |- _] =>
    edestruct hihi;
    [ (apply H) | 
      repeat dunit; apply H2 |
      repeat dunit; apply H3 |
      idtac]; (*clear H2; clear H3;*)
    destruct_conjs; subst
  end.

Lemma get_store_in : forall x st st' o y,
    get_store_at x st = (None, st') ->
    st_store st = o ->
    map_get o x = (Some y) ->
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

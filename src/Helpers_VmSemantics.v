Require Import MonadVM Impl_vm Term Auto StructTactics MonadVMFacts Maps GenStMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Set Nested Proofs Allowed.

Lemma pl_immut : forall t e tr p o,
    well_formed t ->
    st_pl
      (execSt
         (copland_compile t)
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
    repeat (df; dohtac; df).
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
    repeat (df; dohtac; df; try tauto).

    (*

    (*
    assert (PeanoNat.Nat.eqb n3 n1 = false /\
            PeanoNat.Nat.eqb n1 (n4 - 1) = false /\
            PeanoNat.Nat.eqb (n4 - 1) (n2 - 1) = false) as W by
          (eapply abpar_store_non_overlap; [apply H | apply Heqr2 | apply Heqr1]);
      destruct W as [X [Y Z]].
    rewrite X in *; clear X.
      rewrite Y in *; clear Y.
     *)
    

    htac''.

    

    
      
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
    repeat (df; dohtac; try tauto).
    reflexivity.



    assert (PeanoNat.Nat.eqb (n4 - 1) (n2 - 1) = false).
    {
      eapply hhhhh; eauto.
    }
    reflexivity. *)
Defined.

Ltac do_pl_immut :=
  let tac H H2 :=
       erewrite <- pl_immut;
        [ unfold execSt;
          rewrite H;
          reflexivity | 
          apply H2] in
      match goal with
      | [H: copland_compile ?t
            {| st_ev := _;
                        st_trace := _;
                        st_pl := ?p;
                        st_store := _ |} =
            (_,
             {| st_ev := _;
                         st_trace := _;
                         st_pl := ?p';
                                  st_store := _ |}),
         H2: well_formed ?t |- _] =>
        assert_new_proof_by (p' = p) ltac:(tac H H2)  
      end.


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

(*
Ltac allss :=
  repeat find_inversion;
  try bogus;
  repeat (do_get_store_at_facts; subst; eauto);
  repeat (do_get_store_at_facts_fail; subst; eauto);
  repeat get_store_at_bogus;
  try do_bd;
  subst; eauto.
*)



Ltac anhl :=
  annogo;
  match goal with
  | [H: well_formed ?a,
     H2: copland_compile ?a _ = _,
     H3: copland_compile ?a _ = _,
     IH: context[well_formed ?a (*copland_compile ?a _ = _ *) -> _] |- _] =>
    edestruct IH;
    [apply H | 
     apply H2 | apply H3 | idtac]; clear H2; clear H3;
    destruct_conjs; subst
  end.

Lemma hihi : forall t e e' e'' x x' y y' p p' p'' o o' o'',
    well_formed t ->
    copland_compile t {| st_ev := e; st_trace := x; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e'; st_trace := x'; st_pl := p'; st_store := o' |}) ->
    copland_compile t {| st_ev := e; st_trace := y; st_pl := p; st_store := o |} =
    (Some tt, {| st_ev := e''; st_trace := y'; st_pl := p''; st_store := o'' |}) ->
    (e' = e'' /\ p' = p'' /\ o' = o'').
Proof.
  induction t; intros.
  - destruct a;
      df; eauto.
  -
    do_wf_pieces.
    repeat (df; dohtac; df).
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
    repeat (df; dohtac; df).
    tauto.

    (*

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
    
    tauto. *)
Defined.

Ltac clear_triv :=
  match goal with
  | [H: ?x = ?x |- _] => clear H
  end.

Ltac dohi'' :=
  annogo;
  let tac Hwf H H' := eapply hihi; [apply Hwf | apply H | apply H'] in
  match goal with
  | [H : copland_compile ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_store := ?o |} =
         (?opt, {| st_ev := ?e'; st_trace := _; st_pl := ?p'; st_store := ?o' |}),
         H' : copland_compile ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_store := ?o |} =
              (?opt, {| st_ev := ?e''; st_trace := _; st_pl := ?p''; st_store := ?o'' |}),
                Hwf : well_formed ?t1  |- _] =>
    assert_new_proof_by (e' = e'' /\ p' = p'' /\ o' = o'') ltac:(tac Hwf H H')
  end.

Ltac dohi :=
  do 2 (repeat dohi''; destruct_conjs; subst);
      clear_triv.

(*
Ltac dohi' :=
  annogo;
  match goal with
  | [H: well_formed ?a, 
        H2: copland_compile ?a _ = _,
            H3: copland_compile ?a _ = _ |- _] =>
    edestruct hihi;
    [ (apply H) | 
      repeat dunit; apply H2 |
      repeat dunit; apply H3 |
      idtac]; (*clear H2; clear H3;*)
    destruct_conjs; subst
  end.
*)

(*
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
 *)


Lemma always_some : forall t vm_st vm_st' op,
    well_formed t ->
    copland_compile 
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
    repeat (df; dohtac; df).
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
    repeat (df; dohtac; df).
    tauto.
    (*
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
    tauto. *)
Defined.

Ltac do_somett :=
  match goal with
  | [H: copland_compile ?t _ = (?o, _),
        H2: well_formed ?t |- _] =>
    assert_new_proof_by (o = Some tt) ltac:(eapply always_some; [apply H2 | apply H])
  end.


Ltac do_asome := repeat do_somett; clear_triv.

Lemma trace_irrel_store : forall t tr1 tr1' tr2 e e' p1' p1 o' o,
    well_formed t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    
    st_store
      (execSt (copland_compile t)
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |}) = o'.
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  do_asome.
  subst.
  dohi.
  df.
  tauto.
Defined.

Lemma trace_irrel_pl : forall t tr1 tr1' tr2 e e' p1' p1 o' o,
    well_formed t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    
    st_pl
      (execSt (copland_compile t)
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |}) = p1'.
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  do_asome.
  subst.
  dohi.
  df.
  tauto.
Defined.

Lemma trace_irrel_ev : forall t tr1 tr1' tr2 e e' p1' p1 o' o,
    well_formed t ->
    copland_compile t
           {| st_ev := e;  st_trace := tr1; st_pl := p1;  st_store := o  |} =
    (Some tt, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_store := o' |}) ->
    
    st_ev
      (execSt (copland_compile t)
           {| st_ev := e;  st_trace := tr2; st_pl := p1;  st_store := o  |}) = e'.
Proof.
  intros.
  destruct (copland_compile t {| st_ev := e; st_trace := tr2; st_pl := p1; st_store := o |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  do_asome.
  subst.
  dohi.
  df.
  tauto.
Defined.

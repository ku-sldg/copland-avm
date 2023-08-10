(*
Helper lemmas for proofs about the CVM semantics.

Author:  Adam Petz, ampetz@ku.edu
*)

Require Import Anno_Term_Defs Cvm_Monad Cvm_Impl Term_Defs Auto StructTactics AutoApp Manifest.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

(*
Set Nested Proofs Allowed.
*)


Lemma ac_immut : forall t e tr p i ac,
  st_AM_config 
    (execErr 
      (build_cvm t)
      {|
        st_ev := e;
        st_trace := tr;
        st_pl := p;
        st_evid := i;
        st_AM_config := ac
      |}) = ac.
Proof.
  induction t; repeat (monad_unfold; simpl in *); intuition.
  - destruct a; monad_unfold; eauto.
    destruct (aspCb ac a p (encodeEvRaw (get_bits e)) (get_bits e)) eqn:E1; simpl in *; eauto.
  - pose proof (IHt1 e tr p i ac).
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |}) eqn:C1;
    simpl in *; eauto;
    destruct r; simpl in *; intuition; eauto.
    destruct c; simpl in *.
    pose proof (IHt2 st_ev st_trace st_pl st_evid st_AM_config).
    destruct (build_cvm t2 {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl; st_evid := st_evid; st_AM_config := st_AM_config |}) eqn:C2;
    simpl in *; subst; eauto.
  - monad_unfold; simpl in *.
    pose proof (IHt1 e (tr ++ [Term_Defs.split i p]) p (i + 1) ac).
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr ++ [Term_Defs.split i p]; st_pl := p; st_evid := (i + 1); st_AM_config := ac |}) eqn:C1;
    simpl in *; eauto;
    destruct r; simpl in *; intuition; eauto.
    destruct c; simpl in *.
    pose proof (IHt2 e st_trace st_pl st_evid st_AM_config).
    destruct (build_cvm t2 {| st_ev := e; st_trace := st_trace; st_pl := st_pl; st_evid := st_evid; st_AM_config := st_AM_config |}) eqn:C2;
    simpl in *; subst; eauto;
    destruct r; simpl in *; eauto.
  - monad_unfold; simpl in *.
    pose proof (IHt1 e ((tr ++ [Term_Defs.split i p]) ++ [cvm_thread_start l p t2 (get_et e)]) p (i + 1) ac).
    destruct (build_cvm t1 {| st_ev := e; st_trace := (tr ++ [Term_Defs.split i p]) ++ [cvm_thread_start l p t2 (get_et e)]; st_pl := p; st_evid := (i + 1); st_AM_config := ac |}) eqn:C1;
    simpl in *; eauto;
    destruct r; simpl in *; intuition; eauto.
    destruct c; simpl in *; eauto.
Qed.

(* Lemma stating the CVM st_pl parameter ends up where it started execution *)
Lemma pl_immut : forall t e tr p i ac,
    st_pl
      (execErr
         (build_cvm t)
         {|
           st_ev := e;
           st_trace := tr;
           st_pl := p;
           st_evid := i;
           st_AM_config := ac |}) = p.
Proof.
  induction t; intros.
  -
    destruct a; (* asp *)
      try destruct a; (* asp params *)    
      try reflexivity; simpl in *.
      repeat ff.
      
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
    Locate annogo.
    Locate vmsts.
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
        [ unfold execErr;
          rewrite H;
          reflexivity (*| 
          apply H2*)] in
      match goal with
      | [H: build_cvm ?t
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
  forall st tr e p i ac,
    st_ev st = e ->
    st_trace st = tr ->
    st_pl st = p ->
    st_evid st = i ->
    st_AM_config st = ac ->
    st =  {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |}.
Proof.
  intros.
  subst; destruct st; auto.
Defined.

Print build_cvm.

(* Hack to apply a specific induction hypothesis in some proofs *)
Ltac anhl :=
  annogo;
  match goal with
  | [H2: build_cvm ?a _ = _,
     H3: build_cvm ?a _ = _,
     IH: context[ _ -> _] |- _] =>
    edestruct IH;
    [ apply H2 | apply H3 | idtac]; clear H2; clear H3;
    destruct_conjs; subst
  end.

Ltac monad_simp := 
  repeat (monad_unfold; simpl in *; eauto).

Theorem evidence_deterministic_output_on_results : forall t e tr1 tr2 p i1 i2 ac st1 st2,
  build_cvm t {| st_ev := e; st_trace := tr1; st_pl := p; st_evid := i1; st_AM_config := ac |} = (resultC tt, st1) ->
  build_cvm t {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i2; st_AM_config := ac |} = (resultC tt, st2) ->
  st1.(st_ev) = st2.(st_ev).
Proof.
  induction t; intros; monad_simp.
  - destruct a; monad_simp; invc H; invc H0; eauto;
    destruct (aspCb ac a p (encodeEvRaw (get_bits e)) (get_bits e)); 
    simpl in *; invc H1; invc H2; eauto.
  - invc H; invc H0; eauto.
  - destruct (build_cvm t1 {| st_ev := e; st_trace := tr1; st_pl := p; st_evid := i1; st_AM_config := ac |}) eqn:E1;
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i2; st_AM_config := ac |}) eqn:E2;
    destruct r, r0; invc H; invc H0; destruct u, u0, c, c0.
    pose proof (IHt1 _ _ _ _ _ _ _ _ _ E1 E2); simpl in *; subst.
    assert (st_pl = st_pl0). {
      pose proof (pl_immut t1 e tr2 p i2 ac); monad_unfold;
      pose proof (pl_immut t1 e tr1 p i1 ac); monad_unfold.
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    assert (st_AM_config = st_AM_config0). {
      pose proof (ac_immut t1 e tr2 p i2 ac); monad_unfold;
      pose proof (ac_immut t1 e tr1 p i1 ac); monad_unfold.
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    subst; clear E1 E2.
    destruct (build_cvm t2 {| st_ev := st_ev0; st_trace := st_trace; st_pl := st_pl0; st_evid := st_evid; st_AM_config := st_AM_config0 |}) eqn:E1;
    destruct (build_cvm t2 {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0; st_evid := st_evid0; st_AM_config := st_AM_config0 |}) eqn:E2;
    invc H1; invc H2; simpl in *; eauto.
  - destruct (build_cvm t1 {| st_ev := e; st_trace := tr1 ++ [Term_Defs.split i1 p]; st_pl := p; st_evid := i1 + 1; st_AM_config := ac |}) eqn:E1;
    destruct (build_cvm t1 {| st_ev := e; st_trace := tr2 ++ [Term_Defs.split i2 p]; st_pl := p; st_evid := i2 + 1; st_AM_config := ac |}) eqn:E2;
    destruct r, r0; invc H; invc H0; destruct u, u0, c, c0.
    pose proof (IHt1 _ _ _ _ _ _ _ _ _ E1 E2); simpl in *; subst.
    assert (st_pl = st_pl0). {
      pose proof (pl_immut t1 e (tr2 ++ [Term_Defs.split i2 p]) p (i2 + 1) ac); monad_unfold;
      pose proof (pl_immut t1 e (tr1 ++ [Term_Defs.split i1 p]) p (i1 + 1) ac); monad_unfold;
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    assert (st_AM_config = st_AM_config0). {
      pose proof (ac_immut t1 e (tr2 ++ [Term_Defs.split i2 p]) p (i2 + 1) ac); monad_unfold;
      pose proof (ac_immut t1 e (tr1 ++ [Term_Defs.split i1 p]) p (i1 + 1) ac); monad_unfold;
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    subst; clear E1 E2.
    destruct (build_cvm t2 {| st_ev := e; st_trace := st_trace; st_pl := st_pl0; st_evid := st_evid; st_AM_config := st_AM_config0 |}) eqn:E1;
    destruct (build_cvm t2 {| st_ev := e; st_trace := st_trace0; st_pl := st_pl0; st_evid := st_evid0; st_AM_config := st_AM_config0 |}) eqn:E2;
    destruct r0, r;
    invc H1; invc H2; simpl in *;
    destruct u, u0.
    pose proof (IHt2 _ _ _ _ _ _ _ _ _ E1 E2); simpl in *; subst; 
    rewrite H; eauto.
  - destruct (build_cvm t1 {| st_ev := e; st_trace := (tr1 ++ [Term_Defs.split i1 p]) ++ [cvm_thread_start l p t2 (get_et e)]; st_pl := p; st_evid := i1 + 1; st_AM_config := ac |}) eqn:E1;
    destruct (build_cvm t1 {| st_ev := e; st_trace := (tr2 ++ [Term_Defs.split i2 p]) ++ [cvm_thread_start l p t2 (get_et e)]; st_pl := p; st_evid := i2 + 1; st_AM_config := ac |}) eqn:E2;
    destruct r, r0; invc H; invc H0; destruct u, u0, c, c0.
    pose proof (IHt1 _ _ _ _ _ _ _ _ _ E1 E2); simpl in *; subst.
    assert (st_pl = st_pl0). {
      pose proof (pl_immut t1 e ((tr1 ++ [Term_Defs.split i1 p]) ++ [cvm_thread_start l p t2 (get_et e)]) p (i1 + 1) ac); monad_unfold;
      pose proof (pl_immut t1 e ((tr2 ++ [Term_Defs.split i2 p]) ++ [cvm_thread_start l p t2 (get_et e)]) p (i2 + 1) ac); monad_unfold.
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    assert (st_AM_config = st_AM_config0). {
      pose proof (ac_immut t1 e ((tr1 ++ [Term_Defs.split i1 p]) ++ [cvm_thread_start l p t2 (get_et e)]) p (i1 + 1) ac); monad_unfold;
      pose proof (ac_immut t1 e ((tr2 ++ [Term_Defs.split i2 p]) ++ [cvm_thread_start l p t2 (get_et e)]) p (i2 + 1) ac); monad_unfold.
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    subst; clear E1 E2; eauto.
Qed.

Lemma cvm_errors_deterministic :  forall t e tr1 tr2 p i1 i2 ac r1 r2 st1 st2,
  build_cvm t
    {|
      st_ev := e;
      st_trace := tr1;
      st_pl := p;
      st_evid := i1;
      st_AM_config := ac
    |} =
  (r1, st1) -> 

  build_cvm t
    {|
      st_ev := e;
      st_trace := tr2;
      st_pl := p;
      st_evid := i2;
      st_AM_config := ac
    |} =
  (r2, st2) -> 

  ((r1 = r2) \/ (r1 = errC (callback_error Runtime) \/ (r2 = errC (callback_error Runtime)))).
Proof.
  induction t; intros; monad_simp.
  - destruct a; monad_simp; invc H; invc H0; eauto.
    destruct (aspCb ac a p (encodeEvRaw (get_bits e)) (get_bits e)); 
    invc H1; invc H2; eauto.
  - invc H; invc H0; eauto.
  - destruct (build_cvm t1 {| st_ev := e; st_trace := tr1; st_pl := p; st_evid := i1; st_AM_config := ac |}) eqn:E1,
      (build_cvm t1 {| st_ev := e; st_trace := tr2; st_pl := p; st_evid := i2; st_AM_config := ac |}) eqn:E2, r, r0;
    simpl in *; invc H; invc H0; eauto;
    destruct (IHt1 _ _ _ _ _ _ _ _ _ _ _ E1 E2) as [H | [H | H]]; eauto; try congruence.
    invc H; destruct c, c0; simpl in *.
    assert (st_AM_config = st_AM_config0). {
      pose proof (ac_immut t1 e tr2 p i2 ac); monad_unfold;
      pose proof (ac_immut t1 e tr1 p i1 ac); monad_unfold.
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    assert (st_pl = st_pl0). {
      pose proof (pl_immut t1 e tr2 p i2 ac); monad_unfold;
      pose proof (pl_immut t1 e tr1 p i1 ac); monad_unfold.
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    assert (st_ev = st_ev0). {
      destruct u0.
      pose proof (evidence_deterministic_output_on_results t1 e tr1 tr2 p i1 i2 ac _ _ E1 E2); eauto.
    }
    subst; clear E1 E2.
    destruct (build_cvm t2 {| st_ev := st_ev0; st_trace := st_trace; st_pl := st_pl0; st_evid := st_evid; st_AM_config := st_AM_config0 |}) eqn:E1, (build_cvm t2 {| st_ev := st_ev0; st_trace := st_trace0; st_pl := st_pl0; st_evid := st_evid0; st_AM_config := st_AM_config0 |}) eqn:E2; invc H1; invc H2; eauto.

  - destruct (build_cvm t1 {| st_ev := e; st_trace := tr1 ++ [Term_Defs.split i1 p]; st_pl := p; st_evid := i1 + 1; st_AM_config := ac |}) eqn:E1,
      (build_cvm t1 {| st_ev := e; st_trace := tr2 ++ [Term_Defs.split i2 p]; st_pl := p; st_evid := i2 + 1; st_AM_config := ac |}) eqn:E2, r, r0;
    simpl in *; invc H; invc H0; eauto;
    destruct (IHt1 _ _ _ _ _ _ _ _ _ _ _ E1 E2) as [H | [H | H]]; eauto; try congruence.
    invc H; destruct c, c0; simpl in *.
    assert (st_AM_config = st_AM_config0). {
      pose proof (ac_immut t1 e (tr2 ++ [Term_Defs.split i2 p]) p (i2 + 1) ac); monad_unfold;
      pose proof (ac_immut t1 e (tr1 ++ [Term_Defs.split i1 p]) p (i1 + 1) ac); monad_unfold;
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    assert (st_pl = st_pl0). {
      pose proof (pl_immut t1 e (tr2 ++ [Term_Defs.split i2 p]) p (i2 + 1) ac); monad_unfold;
      pose proof (pl_immut t1 e (tr1 ++ [Term_Defs.split i1 p]) p (i1 + 1) ac); monad_unfold;
      rewrite E1, E2 in *; simpl in *; subst; eauto.
    }
    assert (st_ev = st_ev0). {
      destruct u0.
      pose proof (evidence_deterministic_output_on_results t1 e 
        (tr1 ++ [Term_Defs.split i1 p]) (tr2 ++ [Term_Defs.split i2 p]) p (i1 + 1) (i2 + 1) ac _ _ E1 E2); eauto.
    }
    subst; clear E1 E2.
    destruct (build_cvm t2 {| st_ev := e; st_trace := st_trace; st_pl := st_pl0; st_evid := st_evid; st_AM_config := st_AM_config0 |}) eqn:E1, (build_cvm t2 {| st_ev := e; st_trace := st_trace0; st_pl := st_pl0; st_evid := st_evid0; st_AM_config := st_AM_config0 |}) eqn:E2, r, r0; simpl in *; invc H1; invc H2;
    pose proof (IHt2 _ _ _ _ _ _ _ _ _ _ _ E1 E2); eauto;
    destruct H as [H | [H | H]]; eauto; try congruence.
  
  - destruct (build_cvm t1 {| st_ev := e; st_trace := (tr1 ++ [Term_Defs.split i1 p]) ++ [cvm_thread_start l p t2 (get_et e)]; st_pl := p; st_evid := i1 + 1; st_AM_config := ac |}) eqn:E1,
      (build_cvm t1 {| st_ev := e; st_trace := (tr2 ++ [Term_Defs.split i2 p]) ++ [cvm_thread_start l p t2 (get_et e)]; st_pl := p; st_evid := i2 + 1; st_AM_config := ac |} ) eqn:E2, r, r0;
    simpl in *; invc H; invc H0; eauto;
    destruct (IHt1 _ _ _ _ _ _ _ _ _ _ _ E1 E2) as [H | [H | H]]; eauto; try congruence.
Qed.

(* Lemma stating the following:  If all starting parameters to the cvm_st are the same, except 
   for possibly the trace, then all of those final parameters should also be equal. *)
Lemma st_trace_irrel : forall t e e' e'' x x' y y' p p' p'' i i' i'' ac ac' ac'' res,
    build_cvm t {| st_ev := e; st_trace := x; st_pl := p; st_evid := i; st_AM_config := ac |} =
    (res (* resultC tt *), {| st_ev := e'; st_trace := x'; st_pl := p'; st_evid := i'; st_AM_config := ac' |}) ->
    build_cvm t {| st_ev := e; st_trace := y; st_pl := p; st_evid := i; st_AM_config := ac |} =
    (res (* resultC tt *), {| st_ev := e''; st_trace := y'; st_pl := p''; st_evid := i''; st_AM_config := ac'' |}) ->
    ((e' = e'' /\ p' = p'' /\ i' = i'' /\ ac' = ac'') \/ (res = errC (callback_error Runtime))).
Proof.
  induction t; intros.
  - destruct a; (* asp *)
      try destruct a; (* asp params *)
      df; eauto.
      repeat ff.
  - (* at case *)
    repeat (df; try dohtac; df); eauto.

  - (* lseq case *)

    simpl in *.
    monad_unfold.
    repeat break_let;
    destruct r, r1; monad_simp;
    invc H; invc H0; monad_simp;
    destruct (cvm_errors_deterministic t1 e x y p i i ac _ _ _ _ Heqp2 Heqp0) as [H | [H | H]]; 
    try congruence; invc H; intuition;
    destruct c1, c, u; monad_simp.
    pose proof (ac_immut t1 e x p i ac);
    pose proof (ac_immut t1 e y p i ac);
    pose proof (pl_immut t1 e x p i ac);
    pose proof (pl_immut t1 e y p i ac);
    monad_unfold; rewrite Heqp2, Heqp0 in *; simpl in *; subst.
    pose proof (IHt1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqp2 Heqp0); intuition; subst; eauto;
    try congruence.


  - (* bseq case *)

    simpl in *.
    monad_unfold;
    repeat break_let;
    destruct r, r1; monad_simp; 
    invc H; invc H0; invc Heqp4; invc Heqp1; invc Heqp3; invc Heqp0;
    invc Heqp11; invc Heqp10; invc Heqp7; monad_simp;
    destruct r8, r12, r5; invc Heqp5;
    invc Heqp12; invc Heqp8; eauto;
    destruct (cvm_errors_deterministic _ _ _ _ _ _ _ _ _ _ _ _ Heqp9 Heqp2) as [H | [H | H]];
    eauto; try congruence; invc H; intuition;
    destruct c1, c8; monad_simp.
    * 
    pose proof (ac_immut t1 );
    pose proof (ac_immut t1 );
    pose proof (pl_immut t1 );
    pose proof (pl_immut t1 );
    monad_simp.
    * 
    
    * eapply IHt2; eauto.
    invc H; invc H0; monad_simp; subst;
    invc 
    destruct (cvm_errors_deterministic t1 e x y p i i ac _ _ _ _ Heqp2 Heqp0) as [H | [H | H]]; 
    try congruence; invc H; intuition;
    destruct c1, c, u; monad_simp.
    pose proof (ac_immut t1 e x p i ac);
    pose proof (ac_immut t1 e y p i ac);
    pose proof (pl_immut t1 e x p i ac);
    pose proof (pl_immut t1 e y p i ac);
    monad_unfold; rewrite Heqp2, Heqp0 in *; simpl in *; subst.
    pose proof (IHt1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Heqp2 Heqp0); intuition; subst; eauto;
    try congruence.
    simpl in *.
    monad_unfold.
    repeat break_let.
    assert (r = res). ff.
    assert (c = {| st_ev := e''; st_trace := y'; st_pl := p''; st_evid := i''; st_AM_config := ac'' |}) by ff.
    subst.
    invc H0.
    invc Heqp0.
    invc Heqp3.
    invc Heqp4.

    destruct r1.
    + (* t1 term successful *)
      invc Heqp1.
      df.

      destruct r5.
      ++ (* t2 term successful *)
        df. 
        destruct r12; df. 
        destruct r8; df. 
        anhl; ff.

        assert (errC c = resultC tt).
        {
      eapply cvm_errors_deterministic.
      apply Heqp2.
      apply Heqp9.
        }
        solve_by_inversion.

        destruct r8; df.

        anhl; ff.

      ++ (* t2 term failed *)
        df.
        destruct r12; df. 
        +++
        destruct c8; destruct c9; df.

        do_pl_immut.
        subst.
        do_pl_immut.
        subst.
        do_pl_immut.
        subst.
        repeat do_pl_immut.
        subst.
        assert (ac'' = st_AM_config).
        {
          assert (ac = st_AM_config). 
          {
            eapply ac_config_immut; apply Heqp9.
          }
          subst.
          symmetry.
          
          eapply ac_config_immut. apply Heqp2.
        }
        subst.

        assert (resultC tt = errC c0).
        {
      eapply cvm_errors_deterministic.
      apply Heqp6.
      apply Heqp13.
        }
        solve_by_inversion.

        +++
          ff.
          anhl.
          ff.
    + (* t1 term failed *)
      df. 
      ff.
      ++
      assert (resultC tt = errC c).
      {
      eapply cvm_errors_deterministic.
      apply Heqp2.
      apply Heqp9.
      }
      solve_by_inversion.
  
      ++
      assert (resultC tt = errC c).
      {
      eapply cvm_errors_deterministic.
      apply Heqp2.
      apply Heqp9.
      }
      solve_by_inversion.

      ++
      ff.
      anhl.
      ff.
      anhl.
      ff.
      ++
      ff.
      anhl.
      ff.
      ff.
      anhl.
      ff.
      ff.
  - (* bpar case *)
    cbn in *.
    monad_unfold.
    repeat break_let.
    simpl in *.

    dosome.
    df.
    dosome.
    dosome.
    df.

    ff.
    +

    (*
    annogo.
    simpl in *.
    ff. *)

    repeat anhl.
    repeat (find_inversion).
    repeat find_rewrite.
    df.
    tauto.
    +

    repeat anhl.
    repeat (find_inversion).
    repeat find_rewrite.
    df. 
    tauto.
Defined.


Ltac dohi'' :=
  annogo;
  let tac H H' := eapply st_trace_irrel; [apply H | apply H'] in
  match goal with
  | [H : build_cvm ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |} =
         (?opt, {| st_ev := ?e'; st_trace := _; st_pl := ?p'; st_evid := ?i'; st_AM_config := ?ac' |}),
         H' : build_cvm ?t1 {| st_ev := ?e; st_trace := _; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |} =
              (?opt, {| st_ev := ?e''; st_trace := _; st_pl := ?p''; st_evid := ?i''; st_AM_config := ?ac'' |})
     |- _] =>
    assert_new_proof_by (e' = e'' /\ p' = p'' /\ i' = i'' /\ ac' = ac'') ltac:(tac H H')
  end.

Ltac dohi :=
  do 2 (repeat dohi''; destruct_conjs; subst);
  repeat clear_triv.





(* States that the resulting place (st_pl) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_pl : forall t tr1 tr1' tr2 e e' p1' p1 i i' ac ac' res,
    build_cvm t
           {| st_ev := e; st_trace := tr1; st_pl := p1; st_evid := i; st_AM_config := ac |} =
    (res(*resultC tt *), {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_evid := i'; st_AM_config := ac' |}) ->
    
    st_pl
      (execErr (build_cvm t)
           {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i; st_AM_config := ac |}) = p1'.
Proof.
  intros.
  destruct (build_cvm t {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i; st_AM_config := ac |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  (* do_asome. *)
  subst.
  dohi.
  df.
  edestruct st_trace_irrel.
  apply H. 

  assert (r = res).
  {
    eapply cvm_errors_deterministic.
    apply Heqp.
    apply H.
  }
  subst.
  
  

  apply Heqp.
  intuition.  
Defined.

(* States that the resulting evidence (st_ev) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_ev : forall t tr1 tr1' tr2 e e' p1' p1 i i' ac ac' res,
    build_cvm t
           {| st_ev := e; st_trace := tr1; st_pl := p1; st_evid := i; st_AM_config := ac |} =
    (res, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_evid := i'; st_AM_config := ac' |}) ->
    
    st_ev
      (execErr (build_cvm t)
           {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i; st_AM_config := ac |}) = e'.
Proof.

intros.
destruct (build_cvm t {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i; st_AM_config := ac |}) eqn:ff.
simpl.
vmsts.
simpl.
(* do_asome. *)
subst.
dohi.
df.
edestruct st_trace_irrel.
apply H. 

assert (r = res).
{
  eapply cvm_errors_deterministic.
  apply Heqp.
  apply H.
}
subst.

apply Heqp.
intuition. 
Defined.

(* States that the resulting event id counter (st_evid) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_evid : forall t tr1 tr1' tr2 e e' p1' p1 i i' ac ac' res,
    build_cvm t
           {| st_ev := e; st_trace := tr1; st_pl := p1; st_evid := i; st_AM_config := ac|} =
    (res, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_evid := i'; st_AM_config := ac' |}) ->
    
    st_evid
      (execErr (build_cvm t)
           {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i; st_AM_config := ac |}) = i'.
Proof.

intros.
destruct (build_cvm t {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i; st_AM_config := ac |}) eqn:ff.
simpl.
vmsts.
simpl.
(* do_asome. *)
subst.
dohi.
df.
edestruct st_trace_irrel.
apply H. 

assert (r = res).
{
  eapply cvm_errors_deterministic.
  apply Heqp.
  apply H.
}
subst.

apply Heqp.
intuition. 
Defined.


(* States that the resulting evidence (st_ev) is unaffected by the initial trace.
   This is a simple corollary of the Lemma hihi above. *)
Lemma trace_irrel_ac : forall t tr1 tr1' tr2 e e' p1' p1 i i' ac ac' res,
    build_cvm t
           {| st_ev := e; st_trace := tr1; st_pl := p1; st_evid := i; st_AM_config := ac |} =
    (res, {| st_ev := e'; st_trace := tr1'; st_pl := p1'; st_evid := i'; st_AM_config := ac' |}) ->
    
    st_AM_config
      (execErr (build_cvm t)
           {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i; st_AM_config := ac |}) = ac'.
Proof.
  intros.
  destruct (build_cvm t {| st_ev := e; st_trace := tr2; st_pl := p1; st_evid := i; st_AM_config := ac |}) eqn:ff.
  simpl.
  vmsts.
  simpl.
  (* do_asome. *)
  subst.
  dohi.
  df.
  edestruct st_trace_irrel.
  apply H. 

  assert (r = res).
  {
    eapply cvm_errors_deterministic.
    apply Heqp.
    apply H.
  }
  subst.

  apply Heqp.
  intuition. 
Defined.

Ltac do_st_trace :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |}]
     |- context[?tr]] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |} )
      tauto
  end.

Ltac do_st_trace_assumps :=
  match goal with
  | [H': context[{| st_ev := ?e; st_trace := ?tr; st_pl := ?p; st_evid := ?i; st_AM_config := ?ac |}]
     |- _] =>
    assert_new_proof_by
      (tr = st_trace {| st_ev := e; st_trace := tr; st_pl := p; st_evid := i; st_AM_config := ac |} )
      tauto
  end.

Ltac find_rw_in_goal :=
  match goal with
  | [H': context[?x = _]
     |- context[?x]] =>
    rewrite H'; clear H'
  end.

Inductive build_cvmP :
  Core_Term -> cvm_st -> (ResultT unit CVM_Error) -> cvm_st ->  Prop :=
| ccp: forall t st st' res,
    build_cvm t st = (res, st') ->
    build_cvmP t st res st'.

Lemma ccp_implies_cc: forall t st st' res,
  build_cvmP t st res st' ->
  build_cvm t st = (res,st').
Proof.
  intros.
  solve_by_inversion.
Defined.

Lemma cc_implies_ccp: forall t st st' res,
  build_cvm t st = (res,st') -> 
  build_cvmP t st res st'.
Proof.
  intros.
  econstructor.
  tauto.
Defined.

Lemma ccp_iff_cc: forall t st st' res,
  build_cvm t st = (res,st') <-> 
  build_cvmP t st res st'.
Proof.
  intros.
  split; intros;
    try (eapply cc_implies_ccp; eauto);
    try (eapply ccp_implies_cc; eauto).
Defined.

Ltac inv_term_coreP :=
  match goal with
  | [H: term_to_coreP _ _ (* ?t (?c _) *)
     |- _ ] =>
    inversion H; subst
  end.

Lemma term_to_coreP_redo: forall t t',
    copland_compile t = t' ->
    term_to_coreP t t'.
Proof.
  intros.
  econstructor.
  eauto.
Defined.

Ltac do_term_to_core_redo :=
  match goal with
  | [H: copland_compile ?t = ?t'
     |- _ ] =>
    eapply term_to_coreP_redo in H
  end.



Lemma annoP_redo: forall t annt n n',
    anno t n = (n', annt) ->
    annoP annt t.
Proof.
  intros.
  econstructor.
  eexists.
  jkjke.
Defined.

Ltac do_anno_redo :=
  match goal with
  | [H: anno ?t ?n = (_,?annt)
     |- _ ] =>
    eapply annoP_redo in H
  end.

Ltac inv_annoP :=
  match goal with
  | [H: annoP _ _ (*_ (?c _) *)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Lemma annoP_indexed_redo: forall t annt n n',
    anno t n = (n', annt) ->
    annoP_indexed annt t n n'.
Proof.
  intros.
  econstructor.
  jkjke.
Defined.

Ltac do_anno_indexed_redo :=
  match goal with
  | [H: anno _ _ = (_,_)
     |- _ ] =>
    eapply annoP_indexed_redo in H
  end.

Ltac inv_annoP_indexed :=
  match goal with
  | [H: annoP_indexed _ _ _ _(*_ (?c _) _*)
     |- _ ] =>
    inversion H; subst
  end;
  destruct_conjs.

Ltac wrap_annopar :=
  inv_term_coreP;
  dd;
  repeat do_term_to_core_redo.

Ltac wrap_anno :=
  inv_annoP;
  dd;
  repeat do_anno_redo.

Ltac wrap_anno_indexed :=
  inv_annoP_indexed;
  dd;
  repeat do_anno_indexed_redo.

Ltac wrap_ccp :=
  
  try rewrite <- ccp_iff_cc in *;
  dd;
  repeat do_pl_immut;
  dd;
  try rewrite ccp_iff_cc in *.

Ltac wrap_ccp_anno :=
  
  try rewrite <- ccp_iff_cc in *;
  try wrap_annopar;
  try wrap_anno;
  try wrap_anno_indexed;
  repeat do_pl_immut;
  try (unfold OptMonad_Coq.ret in * );
  try (unfold OptMonad_Coq.bind in * );
  try (unfold ErrorStMonad_Coq.bind in * );
  try (unfold ErrorStMonad_Coq.ret in * );
  dd;
  try rewrite ccp_iff_cc in *.



Ltac cumul_ih :=
  match goal with
  | [H: context[(st_trace _ = _ ++ st_trace _)],
        H': build_cvmP ?t1 {| st_ev := _; st_trace := ?m ++ ?k; st_pl := _; st_evid := _; st_AM_config := _ |}
                             (?res(*resultC tt*))
                             ?v_full,
            H'': build_cvmP ?t1 {| st_ev := _; st_trace := ?k; st_pl := _; st_evid := _; st_AM_config := _ |}
                                  (?res(*resultC tt*))
                                  ?v_suffix
     |- _] =>
    assert_new_proof_by (st_trace v_full = m ++ st_trace v_suffix) eauto
  end.

Ltac wrap_ccp_dohi :=
  rewrite <- ccp_iff_cc in *;
  dd;
  dohi;
  rewrite ccp_iff_cc in *.

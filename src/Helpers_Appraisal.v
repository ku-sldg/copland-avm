Require Import MonadAM StAM Impl_appraisal AutoApp Auto AllMapped ConcreteEvidence MonadVM Impl_vm Maps External_Facts VmSemantics Appraisal_Defs.

Require Import StructTactics.

Require Import Coq.Program.Tactics.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

Ltac amsts' :=
  repeat match goal with
         | H:AM_St |- _ => destruct H
         end.

Lemma ba_const : forall e a_st a_st' o,
    build_app_comp_ev e a_st = (o, a_st') ->
    am_nonceMap a_st = am_nonceMap a_st' /\
    am_nonceId a_st = am_nonceId a_st' /\
    st_aspmap a_st = st_aspmap a_st' /\
    st_sigmap a_st = st_sigmap a_st'. (*/\
    checked a_st = checked a_st'. *)
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    
    repeat ff;
    try eauto;
    try (unfold am_add_trace in * );
    try (unfold am_checkNonce in * );
    repeat ff; eauto;

      try (edestruct IHe; eauto; tauto);

      try (
          amsts'; ff;
          edestruct IHe1; eauto;
          ff;
          edestruct IHe2; eauto;
          ff; destruct_conjs; ff
        ).
Defined.

Ltac do_ba_st_const :=
  let tac := (eapply ba_const; eauto) in
  repeat (
      match goal with
      | [H: build_app_comp_ev _ ?a_st = (_, ?a0) |- _] =>
        assert_new_proof_by (
            am_nonceMap a_st = am_nonceMap a0 /\
            am_nonceId a_st = am_nonceId a0 /\
            st_aspmap a_st = st_aspmap a0 /\
            st_sigmap a_st = st_sigmap a0) tac
      end);
  subst.

Lemma evmapped_relevant: forall a_st a e,
    am_nonceMap a_st = am_nonceMap a /\
    (*am_nonceId a_st = am_nonceId a /\ *)
    st_aspmap a_st = st_aspmap a /\
    st_sigmap a_st = st_sigmap a ->
    evMapped e a ->
    evMapped e a_st.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    try (econstructor; tauto);
    try (
        evMappedFacts;
        repeat (econstructor; eauto); subst'; eauto).
Defined.

Lemma build_app_some' : forall e a_st a_st',
    (exists o, build_app_comp_ev e a_st = (Some o, a_st')) ->
    evMapped e a_st.
Proof.
  induction e; intros;
    try (
        repeat ff;
        destruct_conjs;
        try solve_by_inversion;
        try (repeat (econstructor; eauto); tauto)
      ).

  
      (*
  -
    econstructor.
  -
    repeat ff;
      
      destruct_conjs;
      try solve_by_inversion;
      try (repeat (econstructor; eauto); tauto).

    +
      ff.
      repeat (econstructor; eauto). subst'; eauto.
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
*)
  - (* nnc case *)
    repeat ff.
    +
      destruct_conjs.
      ff.
      econstructor.
      ++
        tauto.
      ++    
        eauto.
      ++
        unfold am_checkNonce in *.
        repeat ff.
        +++
        eexists.
        econstructor.
        do_ba_st_const.
        destruct_conjs.
        subst'.
        eassumption.
        +++
          eexists.
          econstructor.
          do_ba_st_const.
          destruct_conjs.
          subst'.
          eassumption.
  -
    repeat ff; 
      destruct_conjs;
      ff.

      do_ba_st_const.
    
      econstructor.
      +
        eauto.
      +
        assert (evMapped e2 a) by eauto.
        
        destruct_conjs.

        eapply evmapped_relevant.
        split; eauto.
        eassumption.

  -
    repeat ff; 
      destruct_conjs;
      ff.

    do_ba_st_const.
    
      econstructor.
      +
        eauto.
      +
        assert (evMapped e2 a) by eauto.
        
        destruct_conjs.

        eapply evmapped_relevant.
        split; eauto.
        eassumption. 
Defined.

Ltac dosomeee :=
  match goal with
  | [H: context[forall _, _ -> exists _ _, build_app_comp_ev _ _ = (_,_)] |- _] =>
    edestruct H; eauto
  end;
  destruct_conjs;
  repeat (subst'; df).
(*
  try subst';
  df;
  try subst';
  df. *)
    
Lemma build_app_some : forall e a_st,
    evMapped e a_st ->
    (*Ev_Shape e -> *)
    exists o a_st', build_app_comp_ev e a_st = (Some o, a_st').
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
    evMappedFacts.
    ff.
    dosomeee.
    eauto.
  -
    evMappedFacts.
    ff.
    dosomeee.
    eauto.
  -
    cbn.
    evMappedFacts.
    df.
    unfold am_checkNonce in *.
    do_ba_st_const.
    destruct_conjs.
    subst'.
    clear H1; clear H2; clear H3.
    repeat (ff; eauto).

  -
    cbn.
    evMappedFacts.
    
    assert (exists o a_st', build_app_comp_ev e1 a_st = (Some o, a_st')) by eauto.
    assert (exists o a_st', build_app_comp_ev e2 a_st = (Some o, a_st')) by eauto.
    destruct_conjs.
    cbn.
    df.
    assert (evMapped e2 H5).
    {
      eapply evmapped_relevant.
      do_ba_st_const.
      destruct_conjs.
      split.
      symmetry.
      apply H8.
      
      split; eauto.
      eassumption.
    }
    assert (exists o a_st', build_app_comp_ev e2 H5 = (Some o, a_st')) by eauto.
    destruct_conjs.
    subst'.
    df.
    eauto.

  -
    cbn.
    evMappedFacts.
    assert (exists o a_st', build_app_comp_ev e1 a_st = (Some o, a_st')) by eauto.
    assert (exists o a_st', build_app_comp_ev e2 a_st = (Some o, a_st')) by eauto.
    destruct_conjs.
    cbn.
    df.
    assert (evMapped e2 H5).
    {
      eapply evmapped_relevant.
      do_ba_st_const.
      destruct_conjs.
      split.
      symmetry.
      apply H8.
      
      split; eauto.
      eassumption.
    }
    assert (exists o a_st', build_app_comp_ev e2 H5 = (Some o, a_st')) by eauto.
    destruct_conjs.
    subst'.
    df.
    eauto.
Defined.


Lemma same_ev_shape: forall e et a_st a_st' ec_res,
    Ev_Shape e et -> 
    build_app_comp_ev e a_st = (Some ec_res, a_st') ->
    Ev_Shape ec_res et.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    try (repeat ff; evShapeFacts; eauto).
Defined.

Lemma am_trace_cumul : forall  e e_res
                          nm nm' ni ni' amap amap' smap smap' tr tr' cs cs',
    build_app_comp_ev e {| am_nonceMap := nm;
                           am_nonceId := ni;
                           st_aspmap := amap;
                           st_sigmap := smap;
                           am_st_trace:= tr;
                           checked := cs
                        |}
    = (Some e_res, {| am_nonceMap := nm';
                      am_nonceId := ni';
                      st_aspmap := amap';
                      st_sigmap := smap';
                      am_st_trace:= tr';
                      checked := cs'
                        |}) -> 
    exists tr'', tr' = tr ++ tr''.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros.
  -
    ff.
    exists [].
    rewrite app_nil_r.
    auto.
  -
    repeat ff.
    unfold am_add_trace in *.
    ff.
    edestruct IHe.
    eassumption.
    subst.
    eexists.
    rewrite app_assoc.
    eauto.
  -
    repeat ff.
    unfold am_add_trace in *.
    ff.
    edestruct IHe.
    eassumption.
    subst.
    eexists.
    rewrite app_assoc.
    eauto.
  
  -
    repeat ff;
      amsts';
    unfold am_checkNonce in *;
    repeat ff;
    eauto.

  -
    repeat ff.
    amsts'.
    edestruct IHe1; eauto.
    subst.
    edestruct IHe2; eauto.
    subst.
    eexists.
    rewrite app_assoc.
    eauto.
  -
    repeat ff.
    amsts'.
    edestruct IHe1; eauto.
    subst.
    edestruct IHe2; eauto.
    subst.
    eexists.
    rewrite app_assoc.
    eauto.
Defined.

Lemma mt_sub_all: forall e,
    EvSub mtc e.
Proof.
  induction e; intros;
    (econstructor; eauto; tauto).
Defined.

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
    try (econstructor; eauto);
    tauto.
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
  induction t; intros;
    try do_wf_pieces.
  -
    destruct a; repeat ff;
      try (repeat econstructor; eauto; tauto).
  -
    repeat ff.
    eapply IHt.
    eassumption.
    eapply copland_compile_at.
    eassumption.
    tauto.
    tauto.
  -
    vmsts.
    edestruct alseq_decomp_gen.
    eassumption.
    eassumption.
    destruct_conjs.

    assert (EvSub st_ev0 x) by eauto.
    
    assert (EvSub x st_ev) by eauto.
    eapply evSub_trans; eauto.

  -
    repeat (vmsts; ff).
    destruct s;
      ff;
      econstructor;
      eauto; tauto.

  -
    repeat (vmsts; ff).
    destruct s;
      ff;
      econstructor;
      eauto; tauto.
Defined.

Lemma evMappedSome: forall e1 e2 a_st,
  EvSub e1 e2 ->
  evMapped e2 a_st ->
  evMapped e1 a_st.
Proof.
  induction e2; intros;
    try evMappedFacts;
    do_evsub;
      try (eauto; tauto);
      econstructor;
        try tauto;
        try (eexists; econstructor; eauto).
Defined.

(*
  Lemma evMappedAll: forall e1 a_st a_st',
    evMapped e1 a_st ->
    am_nonceMap a_st = am_nonceMap a_st' ->
    (*am_nonceId a_st = am_nonceId a_st' -> *)
    st_aspmap a_st = st_aspmap a_st' ->
    st_sigmap a_st = st_sigmap a_st' ->
    evMapped e1 a_st'
 *)


Lemma subSome: forall e1 e2 x a_st a_st',
  EvSub e1 e2 ->
  build_app_comp_ev e2 a_st = (Some x, a_st') ->
  exists x' ab_st ab_st', build_app_comp_ev e1 ab_st = (Some x', ab_st').
Proof.
  intros.
  edestruct build_app_some; eauto.
  eapply evMappedSome.
  eassumption.
  eapply build_app_some'; eauto.
Defined.

Lemma hffh: forall e1 e2
              nm ni amap smap tr cs
              nm' ni' amap' smap' x0 cs'
              nm2' ni2' amap2' smap2' tr2 x1 cs2 cs2'
              x_res1 x_res2,
    
    EvSub e1 e2 ->

    build_app_comp_ev e1
                      {|
                        am_nonceMap := nm;
                        am_nonceId := ni;
                        st_aspmap := amap;
                        st_sigmap := smap;
                        am_st_trace := tr;
                        checked := cs |} =
    (Some x_res1,
     {|
       am_nonceMap := nm';
       am_nonceId := ni';
       st_aspmap := amap';
       st_sigmap := smap';
       am_st_trace := tr ++ x0;
       checked := cs' |}) ->

    build_app_comp_ev e2
                      {|
                        am_nonceMap := nm;
                        am_nonceId := ni;
                        st_aspmap := amap;
                        st_sigmap := smap;
                        am_st_trace := tr2;
                        checked := cs2 |} =
    (Some x_res2,
     {|
       am_nonceMap := nm2';
       am_nonceId := ni2';
       st_aspmap := amap2';
       st_sigmap := smap2';
       am_st_trace := tr2 ++ x1;
       checked := cs2' |}) ->

    forall ev, In ev x0 -> In ev x1.
Proof.
  intros.
  generalizeEverythingElse e2.
  induction e2; intros.
  -
    ff.
    inversion H.
    subst.
    ff.
    assert (x0 = []).
    {
      rewrite app_nil_end in H8 at 1.
      eapply app_inv_head.
      symmetry.
      eassumption.
    }
    subst.
    solve_by_inversion.
  -
    repeat ff.
    inversion H.
    +
      repeat ff.
      subst.
      repeat ff.
      amsts'.
      unfold am_add_trace in * .
      invc H3.
      invc H4.
      assert (exists trr, am_st_trace0 = tr ++ trr).
      {
        eapply am_trace_cumul.
        apply Heqp1.
      }
      destruct_conjs.
      subst.
      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul.
        apply Heqp0.
      }
      destruct_conjs.
      subst.

      
      
      assert (H0 ++ [umeas 0 0 n3 (n2 :: l) n0 n1] = x0).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }

      assert (H1 ++ [umeas 0 0 n3 (n2 :: l) n0 n1] = x1).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }

      assert (EvSub e2 e2).
      {
        econstructor.
      }
      

      assert (forall ev, In ev H0 -> In ev H1).
      {
        eapply IHe2.
        eassumption.
        eassumption.
        eassumption.
      }

      rewrite <- H3 in H2.
      apply in_app_or in H2.
      destruct H2.
      assert (In ev H1) by eauto.
      rewrite <- H4.
      apply in_or_app.
      eauto.
      rewrite <- H4.
      apply in_or_app.
      right.
      eauto.
    +
      subst.
      repeat ff.
      unfold am_add_trace in * .
      amsts'.
      invc H4.

      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul.
        eassumption.
      }
      destruct_conjs.
      subst.

      assert (x1 = H1 ++ [umeas 0 0 n3 (n2 :: l) n0 n1]).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }
      subst.
      apply in_or_app.
      left.
      eauto.
  -

    repeat ff.
    inversion H.
    +
      repeat ff.
      subst.
      repeat ff.
      amsts'.
      unfold am_add_trace in * .
      invc H3.
      invc H4.
      assert (exists trr, am_st_trace0 = tr ++ trr).
      {
        eapply am_trace_cumul.
        apply Heqp1.
      }
      destruct_conjs.
      subst.
      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul.
        apply Heqp0.
      }
      destruct_conjs.
      subst.

      
      
      assert (H0 ++ [umeas 0 0 n1 [encodeEv e2; n0] 0 0] = x0).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }

      assert (H1 ++ [umeas 0 0 n1 [encodeEv e2; n0] 0 0] = x1).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }

      assert (EvSub e2 e2).
      {
        econstructor.
      }
      

      assert (forall ev, In ev H0 -> In ev H1).
      {
        eapply IHe2.
        eassumption.
        eassumption.
        eassumption.
      }

      rewrite <- H3 in H2.
      apply in_app_or in H2.
      destruct H2.
      assert (In ev H1) by eauto.
      rewrite <- H4.
      apply in_or_app.
      eauto.
      rewrite <- H4.
      apply in_or_app.
      right.
      eauto.
    +
      subst.
      repeat ff.
      unfold am_add_trace in *.
      amsts'.
      invc H4.

      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul.
        eassumption.
      }
      destruct_conjs.
      subst.

      assert (x1 = H1 ++ [umeas 0 0 n1 [encodeEv e2; n0] 0 0]).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }
      subst.
      apply in_or_app.
      left.
      eauto.

  -

    repeat ff.
    inversion H.
    +
      repeat ff.
      subst.
      repeat ff.
      amsts'.
      unfold am_checkNonce in * .
      ff.
      ff; try solve_by_inversion.
      ++
        subst.
        assert (forall ev, In ev x0 -> In ev x1).
        {
          eapply IHe2.
          econstructor.
          eassumption.
          eassumption.
        }
        eauto.
      ++
        subst.
        assert (forall ev, In ev x0 -> In ev x1).
        {
          eapply IHe2.
          econstructor.
          eassumption.
          eassumption.
        }
        eauto.
      ++
        subst.
        assert (forall ev, In ev x0 -> In ev x1).
        {
          eapply IHe2.
          econstructor.
          eassumption.
          eassumption.
        }
        eauto.
      ++
        subst.
        assert (forall ev, In ev x0 -> In ev x1).
        {
          eapply IHe2.
          econstructor.
          eassumption.
          eassumption.
        }
        eauto.
    +
      subst.
      repeat ff.
      subst.
      repeat ff.
      amsts'.
      unfold am_checkNonce in *.
      ff.
      ff; try solve_by_inversion.
      ++
        subst.
        assert (forall ev, In ev x0 -> In ev x1).
        {
          eapply IHe2.
          eassumption.
          eassumption.
          eassumption.
        }
        eauto.
      ++
        subst.
        assert (forall ev, In ev x0 -> In ev x1).
        {
          eapply IHe2.
          eassumption.
          eassumption.
          eassumption.
        }
        eauto.
  -
    repeat ff.
    invc H.
    +
      repeat ff.
      amsts'.
      repeat ff.

      assert (exists trr, tr ++ x0 = am_st_trace0 ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, tr2 ++ x1 = am_st_trace ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, am_st_trace0 = tr ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }
      destruct_conjs.
      subst.

      assert (x1 = H1 ++ H0).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }
      
      assert (x0 = H3 ++ H).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }

      rewrite H4.
      rewrite H5 in H2.
      (*
      clear H4; clear H5.
      clear H7; clear H6. *)

      assert (forall ev, In ev H3 -> In ev H1).
      {
        eapply IHe2_1.
        econstructor.
        eassumption.
        eassumption.
      }
      
      apply in_app_or in H2.
      destruct H2.
      ++
        apply in_or_app.
        left.
        eapply IHe2_1.
        econstructor.
        eassumption.
        eassumption.
        eauto.
      ++
        rewrite H5 in Heqp2.
        rewrite H4 in Heqp0.

        assert (forall ev, In ev H -> In ev H0).
        {
          eapply IHe2_2.
          econstructor.
          rewrite app_assoc in Heqp2.
          rewrite app_assoc in Heqp0.
          eassumption.

          assert (am_nonceMap = am_nonceMap0 /\ am_nonceId = am_nonceId0 /\ st_aspmap = st_aspmap0
                  /\ st_sigmap = st_sigmap0).
          {
            do_ba_st_const.
            simpl in *.
            destruct_conjs.
            subst.
            tauto.
          }
          destruct_conjs.
          subst.
          rewrite app_assoc in Heqp0.
          apply Heqp0.
        }
        apply in_or_app.
        eauto.
    +
      amsts'.
      repeat ff.

      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, tr2 ++ x1  = am_st_trace ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }
      destruct_conjs.
      subst.

      assert (x1 = H ++ H1).
      {
        repeat (rewrite <- app_assoc in * );  
          eapply app_inv_head; eauto.
      }
      subst.
       
      assert (forall ev, In ev x0 -> In ev H).
      {
        eapply IHe2_1.
        eassumption.
        eassumption.
        eassumption.
      }
      apply in_or_app.
      eauto.
    +
      amsts'.
      repeat ff.

      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, tr2 ++ x1  = am_st_trace ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }
      destruct_conjs.
      subst.

      assert (x1 = H ++ H1).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }
      subst.

      assert (am_nonceMap = nm /\ am_nonceId = ni /\ st_aspmap = amap /\ st_sigmap = smap).
      {
        do_ba_st_const.
        simpl in *.
        destruct_conjs.
        subst.
        tauto.
      }
      destruct_conjs.
      subst.
      
      assert (forall ev, In ev x0 -> In ev H1).
      {
        eapply IHe2_2.
        eassumption.
        eassumption.
        rewrite app_assoc in Heqp0.
        eassumption.
      }
      apply in_or_app.
      eauto.
  -
    repeat ff.
    invc H.
    +
      repeat ff.
      amsts'.
      repeat ff.

      assert (exists trr, tr ++ x0 = am_st_trace0 ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, tr2 ++ x1 = am_st_trace ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, am_st_trace0 = tr ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }
      destruct_conjs.
      subst.

      assert (x1 = H1 ++ H0).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }
      
      assert (x0 = H3 ++ H).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }

      rewrite H4.
      rewrite H5 in H2.
      (*
      clear H4; clear H5.
      clear H7; clear H6. *)

      assert (forall ev, In ev H3 -> In ev H1).
      {
        eapply IHe2_1.
        econstructor.
        eassumption.
        eassumption.
      }
      

      apply in_app_or in H2.
      destruct H2.
      ++
        apply in_or_app.
        left.
        eapply IHe2_1.
        econstructor.
        eassumption.
        eassumption.
        eauto.
      ++
        rewrite H5 in Heqp2.
        rewrite H4 in Heqp0.

        assert (forall ev, In ev H -> In ev H0).
        {
          eapply IHe2_2.
          econstructor.
          rewrite app_assoc in Heqp2.
          rewrite app_assoc in Heqp0.
          eassumption.

          assert (am_nonceMap = am_nonceMap0 /\ am_nonceId = am_nonceId0 /\
                  st_aspmap = st_aspmap0 /\ st_sigmap = st_sigmap0).
          {
            do_ba_st_const.
            simpl in *.
            destruct_conjs.
            subst.
            tauto.
          }
          destruct_conjs.
          subst.
          rewrite app_assoc in Heqp0.
          apply Heqp0.
        }
        apply in_or_app.
        eauto.
    +
      amsts'.
      repeat ff.

      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, tr2 ++ x1  = am_st_trace ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }
      destruct_conjs.
      subst.

      assert (x1 = H ++ H1).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }
      subst.
      

      
      assert (forall ev, In ev x0 -> In ev H).
      {
        eapply IHe2_1.
        eassumption.
        eassumption.
        eassumption.
      }
      apply in_or_app.
      eauto.
    +
      amsts'.
      repeat ff.

      assert (exists trr, am_st_trace = tr2 ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }

      assert (exists trr, tr2 ++ x1  = am_st_trace ++ trr).
      {
        eapply am_trace_cumul; eauto.
      }
      destruct_conjs.
      subst.

      assert (x1 = H ++ H1).
      {
        repeat (rewrite <- app_assoc in * ); 
          eapply app_inv_head; eauto.
      }
      subst.

      assert (am_nonceMap = nm /\ am_nonceId = ni /\ st_aspmap = amap /\ st_sigmap = smap).
      {
        do_ba_st_const.
        simpl in *.
        destruct_conjs.
        subst.
        tauto.
      }
      destruct_conjs.
      subst.

      assert (forall ev, In ev x0 -> In ev H1).
      {
        eapply IHe2_2.
        eassumption.
        eassumption.
        rewrite app_assoc in Heqp0.
        eassumption.
      }
      apply in_or_app.
      eauto.
Defined.

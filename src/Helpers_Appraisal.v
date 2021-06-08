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
    st_sigmap a_st = st_sigmap a_st' /\
    st_hshmap a_st = st_hshmap a_st'.

                               (*/\
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
            st_sigmap a_st = st_sigmap a0 /\
            st_hshmap a_st = st_hshmap a0
          ) tac
      end);
  subst.

(*
Ltac hshMappedFacts :=
  match goal with
  | [H: hshMapped (?C _) _ |- _] => invc H
  end;
  destruct_conjs;
  try debound.

Lemma hshMapped_relevant: forall a_st a e,
    (*
    am_nonceMap a_st = am_nonceMap a /\
    (*am_nonceId a_st = am_nonceId a /\ *)
    st_aspmap a_st = st_aspmap a /\
    st_sigmap a_st = st_sigmap a /\ *)
    st_hshmap a_st = st_hshmap a ->
    hshMapped e a ->
    hshMapped e a_st.
Proof.
  intros.
  generalizeEverythingElse e.
  induction e; intros;
    try (econstructor; tauto);
    try (
        hshMappedFacts;
        repeat (econstructor; eauto); subst'; eauto).
Defined.
*)


Lemma evmapped_relevant: forall a_st a e,
    am_nonceMap a_st = am_nonceMap a /\
    (*am_nonceId a_st = am_nonceId a /\ *)
    st_aspmap a_st = st_aspmap a /\
    st_sigmap a_st = st_sigmap a /\
    st_hshmap a_st = st_hshmap a ->
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

  (*
  - (* hsh case *)
    econstructor.
    evMappedFacts.
    amsts'.
    df.
    repeat subst'.
    eapply hshMapped_relevant.
    2: {
      eassumption.
    }
    ff. *)
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
  - (* hhc case *)
    repeat ff.
    amsts'.
    df.
    econstructor.

    HEREEEE


    
    admit.
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
    evMappedFacts.
    ff.
    eauto.
  -
    cbn.
    evMappedFacts.
    df.
    unfold am_checkNonce in *.
    do_ba_st_const.
    destruct_conjs.
    subst'.
    clear H1; clear H2; clear H3; clear H4.
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
                          nm nm' ni ni' amap amap' smap smap' hmap hmap' tr tr' cs cs',
    build_app_comp_ev e {| am_nonceMap := nm;
                           am_nonceId := ni;
                           st_aspmap := amap;
                           st_sigmap := smap;
                           st_hshmap := hmap;
                           am_st_trace:= tr;
                           checked := cs
                        |}
    = (Some e_res, {| am_nonceMap := nm';
                      am_nonceId := ni';
                      st_aspmap := amap';
                      st_sigmap := smap';
                      st_hshmap := hmap';
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
    invc H1.
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
    invc H1.
    edestruct IHe.
    eassumption.
    subst.
    eexists.
    rewrite app_assoc.
    eauto.
  -
    repeat ff;
      amsts';
    repeat ff;
    eauto.
    (*
    exists [].
    rewrite app_nil_r.
    eauto. *)
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

Lemma mt_subT_all: forall e,
    EvSubT mt e.
Proof.
    induction e; intros;
    try
      (econstructor; eauto; tauto).
Defined.

  

Lemma mt_sub_all: forall e,
    EvSub mtc e.
Proof.
  induction e; intros;
    try
      (econstructor; eauto; tauto).
  - (* hhc case *)
    econstructor.
    ff.
    apply mt_subT_all.
Defined.

Ltac do_evsub :=
  match goal with
  | [H: EvSub _ (?C) |- _] => invc H
  end.

Ltac do_evsubT :=
  match goal with
  | [H: EvSubT _ (?C) |- _] => invc H
  end.

Lemma evSubT_trans: forall e' e e'',
  EvSubT e e' ->
  EvSubT e' e'' ->
  EvSubT e e''.
Proof.
  induction e''; intros;
    try (
        do_evsubT;
        try solve_by_inversion;
        try (econstructor; eauto);
        tauto).
Defined.

Lemma esub_esubt: forall e e',
    EvSub e e' ->
    EvSubT (et_fun e) (et_fun e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros.
  -
    do_evsub.
    econstructor.
  -
    do_evsub.
    ff.
    econstructor.
    econstructor. eauto.
  -
    do_evsub.
    ff.
    econstructor.
    ff.
    econstructor.
    eauto.
  -
    do_evsub.
    ff.
    econstructor.
    econstructor. eauto.
  -
    do_evsub.
    ff.
    econstructor.
    econstructor. eauto.
  -
    do_evsub.
    econstructor; eauto.
    econstructor; eauto.
    apply ssSubrT.
    eauto.
  -
    do_evsub.
    econstructor; eauto.
    econstructor; eauto.
    apply ppSubrT.
    eauto.
Defined.

    
Lemma evSub_trans: forall e' e e'',
  EvSub e e' ->
  EvSub e' e'' ->
  EvSub e e''.
Proof.
  induction e''; intros;
    try (
    do_evsub;
    try solve_by_inversion;
    try (econstructor; eauto);
    tauto).
  -
    do_evsub; eauto.
    +
      econstructor.
      eapply evSubT_trans.
      Focus 2.
      eassumption.
      apply esub_esubt; eauto.
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
    edestruct alseq_decomp_gen;
    eauto.
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
    try (
    do_evsub;
      try (eauto; tauto);
      econstructor;
        try tauto;
        try (eexists; econstructor; eauto); tauto).
  -
    invc H.
    +
      econstructor.
    +
Abort.

(*
  Lemma evMappedAll: forall e1 a_st a_st',
    evMapped e1 a_st ->
    am_nonceMap a_st = am_nonceMap a_st' ->
    (*am_nonceId a_st = am_nonceId a_st' -> *)
    st_aspmap a_st = st_aspmap a_st' ->
    st_sigmap a_st = st_sigmap a_st' ->
    evMapped e1 a_st'
 *)


(*
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
*)


Ltac do_cumul_app :=
  repeat 
    match goal with
    | [H: build_app_comp_ev _
          {|
            am_nonceMap := _;
            am_nonceId := _;
            st_aspmap := _;
            st_sigmap := _;
            am_st_trace := ?tr;
            checked := _ |} =
          (Some _,
           {|
             am_nonceMap := _;
             am_nonceId := _;
             st_aspmap := _;
             st_sigmap := _;
             am_st_trace := ?tr2;
             checked := _ |})
       |- _] =>
      assert_new_proof_by (exists trr, tr2 = tr ++ trr)
                          ltac:(eapply am_trace_cumul; eauto)
                                                          
    end;
  destruct_conjs; subst.

Ltac do_inv_head' :=
  repeat (rewrite <- app_assoc in * );
  let tac := symmetry; eapply app_inv_head; eauto in
  repeat
    match goal with
    | H:?ls ++ ?xs = ?ls ++ ?ys |- _ => assert_new_proof_by (ys = xs) tac
    end.

Ltac do_evsub_refl :=
  let tac := econstructor in
  repeat
    match goal with
    | [e:EvidenceC

       |- _ ] =>
      assert_new_proof_by (EvSub e e) tac
    end.

Ltac do_inor :=
  let tac := econstructor in
  match goal with
  | [H: In _ (_ ++ _) |- _ ] =>
    apply in_app_or in H;
    destruct H
  end.

Ltac do_cumul_app_ih :=
        repeat 
    match goal with
    | [H: build_app_comp_ev _
          {|
            am_nonceMap := _;
            am_nonceId := _;
            st_aspmap := _;
            st_sigmap := _;
            am_st_trace := ?tr;
            checked := _ |} =
          (Some _,
           {|
             am_nonceMap := _;
             am_nonceId := _;
             st_aspmap := _;
             st_sigmap := _;
             am_st_trace := ?tr ++ ?tr';
             checked := _ |}),
          H': build_app_comp_ev _
           {|
             am_nonceMap := _;
             am_nonceId := _;
             st_aspmap := _;
             st_sigmap := _;
             am_st_trace := ?tr2;
             checked := _ |} =
              (Some _,
               {|
                 am_nonceMap := _;
                 am_nonceId := _;
                 st_aspmap := _;
                 st_sigmap := _;
                 am_st_trace := ?tr2 ++ ?tr2';
                                checked := _ |}),
              IH: context [_ -> _]
       |- _] =>
      assert_new_proof_by (forall ev, In ev tr' -> In ev tr2' )
                          ltac:(eapply IH; eauto)
      end;
  destruct_conjs; subst.

Lemma app_evSub: forall e1 e2
              nm ni amap smap hmap tr cs
              nm' ni' amap' smap' hmap' x0 cs'
              nm2' ni2' amap2' smap2' hmap2' tr2 x1 cs2 cs2'
              x_res1 x_res2,
    
    EvSub e1 e2 ->

    build_app_comp_ev e1
                      {|
                        am_nonceMap := nm;
                        am_nonceId := ni;
                        st_aspmap := amap;
                        st_sigmap := smap;
                        st_hshmap := hmap;
                        am_st_trace := tr;
                        checked := cs |} =
    (Some x_res1,
     {|
       am_nonceMap := nm';
       am_nonceId := ni';
       st_aspmap := amap';
       st_sigmap := smap';
       st_hshmap := hmap';
       am_st_trace := tr ++ x0;
       checked := cs' |}) ->

    build_app_comp_ev e2
                      {|
                        am_nonceMap := nm;
                        am_nonceId := ni;
                        st_aspmap := amap;
                        st_sigmap := smap;
                        st_hshmap := hmap;
                        am_st_trace := tr2;
                        checked := cs2 |} =
    (Some x_res2,
     {|
       am_nonceMap := nm2';
       am_nonceId := ni2';
       st_aspmap := amap2';
       st_sigmap := smap2';
       st_hshmap := hmap2';
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
      rewrite app_nil_end in H9 at 1.
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
      unfold am_add_trace in *.
      invc H3.
      invc H4.

      do_cumul_app.
      do_inv_head'.
      subst.
      do_evsub_refl.

      do_cumul_app_ih.
      do_inor.

      apply in_or_app; eauto.
      apply in_or_app; eauto.
    +
      subst.
      repeat ff.
      unfold am_add_trace in * .
      amsts'.
      invc H4.
      do_cumul_app.
      do_inv_head'.
      subst.
      apply in_or_app; eauto.
  -
    repeat ff.
    inversion H.
    +
      repeat ff.
      subst.
      repeat ff.
      amsts'.
      unfold am_add_trace in *.
      invc H3.
      invc H4.

      do_cumul_app.
      do_inv_head'.
      subst.
      do_evsub_refl.
      do_cumul_app_ih.
      do_inor.

      apply in_or_app; eauto.
      apply in_or_app; eauto.
        +
      subst.
      repeat ff.
      unfold am_add_trace in * .
      amsts'.
      invc H4.
      do_cumul_app.
      do_inv_head'.
      subst.
      apply in_or_app; eauto.
  -
    repeat ff.
    inversion H.
    +
      repeat ff.
      subst.
      repeat ff.
      assert (x0 = []).
      {
        rewrite app_nil_end in H9 at 1.
        eapply app_inv_head.
        symmetry.
        eassumption.
      }
      subst.
      solve_by_inversion.
    +
      repeat ff.
      subst.
      repeat ff.
      




      
      amsts'.
      unfold am_add_trace in *.
      invc H3.
      invc H4.

      do_cumul_app.
      do_inv_head'.
      subst.
      do_evsub_refl.
      do_cumul_app_ih.
      do_inor.

      apply in_or_app; eauto.
      apply in_or_app; eauto.
        +
      subst.
      repeat ff.
      unfold am_add_trace in * .
      amsts'.
      invc H4.
      do_cumul_app.
      do_inv_head'.
      subst.
      apply in_or_app; eauto.
    


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
      ff; try solve_by_inversion;
        subst;
        do_evsub_refl;
        do_cumul_app_ih; eauto.

    +
      repeat (subst; ff).
      amsts'.
      unfold am_checkNonce in *.
      repeat ff; try solve_by_inversion;
        subst;
        do_cumul_app_ih; eauto.
  -
    repeat ff.
    invc H.
    +
      repeat ff; amsts'; repeat ff.

      do_cumul_app.

      do_inv_head'.

      subst.

      assert (forall ev, In ev H3 -> In ev H0).
      {
        eapply IHe2_1.
        econstructor.
        eassumption.
        eassumption.
      }

      do_ba_st_const.
      ff.
      destruct_conjs.
      subst.

      rewrite app_assoc in *.

      
      assert (forall ev, In ev H1 -> In ev H).
      {
        eapply IHe2_2.
        econstructor.
        eassumption.
        eassumption.
      }

      do_inor;
        apply in_or_app; eauto.

    +
      amsts'.
      repeat ff.

      do_cumul_app.

      do_inv_head'.

      subst.

      do_cumul_app_ih.

      apply in_or_app.
      eauto.
    +
      amsts'.
      repeat ff.

      do_cumul_app.

      do_inv_head'.

      subst.

      do_ba_st_const.

      destruct_conjs.
      ff.
      subst.

      rewrite app_assoc in *.
      do_cumul_app_ih.

      apply in_or_app.
      eauto.
  -
    repeat ff.
    invc H.
    +
      repeat ff; amsts'; repeat ff.

      do_cumul_app.

      do_inv_head'.

      subst.

      assert (forall ev, In ev H3 -> In ev H0).
      {
        eapply IHe2_1.
        econstructor.
        eassumption.
        eassumption.
      }

      do_ba_st_const.
      ff.
      destruct_conjs.
      subst.

      rewrite app_assoc in *.

      
      assert (forall ev, In ev H1 -> In ev H).
      {
        eapply IHe2_2.
        econstructor.
        eassumption.
        eassumption.
      }

      do_inor;
        apply in_or_app; eauto.

    +
      amsts'.
      repeat ff.

      do_cumul_app.

      do_inv_head'.

      subst.

      do_cumul_app_ih.

      apply in_or_app.
      eauto.
    +
      amsts'.
      repeat ff.

      do_cumul_app.

      do_inv_head'.

      subst.

      do_ba_st_const.

      destruct_conjs.
      ff.
      subst.

      rewrite app_assoc in *.
      do_cumul_app_ih.

      apply in_or_app.
      eauto.
Defined.

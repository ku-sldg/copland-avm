Require Import GenStMonad MonadVM MonadAM ConcreteEvidence.
Require Import StAM Axioms_Io Impl_vm Impl_appraisal Maps VmSemantics Event_system Term_system External_Facts Helpers_VmSemantics.
Require Import Auto AutoApp AllMapped Appraisal_Defs Helpers_Appraisal.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Lemma appraisal_correct : forall t ev1 tr1 p e_res tr1' p'
                            nm nm' ni ni' amap amap' smap smap' tr tr' cs cs'
                            app_res
                            e ev,
    well_formed_r t ->
    copland_compile t
                    {| st_ev := ev1; st_trace := tr1; st_pl := p |} =
    (Some tt, {| st_ev := e_res; st_trace := tr1'; st_pl := p' |}) ->

    build_app_comp_ev e_res {| am_nonceMap := nm;
                               am_nonceId := ni;
                               st_aspmap := amap;
                               st_sigmap := smap;
                               am_st_trace:= tr;
                               checked := cs
                            |} = (Some app_res,  {| am_nonceMap := nm';
                                                    am_nonceId := ni';
                                                    st_aspmap := amap';
                                                    st_sigmap := smap';
                                                    am_st_trace:= tr';
                                                    checked := cs'
                                                 |}) ->

    measEvent t p e ev ->
    exists ev', In ev' tr' /\ appEvent ev {| am_nonceMap := nm;
                                       am_nonceId := ni;
                                       st_aspmap := amap;
                                       st_sigmap := smap;
                                       am_st_trace:= tr;
                                       checked := cs
                                    |} ev'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    measEventFacts.
    evEventFacts.
    invEvents.
    unfold empty_vmst in *.
    amsts'.
    vmsts.
    repeat ff.
    
    eexists.
    split.
    amsts'.
    ff.
    2: {
      econstructor.
      reflexivity.
      ff.
      econstructor.
      eassumption.
    }
    simpl.
    eapply in_or_app.
    right.
    econstructor.
    tauto.
  -
    measEventFacts.
    evEventFacts.
    invEvents.
    unfold empty_vmst in *.
    amsts.
    vmsts.
    ff.
    do_wf_pieces.
    edestruct IHt.
    eassumption.
    eapply copland_compile_at.
    eassumption.
    eassumption.
    
    econstructor.
    eassumption.
    econstructor.
    eauto.
  -
    do_wf_pieces.
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.
    amsts'.
    ff.
    amsts'.

    unfold empty_amst in *.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.

    assert (evMapped e_res
                     {|
                       am_nonceMap := nm;
                       am_nonceId := ni;
                       st_aspmap := amap;
                       st_sigmap := smap;
                       am_st_trace := tr;
                       checked := cs |}).
    {
      eapply build_app_some'.
      eauto.
    }

    assert (EvSub st_ev e_res).
    {
      eapply evAccum.
      eauto.
      eauto.
      eauto.
      eauto.
    }

    assert (evMapped st_ev
                     {|
                       am_nonceMap := nm;
                       am_nonceId := ni;
                       st_aspmap := amap;
                       st_sigmap := smap;
                       am_st_trace := tr;
                       checked := cs |}).
    {
      eapply evMappedSome.
      eassumption.
      eassumption.
    }
    edestruct build_app_some.
    apply H7.
    destruct_conjs.
    amsts'.

    edestruct am_trace_cumul.
    apply H9.
    subst.
    edestruct am_trace_cumul.
    apply H1.
    subst.


    assert (forall ev, In ev x0 -> In ev x1).
    {
      eapply hffh; eauto.

    }

    inv_events;
      unfold runSt in *.
    
    + (* t1 case *)
      amsts'.
      edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      econstructor.
      eassumption.
      eassumption.

      destruct_conjs.
      exists x2.
      split.
      apply in_app_or in H10.
      destruct H10.


      apply in_or_app.
      eauto.
      eauto.
      eapply in_or_app.
      right.
      eauto.
      eassumption.

    + (* t2 case *)
      amsts'.
      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      econstructor.
      eassumption.
      eassumption.
      destruct_conjs.
      exists x2.
      eauto.
      
  -
    do_wf_pieces.
    repeat ff.
    vmsts.
    repeat ff.
    amsts'.

    edestruct am_trace_cumul; eauto.
    subst.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    inv_events;
      unfold runSt in *;
      try solve_by_inversion.
    
    + (* t1 case *)
      assert (exists ev', In ev' am_st_trace /\
                     appEvent ev
                              {|
                                am_nonceMap := nm;
                                am_nonceId := ni;
                                st_aspmap := amap;
                                st_sigmap := smap;
                                am_st_trace := tr;
                                checked := cs |} ev').
      eapply IHt1.
      eassumption.
      eassumption.
      eassumption.
      econstructor.
      eassumption.
      eassumption.
      destruct_conjs.
      exists H2.
      split.
      apply in_or_app.
      eauto.
      eassumption.
      
    + (* t2 case *)
      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      econstructor.
      eassumption.
      eassumption.
      destruct_conjs.

      exists x0.
      split; eauto.

      assert (nm = am_nonceMap /\ ni = am_nonceId /\ amap = st_aspmap /\ smap = st_sigmap).
      {
        edestruct ba_const.
        apply Heqp0.
        destruct_conjs.
        ff.
      }

      destruct_conjs.
      subst.
      invc H5.
      ff.

      econstructor.
      reflexivity.
      ff.
  -
    do_wf_pieces.
    repeat ff.
    vmsts.
    repeat ff.
    amsts'.
    repeat ff.

    edestruct am_trace_cumul; eauto.
    subst.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    inv_events;
      unfold runSt in *;
      try solve_by_inversion.
    
    + (* t1 case *)
      assert (exists ev', In ev' am_st_trace /\
                     appEvent ev
                              {|
                                am_nonceMap := nm;
                                am_nonceId := ni;
                                st_aspmap := amap;
                                st_sigmap := smap;
                                am_st_trace := tr;
                                checked := cs |} ev').
      eapply IHt1.
      eassumption.
      eassumption.
      eassumption.
      econstructor.
      eassumption.
      eassumption.
      destruct_conjs.
      exists H2.
      split.
      apply in_or_app.
      eauto.
      eassumption.
      
    + (* t2 case *)
      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      econstructor.
      eassumption.
      eassumption.
      destruct_conjs.

      exists x0.
      split; eauto.

      assert (nm = am_nonceMap /\ ni = am_nonceId /\ amap = st_aspmap /\ smap = st_sigmap).
      {
        edestruct ba_const.
        apply Heqp0.
        destruct_conjs.
        ff.
      }

      destruct_conjs.
      subst.
      invc H5.
      ff.

      econstructor.
      reflexivity.
      ff.
Defined.

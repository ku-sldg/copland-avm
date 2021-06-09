Require Import GenStMonad MonadVM MonadAM ConcreteEvidence.
Require Import StAM Axioms_Io Impl_vm Impl_appraisal Maps VmSemantics Event_system Term_system External_Facts Helpers_VmSemantics.
Require Import Auto AutoApp AllMapped Appraisal_Defs Helpers_Appraisal.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Lemma appraisal_correct : forall t ev1 tr1 p e_res tr1' p'
                            nm nm' ni ni' amap amap' smap smap' hmap hmap' tr tr' cs cs'
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
                               st_hshmap := hmap;
                               am_st_trace:= tr;
                               checked := cs
                            |} = (Some app_res,  {| am_nonceMap := nm';
                                                    am_nonceId := ni';
                                                    st_aspmap := amap';
                                                    st_sigmap := smap';
                                                    st_hshmap := hmap';
                                                    am_st_trace:= tr ++ tr';
                                                    checked := cs'
                                                 |}) ->
   (* Ev_Shape ev1 e -> *)

    measEvent t p e ev ->
    exists ev', In ev' tr' /\ appEvent ev {| am_nonceMap := nm;
                                       am_nonceId := ni;
                                       st_aspmap := amap;
                                       st_sigmap := smap;
                                       st_hshmap := hmap;
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
    unfold am_add_trace in *.
    repeat ff.
    invc H2.

    do_cumul_app.
    do_inv_head'.
    subst.
    clear H7.
    
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
    2: {
    
    econstructor.
    eassumption.
    }
    econstructor.
    eauto.
    econstructor.

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

    (*

    assert (evMapped e_res
                     {|
                       am_nonceMap := nm;
                       am_nonceId := ni;
                       st_aspmap := amap;
                       st_sigmap := smap;
                       st_hshmap := hmap;
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
                       st_hshmap := hmap;
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
    subst. *)


    (*
    assert (forall ev, In ev x0 -> In ev x1).
    {
      eapply app_evSub; eauto.

    } *)

     assert (EvSub st_ev e_res).
    {
      eapply evAccum.
      eauto.
      eauto.
      eauto.
      eauto.
    }

    Check build_app_some.
    Check evMappedSome.

    edestruct build_app_some.
    eapply evMappedSome.
    eassumption.
    eapply build_app_some'.
    eauto.
    
(*
    edestruct subSome.
    apply H2.
    eassumption.
 *)
    

    destruct_conjs.
    amsts'.

    

    edestruct am_trace_cumul.
    apply H7.
    (*
    edestruct am_trace_cumul.
    apply H1. *)
    subst.

    
(*
    assert (
        forall n p i args tpl tid,
      In (umeas n p i args tpl tid) x0 ->
      (In (umeas n p i args tpl tid) tr' \/
       (exists n' p' args' tpl' tid' e e',
           In (umeas n' p' 1 ([hashEvT e] ++ args') tpl' tid') tr' /\
           EvSubT (uu i args tpl tid e') e))).



    
(*
         assert (    forall ev, In ev x0 ->
          (In ev x1 \/ (exists n p i args tpl tid, ev = (umeas n p i args tpl tid) /\ (exists n' p' args' tpl' tid' e e', In (umeas n' p' 1 ([hashEvT e] ++ args') tpl' tid') x1 /\
                                                                                                              EvSubT (uu i args tpl tid e') e)))). *)
        {
          eapply app_evSub.
          eassumption.
          eassumption.
          eassumption.
        }
 *)
    assert (forall ev, In ev x0 -> In ev tr').
    {
      eapply app_evSub.
      eauto.
      eauto.
      eassumption.
      eassumption.
    }
    

    inv_events;
          unfold runSt in *.







    (*
    eapply evAccum.
    apply H3.
    eassumption.
    tauto.
    tauto.
    ff.
    
    eassumption. *)




    
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
      invc H5.

      invc H9.
      ++
        specialize (H6 (umeas n' p' i' ([n] ++ args) tpl' tid')).
        concludes.
        eexists.
        split.
        eassumption.
        econstructor.
        tauto.
        eassumption.
      ++
        specialize (H6 (umeas n0 p1 1 ([hashEvT e0] ++ args0) tpl0 tid0)).
        concludes.
        eexists.
        split.
        eassumption.
        eapply ahu.
        eassumption.

    + (* t1 case *)

      amsts'.
      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      econstructor.
      eassumption.
      eassumption.

      
      destruct_conjs.
      invc H5.

      invc H9.
      ++
        (*
        specialize (H6 (umeas n' p' i' ([n] ++ args) tpl tid)).
        concludes. *)
        eexists.
        split.
        eassumption.
        econstructor.
        tauto.
        eassumption.
      ++
        (*
        specialize (H6 (umeas n0 p1 1 ([hashEvT e0] ++ args0) tpl0 tid0)).
        concludes. *)
        eexists.
        split.
        eassumption.
        eapply ahu.
        eassumption.







        
      
        
        




      

      eexists.
      split.
      apply H6.
      eassumption.


      

      invc H9.
      ++

        specialize (H6 n' p' i' ([n] ++ args) tpl tid).
        concludes.
        destruct H6.
        +++
          eexists.
          split.
          eassumption.
          econstructor.
          eauto.
          eauto.
        +++
          destruct_conjs.
          eexists.
          split.
          eassumption.
          eapply ahu.
          
      



      
      apply in_app_or in H6.
      destruct H6.
      ++
       exists x2.
        split.
        apply in_or_app.
        eauto.
        eassumption.
      ++

        invc H9.
        +++
          pose (H7 n p0 i args tpl tid).
          concludes.
          destruct o.
          ++++
            eexists.
            split.
            apply in_or_app.
            right.
            apply H9.
            econstructor.
            tauto.
            eassumption.
          ++++
            destruct_conjs.
            eexists.
            split.
            apply in_or_app.
            right.
            eassumption.
            

        pose (H7 n p0 i args tpl tid).
        

      apply in_app_or in H5.
      destruct H5.
      ++
        exists x2.
        split.
        apply in_or_app.
        eauto.
        eassumption.
      ++
        concludes.
        destruct o.
        +++
          eexists.
          split.
          apply in_or_app.
          right.
          apply H9.
          eassumption.
        +++
          destruct_conjs.
          subst.
          pose (H6  (umeas H9 H10 H11 H12 H14 H15)).
          concludes.

          invc H8.
          ++++




          
          destruct o.
          ++++


          
          invc H8.
          ++++
          

          
        


      invc H8.
      ++ (* aeu case of appEvent *)
        apply in_app_or in H5.
        destruct H5.
        +++
          eexists.
          split.
          eapply in_or_app.
          left.
          apply H5.
          econstructor.
          tauto.
          eassumption.
        +++
          pose (H6  (umeas n' p' i' ([n] ++ args) tpl tid)).
          concludes.
          destruct o.
          ++++
            eexists.
            split.
            apply in_or_app.
            eauto.
            econstructor.
            tauto.
            eassumption.
          ++++
            destruct_conjs.
            invc H15.
            
          
        






      
(*
      invc H8.
      ++
        df.

        apply in_app_or in H6.
        destruct H6.
        +++
          df.
          eexists.
          split.
          apply in_or_app.
          eauto.
          econstructor.
          eauto.
          eauto.
        +++ *)
          
          



      

      apply in_app_or in H6.
      destruct H6.
      ++
        exists x2.
        split.
        +++
        apply in_or_app.
        eauto.
        +++
          eassumption.
      ++

       

        pose (H9 x2).
        concludes.
        destruct o.
        +++
          exists x2.
          split.
          apply in_or_app.
          eauto.
          eauto.
        +++
          destruct_conjs.
          invc H8.
          ++++
          invc H31.
          exists (umeas H18 H19 1 ([hashEvT H23] ++ H20) H21 H22).
          split.
          apply in_or_app.
          eauto.
          eapply ahu.
          eassumption.
          eassumption.
          

        
        exists x2.
        split.
        apply in_or_app.
        eauto.
        eassumption.
        destruct_conjs.

        invc H8.
        +++
          invc H30.

        exists (umeas H17 H18 1 ([hashEvT H22] ++ H19) H20 H21).
        split.
        apply in_or_app.
        eauto.
        eapply ahu.
        invc H30.
        eassumption.


        
        eauto.

        (*
        invc H5.
        invc H8.
        +++
          df.
          eexists.
          split.
          2 : {
            econstructor.
            tauto.
            eassumption.
          }
          
          

            econstructor.
            df.
          ++++
            
        


      

      invc H8.
      ++

        apply in_app_or in H6.
        destruct H6.
        +++
          eexists.
          split.
          ++++
            apply in_or_app.
            eauto.
          ++++
            econstructor.
            tauto.
            eassumption.
        +++
          
          
            

      exists x0.
      split.
      

      eauto.

      (*
      eapply build_app_some'.
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
      eassumption. *)

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
      exists x.
      eauto. *)
      
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
                                st_hshmap := hmap;
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

      assert (nm = am_nonceMap /\ ni = am_nonceId /\ amap = st_aspmap /\ smap = st_sigmap /\ st_hshmap = st_hshmap).
      {
        edestruct ba_const.
        apply Heqp0.
        destruct_conjs.
        ff.
      }

      destruct_conjs.
      subst.
      invc H5.
      ++
      ff.
      econstructor.
      reflexivity.
      ff.
      ++
        ff.
        econstructor.
        eassumption.
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
                                st_hshmap := hmap;
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

      assert (nm = am_nonceMap /\ ni = am_nonceId /\ amap = st_aspmap /\ smap = st_sigmap /\ hmap = st_hshmap).
      {
        edestruct ba_const.
        apply Heqp0.
        destruct_conjs.
        ff.
      }

      destruct_conjs.
      subst.
      invc H5.
      ++
      ff.
      econstructor.
      reflexivity.
      ff.
      ++
        econstructor.
        eassumption.
        
Defined.

Require Import GenStMonad MonadVM (*MonadAM*) ConcreteEvidence.
Require Import StAM Axioms_Io Impl_vm (*Impl_appraisal*) Maps VmSemantics Event_system Term_system External_Facts Helpers_VmSemantics.
Require Import Auto AutoApp (*AllMapped Appraisal_Defs Helpers_Appraisal*).

Require Import Appraisal_Defs_alt alt_Impl_appraisal.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

Lemma build_app_some_evshape: forall e et,
    Ev_Shape e et ->
    exists x, build_app_comp_ev e et = Some x.
Proof.
Admitted.

Lemma appraisal_correct : forall t ev1 tr1 p e_res tr1' p' et_res et
                            e ev,
    well_formed_r t ->
    Ev_Shape ev1 e ->
    copland_compile t
      {| st_ev := ev1; st_evT := et; st_trace := tr1; st_pl := p |} =
    (Some tt, {| st_ev := e_res;
                 st_evT := et_res;
                 st_trace := tr1';
                 st_pl := p' |}) ->

    measEvent t p e ev ->
    exists app_res, build_app_comp_ev e_res (aeval t p e) = Some app_res /\
    
    appEvent_Evidence ev app_res.
Proof.
  intros.

  edestruct build_app_some_evshape.
  eapply cvm_refines_lts_evidence.
  eassumption.
  eassumption.
  eassumption.
  tauto.
  exists x.
  split.
  Locate aeval.
  rewrite eval_aeval in H3.
  eassumption.



  
  generalizeEverythingElse t.
  induction t; intros.
  -
      measEventFacts.
      evEventFacts.
      inv_events.
      (*
      edestruct build_app_some_evshape.
      eapply cvm_refines_lts_evidence.
      eassumption.
      eassumption.
      eassumption.
      tauto. 

      eexists.
      split.
      eassumption. *)

      ff.
      break_match; try solve_by_inversion.
      ff.

      repeat econstructor.

  -
    measEventFacts.
    evEventFacts.
    invEvents.
    vmsts.
    ff.
    do_wf_pieces.
    eapply IHt.
    eassumption.
    eassumption.
    eapply copland_compile_at.
    eassumption.
    econstructor.
    eassumption.
    econstructor.
    eassumption.
  -
    Print do_wf_pieces.
    edestruct wf_lseq_pieces;[eauto | idtac].
    (* do_wf_pieces. *)
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.

    invc H6.

    
    inv_events.
     + (* t1 case *)
       clear H1.

       edestruct build_app_some_evshape.
       eapply cvm_refines_lts_evidence.
       apply H4.
       eassumption.
       eassumption.
       tauto.
       edestruct build_app_some_evshape.
       eapply cvm_refines_lts_evidence.
       apply H5.
       eassumption.
       eapply cvm_refines_lts_evidence.
       apply H4.
       eassumption.
       eassumption.
       tauto.
       tauto.
       
(*
       assert (exists et pi bs e',
                  EvSub (HashV (checkHash et pi bs)) x0 /\
                  EvSubT (uu i args tpl tid e') et).
       {
         admit.
       }
 *)
       rewrite H3 in *.
       invc H2.

       

       
       

       assert (exists et pi bs e',
                  EvSub (BitsV (bsval (checkHash et pi bs))) x1 /\
                  EvSubT (uu i args tpl tid e') et).
       {
         admit.
       }

       destruct_conjs.
       

       eapply ahu.
       apply H10.
       eassumption.

       subst'.

       
       
       




       

       assert (
            forall x : EvidenceC,
         build_app_comp_ev st_ev (eval (unanno t1) p e) = Some x ->
         appEvent_Evidence (umeas n p0 i args tpl tid) x).
       {
        
         (*

        assert (exists app_res : EvidenceC,
           build_app_comp_ev st_ev (aeval t1 p e) = Some app_res ->
           appEvent_Evidence (umeas n p0 i args tpl tid) app_res).
       {  *)
         eapply IHt1.
         eassumption.
         eassumption.
         eassumption.
         econstructor.
         eassumption.
         econstructor.
       }
       destruct_conjs.

       
     



       (*
       edestruct build_app_some_evshape.
       eapply cvm_refines_lts_evidence.
       apply H.
       ff.
       rewrite Heqp0 in *.
       ff.
       rewrite Heqp1 in *.
       ff.
       eassumption.
       tauto.
       ff.
       exists x.
       split.
       admit. *)

       (*
       assert ((exists n' p' et' e', events t1 p e (hash n' p' et') /\
                             EvSubT (uu i args tpl tid e') et') \/
               (exists n' p' et' e', events t2 p (aeval t1 p e) (hash n' p' et') /\
                             EvSubT (uu i args tpl tid e') et') \/
               (EvSub (HashV (checkASP i args tpl tid n)) x)).
       {
         admit.
       }
        *)

       assert (


       

       Lemma events_dec_hsh:
         forall t p e i args tpl tid,
           {exists n' p' et' e',
               events t p e (hash n' p' et') /\
               EvSubT (uu i args tpl tid e') et'} +
           {~
              (exists n' p' et' e',
               events t p e (hash n' p' et') /\
               EvSubT (uu i args tpl tid e') et')}.
       Proof.
       Admitted.

       destruct (events_dec_hsh t2 p (aeval t1 p e) i args tpl tid).
       ++
         destruct_conjs.
         eapply ahu.
         eassumption.
         

         assert (
         exists app_res : EvidenceC,
           build_app_comp_ev e_res (aeval t2 p (aeval t1 p e)) = Some app_res /\
           appEvent_Evidence (umeas n p0 i args tpl tid) app_res).
         {
           eapply IHt2.
           eassumption.

         eapply cvm_refines_lts_evidence.
         apply H3.
         eassumption.
         eassumption.
         admit.
         eassumption.
         econstructor.
         eassumption.
         ff.
         rewrite Heqp0 in *.
         ff.
         rewrite Heqp1 in *.
         ff.
         eassumption.
         tauto.
         eassumption.

       destruct (events_dec_hsh t1 p e i args tpl tid).
       ++
         destruct_conjs.
         destruct (events_dec_hsh t2 p (aeval t1 p e) i args tpl tid).
         +++
           destruct_conjs.

       assert ((exists n' p' et' e', events t1 p e (hash n' p' et') /\
                                
                             EvSubT (uu i args tpl tid e') et') \/
               (exists n' p' et' e', events t2 p (aeval t1 p e) (hash n' p' et') /\
                             EvSubT (uu i args tpl tid e') et') \/
               (EvSub (HashV (checkASP i args tpl tid n)) x)).
       
       destruct H7.
       ++
         destruct_conjs.
         eapply ahu.
         eassumption.


         
         admit.
       ++
         destruct H2.
         +++
         
       
               


       

       assert (exists app_res : EvidenceC,
           build_app_comp_ev st_ev (aeval t1 p e) = Some app_res /\
           appEvent_Evidence (umeas n p0 i args tpl tid) app_res).
       {
         eapply IHt1.
         eassumption.
         eassumption.
         eassumption.
         econstructor.
         eassumption.
         econstructor.
       }
       destruct_conjs.

       invc H5.
       ++
         edestruct build_app_some_evshape.
         eapply cvm_refines_lts_evidence.
         apply H.
         cbn.
         ff.
         rewrite Heqp0 in *.
         ff.
         rewrite Heqp1 in *.
         ff.
         eassumption.
         tauto.
         exists x.
         split.
         admit.
         ff.


         
         ff.
         
         eexists.
         split.

       edestruct IHt1.
       eassumption.
       eapply cvm_refines_lts_evidence.
       
       apply H3.
       eassumption.
       eassumption.
       tauto.
       eassumption.
       e


       

       assert (EvSub ev1 st_ev /\ EvSub st_ev e_res).
       {
         admit.
       }
       destruct_conjs.

       assert (exists res, build_app_comp_ev st_ev st_evT = res).
       {
         eexists.
         tauto.
       }
       destruct_conjs.
       
       

       assert (appEvent_Evidence (umeas n p0 i args tpl tid) H4).
       rewrite <- H5.
       eapply IHt1.
       eassumption.
       eassumption.
       econstructor.
       eassumption.
       econstructor.

       invc H6.
       ++
         econstructor.
         tauto.

         Lemma evsub_trans: forall e e' e'',
           EvSub e e' ->
           EvSub e' e'' ->
           EvSub e e''.
         Proof.
           intros.
           generalizeEverythingElse e''.
           induction e''; intros.
           -
             invc H0.
             eassumption.
           -
             invc H0.
             +
               eassumption.
             +
               apply uuSub.
               eauto.
           -
             invc H0.
             +
               eassumption.
             +
               econstructor; eauto.
           -
             invc H0.
             eassumption.
           -
             invc H0.
             +
               eassumption.
             +
               econstructor; eauto.
           -
             invc H0; eauto.
             econstructor; eauto.
             apply ssSubr; eauto.
           -
             invc H0; eauto.
             econstructor; eauto.
             apply ppSubr; eauto.
         Defined.

         Lemma app_sub: forall e e' et et',
           EvSub e e' ->
           EvSub (build_app_comp_ev e et) (build_app_comp_ev e' et').
         Proof.
           intros.
           generalizeEverythingElse H.
           induction H; intros.
           -
             
         Admitted.

         eapply evsub_trans.
         eassumption.
         eapply app_sub.
         eassumption.
       ++
         assert (EvSub (hhc pi (checkHash et0 pi bs)) (build_app_comp_ev e_res et_res)).
         {
           eapply evsub_trans.
           eassumption.
           eapply app_sub.
           eassumption.
         }

         eapply ahu.
         eassumption.
         eassumption.

     +
       eapply IHt2.
       eassumption.
       eassumption.
       econstructor.
       eassumption.
       eassumption.
  -
    
    do_wf_pieces.
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H4.

    
    inv_events;
      ff.
    +
      assert (appEvent_Evidence (umeas n1 p0 i args tpl tid) (build_app_comp_ev st_ev0 st_evT0)).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H1.
      ++
      econstructor.
      tauto.
      econstructor.
      eassumption.
      ++
        eapply ahu.
        eassumption.
        econstructor.
        eassumption.
    +
      assert (appEvent_Evidence (umeas n1 p0 i args tpl tid) (build_app_comp_ev st_ev st_evT)).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H1.
      ++
        econstructor.
        tauto.
        eapply ssSubr.
        eassumption.
      ++
        eapply ahu.
        eassumption.
        eapply ssSubr.
        eassumption.
  -
    
      
      
        

      

      econstructor.
      tauto.
      econstructor.
      eassumption.
      
      edestruct IHt1; eauto.
      econstructor; eauto.
    
    






Lemma appraisal_correct : forall t ev1 tr1 p e_res tr1' p' et_res et
                            nm nm' ni ni' amap amap' smap smap' hmap hmap' tr tr' cs cs'
                            app_res
                            e ev,
    well_formed_r t ->
    (*Ev_Shape ev1 et -> *)
    copland_compile t
                    {| st_ev := ev1; st_evT := et; st_trace := tr1; st_pl := p |} =
    (Some tt, {| st_ev := e_res; st_evT := et_res; st_trace := tr1'; st_pl := p' |}) ->

    build_app_comp_ev e_res et_res {| am_nonceMap := nm;
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
                                                    am_st_trace:= tr';
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
    (*
    eapply in_or_app.
    right. *)
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



    

     assert (EvSubT st_evT et_res).
    {
      eapply evAccum.
      eauto.
      eauto.
      eauto.
      eauto.
    }
     
    

    edestruct build_app_some.
    eapply evMappedSome.
    eassumption.
    eapply build_app_some'.
    eauto.
    admit.

    
    
(*
    edestruct subSome.
    apply H2.
    eassumption.
 *)
    

    destruct_conjs.
    amsts'.

    
(*
    edestruct am_trace_cumul.
    apply H7. *)
    
    edestruct am_trace_cumul.
    apply H1.
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



    (*
    assert (forall ev, In ev x0 -> In ev x1).
    {
      eapply app_evSub.
      eauto.
      eauto.
      eassumption.
      eassumption.
    } *)
    

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

      invc H8.
      ++
        specialize (H6 (umeas n' p' i' ([n] ++ args) tpl' tid')).
        apply in_app_or in H8.
        destruct H8.
        +++
          eexists.
          split.
          apply in_or_app.
          eauto.
          econstructor.
          tauto.
          eassumption.
        +++
          
        concludes.
        eexists.
        split.
        apply in_or_app.
        eauto.
        
        econstructor.
        tauto.
        eassumption.
      ++
        specialize (H6 (umeas n0 p1 1 ([hashEvT e0] ++ args0) tpl0 tid0)).
        apply in_app_or in H8.
        destruct H8.
        +++
          eexists.
          split.
          apply in_or_app.
          eauto.
          eapply ahu.
          eassumption.
        +++
          
        concludes.
        eexists.
        split.
        apply in_or_app.
        eauto.
        eapply ahu.
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







        
      (*
        
        




      

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




*)
      
  - (* abseq case *)
    do_wf_pieces.
    repeat ff.
    vmsts.
    repeat ff.
    amsts'.

    (*
    edestruct am_trace_cumul; eauto. *)

     edestruct am_trace_cumul; eauto.
    subst.
    

    measEventFacts.
    (*
    do_cumul_app.
    do_inv_head'.
    do_inv_head'. *)
    subst.
    (*
    ff. *)
    do_pl_immut.
    do_pl_immut.
    subst.
    inv_events;
      unfold runSt in *;
      try solve_by_inversion.
    
    + (* t1 case *)
      (*
      edestruct am_trace_cumul.
      apply Heqp0.
      subst.

      edestruct am_trace_cumul.
      apply Heqp1.
      do_inv_head'.
      subst. *)


     
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

      (*

      edestruct am_trace_cumul.
      apply Heqp0.
      subst.

      edestruct am_trace_cumul.
      apply Heqp1.
      do_inv_head'.
      subst.



      
      assert (exists ev', In ev' H2 /\
                     appEvent ev
                              {|
                                am_nonceMap := am_nonceMap;
                                am_nonceId := am_nonceId;
                                st_aspmap := st_aspmap;
                                st_sigmap := st_sigmap;
                                st_hshmap := st_hshmap;
                                am_st_trace := tr ++ H5;
                                checked := checked |} ev'). *)
      eapply IHt2.
      eassumption.
      eassumption.
      (*
      rewrite app_assoc in *. *)
      eassumption.
      econstructor.
      eassumption.
      eassumption.
      destruct_conjs.
      exists H9.
      split.
      apply in_or_app.
      eauto.
      eassumption.





      
      
    + (* t2 case *)
     

      assert (nm = am_nonceMap /\ ni = am_nonceId /\ amap = st_aspmap /\ smap = st_sigmap /\ hmap = st_hshmap).
      {
        edestruct ba_const.
        apply Heqp0.
        destruct_conjs.
        ff.
      }
      destruct_conjs.
      subst.
      
       assert (exists ev', In ev' H2 /\
                     appEvent ev
                              {|
                                am_nonceMap := am_nonceMap;
                                am_nonceId := am_nonceId;
                                st_aspmap := st_aspmap;
                                st_sigmap := st_sigmap;
                                st_hshmap := st_hshmap;
                                am_st_trace := tr ++ H5;
                                checked := checked |} ev').
       eapply IHt2.
       eassumption.
       eassumption.
       rewrite app_assoc in *.
       eassumption.
       econstructor.
       eassumption.
       eassumption.
       destruct_conjs.
       exists H9.
       split.
       apply in_or_app.
       eauto.
       eassumption.




      
      rewrite app_assoc in *.
      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      econstructor.
      eassumption.
      eassumption.
      destruct_conjs.

            assert (nm = am_nonceMap /\ ni = am_nonceId /\ amap = st_aspmap /\ smap = st_sigmap /\ st_hshmap = st_hshmap).
      {
        edestruct ba_const.
        apply Heqp0.
        destruct_conjs.
        ff.
      }
      destruct_conjs.
      subst.

      exists x0.
      split.
      ++
        apply in_or_app.
        eauto.
      ++
        
        
        



      destruct_conjs.
      subst.
      invc H5.
      ++
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

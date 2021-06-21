Require Import (*GenStMonad*) MonadVM (*MonadAM*) ConcreteEvidence.
Require Import StAM Axioms_Io Impl_vm (*Impl_appraisal*) Maps VmSemantics Event_system Term_system External_Facts Helpers_VmSemantics.
Require Import Auto AutoApp (*AllMapped Appraisal_Defs Helpers_Appraisal*).

Require Import Appraisal_Defs_alt alt_Impl_appraisal.

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

Lemma build_app_some_evshape: forall e et,
    Ev_Shape e et ->
    exists x, build_app_comp_ev e et = Some x.
Proof.
Admitted.

Definition peelOneBitsVval (e:EvidenceC) : option BS :=
  match e with
  | (BitsV bs) => Some bs
  | _ => None
  end.

(*
Inductive EvidenceCon: Set :=
| mtc: EvidenceCon
| uuc: ASP_ID -> (list Arg) -> Plc -> TARG_ID -> BS -> EvidenceCon -> EvidenceCon
| ggc: Plc -> BS -> EvidenceCon -> EvidenceCon
| hhc: Plc -> BS -> Evidence -> EvidenceCon
| nnc: N_ID -> BS -> EvidenceCon
| ssc: EvidenceCon -> EvidenceCon -> EvidenceCon
| ppc: EvidenceCon -> EvidenceCon -> EvidenceCon.
*)

Fixpoint reconstruct_EvCon (e:EvidenceC) (et:Evidence): option EvidenceCon :=
  match et with
  | mt =>
    match e with
    | BitsV 0 => ret mtc
    | _ => None
    end
  | uu i args tpl tid et' =>
    '(bs,e') <- peelBitsVval e ;;
    e_res <- reconstruct_EvCon e' et' ;;
    ret (uuc i args tpl tid bs e_res)
  | gg p et' =>
    '(bs,e') <- peelBitsVval e ;;
    e_res <- reconstruct_EvCon e' et' ;;
    ret (ggc p bs e_res)
  | hh p et' =>
    bs <- peelOneBitsVval e ;;
    ret (hhc p bs et')
  | nn nid =>
    bs <- peelOneBitsVval e ;;
    ret (nnc nid bs)
  | ss et1 et2 =>
    '(e1,e2) <- peelPairBitsV e ;;
    e1r <- reconstruct_EvCon e1 et1 ;;
    e2r <- reconstruct_EvCon e2 et2 ;;
    ret (ssc e1r e2r)
  | pp et1 et2 =>
    '(e1,e2) <- peelPairBitsV e ;;
    e1r <- reconstruct_EvCon e1 et1 ;;
    e2r <- reconstruct_EvCon e2 et2 ;;
    ret (ppc e1r e2r)
  end.
    




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
  rewrite eval_aeval in H3.
  eassumption.



  
  generalizeEverythingElse t.
  induction t; intros.
  
  - (* aasp case *)
      measEventFacts.
      evEventFacts.
      inv_events.

      ff.
      break_match; try solve_by_inversion.
      ff.

      repeat econstructor.

  - (* aatt case *)
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
    
  - (* alseq case *)
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

       Lemma t1_ev1: forall t1 ev1 et tr1 p st_ev st_evT st_trace
                      n p0 i args tpl tid e,
         copland_compile t1
            {| st_ev := ev1; st_evT := et; st_trace := tr1; st_pl := p |} =
          (Some tt,
          {|
          st_ev := st_ev;
          st_evT := st_evT;
          st_trace := st_trace;
          st_pl := p |}) ->

         
         events t1 p e (umeas n p0 i args tpl tid) ->

         (
         EvSub (BitsV n) st_ev /\
         (exists et', EvSubT (uu i args tpl tid et') (aeval t1 p e))
         ) \/
         (exists p' et' et'',
             EvSubT (hh p' et') (aeval t1 p e) /\
             EvSubT (uu i args tpl tid et'') et').
       Proof.
       Admitted.


       assert
       (
         EvSub (BitsV n) e_res /\
         (exists et', EvSubT (uu i args tpl tid et') (aeval t2 p (aeval t1 p e)))
         \/
         (exists p' et' et'',
             EvSubT (hh p' et') (aeval t1 p e) /\
             EvSubT (uu i args tpl tid et'') et')
       ).
       {
         admit.
       }

       
       destruct H1.
       ++
         destruct_conjs.
         rewrite eval_aeval in H3.
         rewrite eval_aeval in H3.
         econstructor.
         
       












       

       Lemma t2_ev:
         copland_compile t2
            {|
            st_ev := st_ev;
            st_evT := st_evT;
            st_trace := st_trace;
            st_pl := p |} =
          (Some tt,
           {| st_ev := e_res; st_evT := et_res; st_trace := tr1'; st_pl := p |}) ->
         EvSub e st_ev ->

         EvSub e e_res \/
         EvSubT 
       
           



       

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

       

       
       

       assert ({(exists et pi bs e',
                  EvSub (BitsV (checkHash et pi bs)) x1 /\
                  EvSubT (uu i args tpl tid e') et)} +
               {~(exists et pi bs e',
                  EvSub (BitsV (checkHash et pi bs)) x1 /\
                  EvSubT (uu i args tpl tid e') et)}).
       {
         admit.
       }

        assert ({(exists et pi bs e',
                  EvSub (BitsV (checkHash et pi bs)) x0 /\
                  EvSubT (uu i args tpl tid e') et)} +
               {~(exists et pi bs e',
                  EvSub (BitsV (checkHash et pi bs)) x0 /\
                  EvSubT (uu i args tpl tid e') et)}).
       {
         admit.
       }

       destruct H2.
       ++
         destruct_conjs.
         eapply ahu.
         apply H10.
         eassumption.
       ++
         destruct H6.
         +++
           destruct_conjs.
           admit.
         +++
           admit.
     + (* t2 case *)
       eapply IHt2.
       eassumption.
       eapply cvm_refines_lts_evidence.
       apply H4.
       eassumption.
       eassumption.
       tauto.
       eassumption.
       econstructor.
       rewrite eval_aeval.
       eassumption.
       econstructor.
       eassumption.

  - (* abseq case *)
    (*
    do_wf_pieces. *)
    edestruct wf_bseq_pieces;[eauto | idtac].
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
    invc H3.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

      
      assert (appEvent_Evidence (umeas n1 p0 i args tpl tid) e2).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
      }

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahu.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

      
      assert (appEvent_Evidence (umeas n1 p0 i args tpl tid) e2).
      {
        eapply IHt1.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
      }

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahu.
        eassumption.
        econstructor.
        eassumption.
      ++
                ff.

      
      assert (appEvent_Evidence (umeas n1 p0 i args tpl tid) e2).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
      }

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahu.
        eassumption.
        econstructor.
        eassumption.
    + (* t2 case *)

      destruct s.
      ++
        ff.

      
      assert (appEvent_Evidence (umeas n1 p0 i args tpl tid) e3).
      {
        eapply IHt2.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
      }

      invc H2.
      +++
        econstructor.
        apply evsub_pairr.
        eassumption.
      +++
        eapply ahu.
        eassumption.
        apply evsub_pairr.
        eassumption.
      ++
        ff.

      
      assert (appEvent_Evidence (umeas n1 p0 i args tpl tid) e3).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
      }

      invc H2.
      +++
        econstructor.
        apply evsub_pairr.
        eassumption.
      +++
        eapply ahu.
        eassumption.
        apply evsub_pairr.
        eassumption.
      ++
        ff.

      
      assert (appEvent_Evidence (umeas n1 p0 i args tpl tid) e3).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
      }

      invc H2.
      +++
        econstructor.
        apply evsub_pairr.
        eassumption.
      +++
        eapply ahu.
        eassumption.
        apply evsub_pairr.
        eassumption.
  - (* abpar base *)
    admit.

    (*
    Unshelve.
    eauto. 
     *)
    

Abort.



(* ** MISC extra lemmas ** *)
(*
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
      econstructor.
      eauto.
    +
      apply evsub_pairr.
      eauto.
Defined.

Lemma app_sub: forall e e' et et' e1 e2,
    EvSub e e' ->
    build_app_comp_ev e et = Some e1 ->
    build_app_comp_ev e' et' = Some e2 ->
    
    EvSub e1 e2.
Proof.
  intros.
  generalizeEverythingElse H.
  induction H; intros.
  -
    
Admitted.

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
*)

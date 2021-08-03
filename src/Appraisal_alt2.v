Require Import Maps Event_system Term_system MonadVM ConcreteEvidence.
Require Import Impl_vm Helpers_VmSemantics VmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp.

Require Import StAM Appraisal_Defs Impl_appraisal (*MonadAM*).

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

(*
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
 *)

Ltac evsub_ih :=
  match goal with
  | [H: EvSub _ ?e,
        IH: context[EvSub _ ?e -> _] |- _] =>
    edestruct IH; [eauto | eauto ]
  end.
          
Lemma uuc_app: forall e' e'' i args tpl tid n,
    EvSub (uuc i args tpl tid n e'') e' ->
    exists e'', EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e'')
                 (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff;
    try evSubFacts; eauto;
    try evsub_ih.
Defined.

Lemma hhc_app: forall e' p bs et,
    EvSub (hhc p bs et) e' ->
    EvSub (hhc p (checkHash et p bs) et)
          (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff;
    try evSubFacts;
    eauto.
Defined.

Lemma evsubT_transitive: forall e e' e'',
    EvSubT e e' ->
    EvSubT e' e'' ->
    EvSubT e e''.
Proof.
  intros.
  generalizeEverythingElse e''.
  induction e''; intros;
    try evSubTFacts;
       eauto.
Defined.

Lemma evsub_etfun: forall e e',
    EvSub e e' ->
    EvSubT (et_fun e) (et_fun e').
Proof.
  intros.
  induction H; intros;
    ff; eauto.
Defined.

Lemma etfun_reconstruct: forall e e0 e1,
    Some e = reconstruct_ev' e0 e1 ->
    e1 = et_fun e.
Proof.
  intros.
  generalizeEverythingElse e1.
  induction e1; intros.
  -
    ff.
  -
    ff.
    ff.
    erewrite IHe1; eauto.
  -
    ff.
    ff.
    erewrite IHe1; eauto.
  -
    ff.
    ff.
  -
    ff.
    ff.
  -
    ff.
    ff.
    erewrite IHe1_1; eauto.
    erewrite IHe1_2; eauto.
  -
    ff.
    ff.
    erewrite IHe1_1; eauto.
    erewrite IHe1_2; eauto.
Defined.

Inductive wf_ec : EvC -> Prop :=
| wf_ec_c: forall ls et,
    length ls = et_size et ->
    wf_ec (evc ls et).

Lemma wf_ec_preserved_by_cvm : forall bits bits' et et' t1 tr tr' p p',
    wf_ec (evc bits et) ->
    copland_compile t1
                    {| st_ev := evc bits et; st_trace := tr; st_pl := p |} =
    (Some tt,
     {| st_ev := evc bits' et'; st_trace := tr'; st_pl := p' |}) ->
    wf_ec (evc bits' et').
Proof.
Admitted.

Lemma evAccum: forall t p (e e' e'':EvidenceC) tr tr' p' (ecc ecc':EvC),

    well_formed_r t ->
    Some e =  (reconstruct_ev ecc) -> (*fromSome mtc (reconstruct_ev ecc) ->*) (* = (Some e) -> *)
    Some e' = (reconstruct_ev ecc') -> (*fromSome mtc (reconstruct_ev ecc') ->*) (* = (Some e') -> *)
    EvSub e'' e ->
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    

    (
      (EvSub e'' e') \/
      (exists ett p' bs,
          EvSub (hhc p' bs ett) e' /\
          EvSubT (et_fun e'') ett
      )
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      (ff; try eauto).
    +
      rewrite <- H0 in *. clear H0.
      ff.
    +
      unfold cons_uu in *.
      repeat ff.
    +
      unfold cons_gg in *.
      repeat ff.
    +
      right.
      repeat eexists.
      econstructor.
      Check evsub_etfun.
      assert (e1 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.

      apply evsub_etfun; eauto.
  -
    do_wf_pieces.
    ff.
    
    eapply IHt.
    eassumption.
    apply H0.
    eassumption.
    eassumption.
    apply copland_compile_at.
    eassumption.
  -
    ff.
    dosome.
    vmsts.

    do_wf_pieces.

    (*
    destruct st_ev.
    destruct ecc.
    destruct ecc'. *)
    
    
    
    assert (exists ee, Some ee = reconstruct_ev st_ev).
    {
      admit.
    }
    destruct_conjs.
    

    assert (EvSub e'' H5 \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) H5 /\ EvSubT (et_fun e'') ett)).
    {
      eauto.
    }
    destruct H7.
    +
      
      
      
      
      


      (*

      assert (EvSub e'' e' \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett)).
      { *)
        
        
        eapply IHt2.
        eassumption.
        2: {
          eassumption.
        }
        3: {
          eassumption.
        }
        eassumption.
        eassumption.

        (*
      }
      eauto. *)

      (*

    destruct H6.
      ++
        eauto.
        (*
        eapply IHt2.
        eassumption.
        apply H3.
        eassumption. *)
      ++
        destruct_conjs.
        eauto.
        (*
        right.
        repeat eexists.
        eauto.
        eauto. *) *)
    +
      destruct_conjs.
      assert (EvSub (hhc H8 H9 H7) e' \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun (hhc H8 H9 H7)) ett)).
    {
      eapply IHt2.
      eassumption.
      2: {
        eassumption.
      }
      2: {
        eassumption.
      }
      eassumption.
      eassumption.
      (*
      
      
      eassumption.
      eassumption.
      eassumption. *)
    } 
    destruct H12.
      ++
        right.
        repeat (eexists; eauto).
        (*
        eauto.
        eauto. *)
      ++
        destruct_conjs.
        ff.
        
        right.
        exists H12.
        repeat eexists.
        eassumption.
        assert (EvSubT (et_fun e'') (hh H8 H7)).
        {
          
        
        eapply evsubT_transitive.
        eassumption.
        apply hhSubT.
        econstructor.
        }
        eapply evsubT_transitive.
        eassumption.
        eassumption.
  -
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
    subst.

    (*
    assert (firstn (et_size e1) (e0 ++ e2) = e0).
    {
      admit.
    }
    rewrite H1 in *. clear H1.
    assert (skipn (et_size e1) (e0 ++ e2) = e2).
    {
      admit.
    }
    rewrite H1 in *. clear H1.
     *)


    assert (firstn (et_size e1) (e0 ++ e2) = e0).
    {
          assert (wf_ec (evc e0 e1)).
          {
            admit.
            (*
            eapply wf_ec_preserved_by_cvm; eauto. *)
          }
          invc H1.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
    {
      admit.
      (*
      assert (wf_ec (evc e e0)).
      {
        eapply wf_ec_preserved_by_cvm; eauto.
      }
      invc H3.
      rewrite <- H7.
      eapply More_lists.skipn_append. *)
    }
    rewrite H1 in *; clear H1.
    rewrite H3 in *; clear H3.








    
    
    

    destruct s.
    +
      ff.
      assert (
           EvSub e'' (fromSome mtc (reconstruct_ev (evc e0 e1))) \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) (fromSome mtc (reconstruct_ev (evc e0 e1))) /\ EvSubT (et_fun e'') ett)
        ).
      {
        cbn.
        rewrite Heqo.
        ff.
        eapply IHt1.
        eassumption.
        apply H0.
        rewrite <- Heqo.
        2: {
          eassumption.
        }
        2: {
          eassumption.
        }
        cbn.
        tauto.
      }

      cbn in *.
      rewrite Heqo in *.
      ff.
      
      
        
        


        
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ssSubl; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ssSubl.
        eassumption.
        eassumption. *)

    +
      
      
      ff.
      unfold mt_evc in *.
      ff.
      assert (
           EvSub e'' (fromSome mtc (reconstruct_ev (evc e2 e3))) \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) (fromSome mtc (reconstruct_ev (evc e2 e3))) /\ EvSubT (et_fun e'') ett)
        ).
      {
        cbn.
        rewrite Heqo0.
        ff.
        eapply IHt2.
        eassumption.
        4: {
          
          eassumption.
        }
        ff.
        cbn.
        rewrite Heqo0. tauto.
        eassumption.

      }
      
      

      ff.
      rewrite Heqo0 in *.
      ff.
        


        
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ssSubl; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ssSubl.
        eassumption.
        eassumption. *)

    +
      

      ff.
      assert (
           EvSub e'' (fromSome mtc (reconstruct_ev (evc e2 e3))) \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) (fromSome mtc (reconstruct_ev (evc e2 e3))) /\ EvSubT (et_fun e'') ett)
        ).
      {
        cbn.
        rewrite Heqo0.
        ff.
        eapply IHt2.
        eassumption.
        4: {
          
          eassumption.
        }
        ff.
        cbn.
        rewrite Heqo0. tauto.
        eassumption.

      }
      
      

      ff.
      rewrite Heqo0 in *.
      ff.
        


        
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ssSubl; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ssSubl.
        eassumption.
        eassumption. *)

  -
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
    subst.

    assert (firstn (et_size e1) (e0 ++ e2) = e0).
    {
      admit.
    }
    rewrite H1 in *. clear H1.
    assert (skipn (et_size e1) (e0 ++ e2) = e2).
    {
      admit.
    }
    rewrite H1 in *. clear H1.
    
    

    destruct s.
    +
      ff.
      assert (
           EvSub e'' (fromSome mtc (reconstruct_ev (evc e0 e1))) \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) (fromSome mtc (reconstruct_ev (evc e0 e1))) /\ EvSubT (et_fun e'') ett)
        ).
      {
        cbn.
        rewrite Heqo.
        ff.
        eapply IHt1.
        eassumption.
        apply H0.
        rewrite <- Heqo.
        2: {
          eassumption.
        }
        2: {
          eassumption.
        }
        cbn.
        tauto.
      }

      cbn in *.
      rewrite Heqo in *.
      ff.
      
      
        
        


        
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ssSubl; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ssSubl.
        eassumption.
        eassumption. *)

    +
      
      
      ff.
      unfold mt_evc in *.
      ff.
      assert (
           EvSub e'' (fromSome mtc (reconstruct_ev (evc e2 e3))) \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) (fromSome mtc (reconstruct_ev (evc e2 e3))) /\ EvSubT (et_fun e'') ett)
        ).
      {
        cbn.
        rewrite Heqo0.
        ff.
        eapply IHt2.
        eassumption.
        4: {
          
          eassumption.
        }
        ff.
        cbn.
        rewrite Heqo0. tauto.
        eassumption.

      }
      
      

      ff.
      rewrite Heqo0 in *.
      ff.
        


        
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ssSubl; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ssSubl.
        eassumption.
        eassumption. *)

    +
      

      ff.
      assert (
           EvSub e'' (fromSome mtc (reconstruct_ev (evc e2 e3))) \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) (fromSome mtc (reconstruct_ev (evc e2 e3))) /\ EvSubT (et_fun e'') ett)
        ).
      {
        cbn.
        rewrite Heqo0.
        ff.
        eapply IHt2.
        eassumption.
        4: {
          
          eassumption.
        }
        ff.
        cbn.
        rewrite Heqo0. tauto.
        eassumption.

      }
      
      

      ff.
      rewrite Heqo0 in *.
      ff.
        


        
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ssSubl; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ssSubl.
        eassumption.
        eassumption. *)
Admitted.




















(*  
  -
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    destruct s.
    +
      ff.
      assert (
           EvSub e'' st_ev0 \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (et_fun e'') ett)
        ) by eauto.
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ppSubl; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ppSubl.
        eassumption.
        eassumption. *)
    +
      ff.
      assert (
           EvSub e'' st_ev \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (et_fun e'') ett)
        ) by eauto.
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ppSubr; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ppSubr.
        eassumption.
        eassumption. *)
    +
      ff.
      assert (
           EvSub e'' st_ev0 \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (et_fun e'') ett)
        ) by eauto.
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ppSubl; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ppSubl.
        eassumption.
        eassumption. *)
*)

Lemma uu_preserved': forall t p et n p0 i args tpl tid
                       e tr e' tr' p' ecc ecc',

    well_formed_r t ->
    Some e = (reconstruct_ev ecc) -> (* = (Some e) -> *)
    Some e' = (reconstruct_ev ecc') -> (* = (Some e') -> *)
    events t p et (umeas n p0 i args tpl tid) ->
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid et') ett)
    ).
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a; ff.
    +
      inv_events.
      ff.
      unfold cons_uu in *.
      repeat ff.
      left.
      eexists.
      econstructor.
      (*
      econstructor.
      eauto.
      unfold cons_uu.
      ff.
      ff.
      econstructor.
      eauto.
      econstructor. *)
  -
    ff.
    invEvents.
    do_wf_pieces.
    assert (
         (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n0 e'')  e') \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett)  e' /\ EvSubT (uu i args tpl tid et') ett)
      ).

    {
      eapply IHt.
           
      eassumption.
      2: {
        eassumption.
      }
      apply H0.
      
    eassumption.

    apply copland_compile_at.
    eassumption.
    }
    eassumption.
  -
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)

      assert (exists ee, Some ee = reconstruct_ev st_ev).
      {
        admit.
      }
      destruct_conjs.
      
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') H2) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) H2 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        3: {
          eassumption.
        }
        2: {
          eassumption.
        }
        apply H0.
        
        
        eassumption.
      }
      destruct_conjs.
      destruct H6.
      ++
        destruct_conjs.
        assert (
            (EvSub (uuc i args tpl tid n H6) e') \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e' /\
                EvSubT (et_fun (uuc i args tpl tid n H6)) ett
            )
          ).
        {
          eapply evAccum; eauto.
        }
        clear H11.
        destruct H8.
        +++
          left.
          eauto.
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          eauto.
          eauto. *)
      ++
        destruct_conjs.
        assert (
            (EvSub (hhc H7 H8 H6) e') \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e' /\
                EvSubT (et_fun (hhc H7 H8 H6)) ett
            )
          ).
        {
          eapply evAccum; eauto.
        }
        destruct H13.
        +++
          right.
          repeat (eexists; eauto).
                 (*
          eauto.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat eexists.
          eauto.

          assert (EvSubT (uu i args tpl tid H9) (hh H7 H6)).
          {
            apply hhSubT.
            eassumption.
          }

          
          

          eapply evsubT_transitive.
          eassumption.
          eassumption.
          (*
          apply H14.
          eassumption. *)
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      assert (exists ee, Some ee = reconstruct_ev st_ev).
      {
        admit.
      }
      destruct_conjs.

      assert (
           (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e') \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        apply H3.
        eassumption.
        eassumption.
        eassumption.
      }
      destruct H6.
      ++
        destruct_conjs.
        left.
        eauto.
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        eauto.
        eauto. *)
  -
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)

      destruct s; ff.
      ++

        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
        
        

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e4) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e4 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        3: { eassumption. }
        apply H0.
        2: { eassumption. }
        rewrite <- Heqo.
        cbn. tauto.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        eauto.
        (*
        left.
        eexists.
        apply ssSubl; eauto. *)
        
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubl; eauto.
          eauto. *)
      ++

        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
        
          
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e4) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e4 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        cbn. tauto.
        rewrite <- Heqo.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubl; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubl; eauto.
          eauto. *)
      ++

        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.




        
        
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e4) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e4 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        ff.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubl; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubl; eauto.
          eauto. *)
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      destruct s; ff.
      ++

        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e5) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e5 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        
        3: { eassumption. }
        3: { eassumption. }
        ff.
        ff.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubr; eauto.
          eauto. *)

      ++
        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e5) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e5 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        
        3: { eassumption. }
        3: { eassumption. }
        ff.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubr; eauto.
          eauto. *)

      ++
                assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e5) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e5 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        
        3: { eassumption. }
        3: { eassumption. }
        ff.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubr; eauto.
          eauto. *)

  -
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)

      destruct s; ff.
      ++

        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
        
        

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e4) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e4 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        3: { eassumption. }
        apply H0.
        2: { eassumption. }
        rewrite <- Heqo.
        cbn. tauto.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        eauto.
        (*
        left.
        eexists.
        apply ssSubl; eauto. *)
        
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubl; eauto.
          eauto. *)
      ++

        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
        
          
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e4) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e4 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        cbn. tauto.
        rewrite <- Heqo.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubl; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubl; eauto.
          eauto. *)
      ++

        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.




        
        
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e4) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e4 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        ff.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubl; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubl; eauto.
          eauto. *)
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      destruct s; ff.
      ++

        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e5) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e5 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        
        3: { eassumption. }
        3: { eassumption. }
        ff.
        ff.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubr; eauto.
          eauto. *)

      ++
        assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e5) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e5 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        
        3: { eassumption. }
        3: { eassumption. }
        ff.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubr; eauto.
          eauto. *)

      ++
                assert (firstn (et_size e1) (e0 ++ e2) = e0).
        {
          admit.
        }
        assert (skipn (et_size e1) (e0 ++ e2) = e2).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') e5) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) e5 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        
        3: { eassumption. }
        3: { eassumption. }
        ff.
        ff.
      }
      
      destruct H1.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubr; eauto.
          eauto. *)
Admitted.


















          
(*

          
      ++
        
          
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
      }
      
      destruct H0.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubr; eauto.
          eauto. *)
      ++
        
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
      }
      
      destruct H0.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ssSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ssSubr; eauto.
          eauto. *)

  -
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)

      destruct s; ff.
      ++

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') st_ev0) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
      }
      
      destruct H0.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ppSubl; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ppSubl; eauto.
          eauto. *)
      ++
        
          
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') st_ev0) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
      }
      
      destruct H0.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ppSubl; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ppSubl; eauto.
          eauto. *)
      ++
        
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') st_ev0) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
      }
      
      destruct H0.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ppSubl; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ppSubl; eauto.
          eauto. *)
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      destruct s; ff.
      ++

      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
      }
      
      destruct H0.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ppSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ppSubr; eauto.
          eauto. *)
      ++
        
          
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
      }
      
      destruct H0.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ppSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ppSubr; eauto.
          eauto. *)
      ++
        
      assert (
            (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (uu i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
      }
      
      destruct H0.
      +++
        destruct_conjs.
        left.
        eauto.
        (*
        eexists.
        apply ppSubr; eauto. *)
        (*
        assert (
            (EvSub (uuc i args tpl tid n H0) e) \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum.
          apply H2.
          eassumption.
          eassumption.
        }
        clear H1.
        destruct H4. 
        +++

          left.
          eauto. *)
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).
          (*
          apply ppSubr; eauto.
          eauto. *)
Defined.
Admitted.
*)


Lemma uu_preserved: forall t1 t2 p et n p0 i args tpl tid
                      e tr st_ev st_trace p'
                      e' tr' p'' ecc,
    well_formed_r t1 ->
    well_formed_r t2 ->
    Some e' = (reconstruct_ev ecc) -> (* = (Some e') -> *)
    events t1 p et (umeas n p0 i args tpl tid) ->
    copland_compile t1 {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |}) ->
    
    copland_compile t2
                    {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |} =
    (Some tt, {| st_ev := ecc; st_trace := tr'; st_pl := p'' |}) ->

    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid et') ett)
    ).
Proof.
  intros.
  assert (exists ee, Some ee = reconstruct_ev st_ev).
  {
    admit.
  }
  assert (exists ee, Some ee = reconstruct_ev e).
  {
    admit.
  }
  
  destruct_conjs.
  
  assert (
      (exists e'', EvSub (uuc i args tpl tid n e'') H5) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) H5 /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      apply H7.
      eassumption.
      eassumption.
      eassumption.
    }
  generalizeEverythingElse e'.
  induction e'; intros.

  

  
  -

    Ltac door :=
      match goal with
      | [H: _ \/ _  |- _] =>
        destruct H
      end; destruct_conjs.

    door.
    +

      

      assert (
           (EvSub (uuc i args tpl tid n H9) mtc) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) mtc /\
               EvSubT (et_fun (uuc i args tpl tid n H9)) ett
           )
        ).
      {
        eapply evAccum.
        apply H0.
        2: { eassumption. }
        apply H8.
        eassumption.
        eassumption.
        
      }
      destruct H11.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.
    +
      destruct_conjs.
       assert (
           (EvSub (hhc H10 H11 H9) mtc) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) mtc /\
               EvSubT (et_fun (hhc H10 H11 H9)) ett
           )
         ).
       {
         eapply evAccum.
         apply H0.
         2: { eassumption. }
         apply H8.
         eassumption.
         eassumption.
       }
       destruct H15.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.

  - (* nnc case *)

    (*
    assert (
      (exists e'', EvSub (uuc i args tpl tid n1 e'') st_ev) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) st_ev /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      eassumption.
      eassumption.
    } *)
    door.
    (*
    destruct H4. *)
    +
      destruct_conjs.

      assert (
           (EvSub (uuc i args tpl tid n1 H9) (nnc n n0)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (nnc n n0) /\
               EvSubT (et_fun (uuc i args tpl tid n1 H9)) ett
           )
        ).
      {
        eapply evAccum.
        apply H0.
        apply H8.
        eassumption.
        eassumption.
        eassumption.

      }
      door.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.
    +
      destruct_conjs.
       assert (
           (EvSub (hhc H10 H11 H9) (nnc n n0)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (nnc n n0) /\
               EvSubT (et_fun (hhc H10 H11 H9)) ett
           )
         ).
       {
        eapply evAccum.
        apply H0.
        apply H8.
        eassumption.
        eassumption.
        eassumption.

      }
      door.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.
      
  - (* uuc case *)
    (*
        
    assert (
      (exists e'', EvSub (uuc i args tpl tid n3 e'') st_ev) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) st_ev /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      eassumption.
      eassumption.
    } *)
    door.
    (*
    destruct H4. *)
    +
      destruct_conjs.

      assert (
           (EvSub (uuc i args tpl tid n3 H9) (uuc n l n0 n1 n2 e')) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (uuc n l n0 n1 n2 e') /\
               EvSubT (et_fun (uuc i args tpl tid n3 H9)) ett
           )
        ).
      {
        eapply evAccum.
        apply H0.
        apply H8.
        eassumption.
        eassumption.
        eassumption.
      }
      door.
      ++
        invc H11; eauto.
        (*
        +++
          left.
          eexists.
          econstructor.
        +++
          left.
          eexists.
          apply uuSub.
          eauto. *)
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +
      destruct_conjs.
       assert (
           (EvSub (hhc H10 H11 H9) (uuc n l n0 n1 n2 e')) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (uuc n l n0 n1 n2 e') /\
               EvSubT (et_fun (hhc H10 H11 H9)) ett
           )
         ).
       {
         eapply evAccum.
         eassumption.
         apply H8.
         eassumption.
         eassumption.
         eassumption.
       }
       door.
      ++
        invc H15.
        right.
        repeat eexists.
        apply uuSub.
        eassumption.
        eassumption.
      ++
        destruct_conjs.
        ff.
        invc H18.
        assert (EvSubT (uu i args tpl tid H12) H15).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        
        right.
        repeat eexists.
        apply uuSub.
        eassumption.
        eassumption.
  -
    (*
    assert (
      (exists e'', EvSub (uuc i args tpl tid n1 e'') st_ev) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) st_ev /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      eassumption.
      eassumption.
    }
    destruct H4.
     *)
    door.
    +
      destruct_conjs.

      assert (
           (EvSub (uuc i args tpl tid n1 H9) (ggc n n0 e')) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ggc n n0 e') /\
               EvSubT (et_fun (uuc i args tpl tid n1 H9)) ett
           )
        ).
      {
        eapply evAccum.
        eassumption.
        apply H8.
        eassumption.
        eassumption.
        eassumption.
      }
      door.
      ++
        invc H11.
        left.
        repeat eexists.
        apply ggSub; eauto.
        (*
        +++
          left.
          eexists.
          econstructor.
        +++
          left.
          eexists.
          apply uuSub.
          eauto. *)
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +
      destruct_conjs.
       assert (
           (EvSub (hhc H10 H11 H9) (ggc n n0 e')) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ggc n n0 e') /\
               EvSubT (et_fun (hhc H10 H11 H9)) ett
           )
         ).
       {
         eapply evAccum.
         eassumption.
         apply H8.
         eassumption.
         eassumption.
         eassumption.
       }
       door.
      ++
        invc H15.
        right.
        repeat eexists.
        apply ggSub.
        eassumption.
        eassumption.
      ++
        destruct_conjs.
        ff.
        invc H18.
        assert (EvSubT (uu i args tpl tid H12) H15).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        
        right.
        repeat eexists.
        apply ggSub.
        eassumption.
        eassumption.
  -

    (*
    assert (
      (exists e'', EvSub (uuc i args tpl tid n1 e'') st_ev) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) st_ev /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      eassumption.
      eassumption.
    }
    destruct H4.
     *)
    door.
    +
      destruct_conjs.

      assert (
           (EvSub (uuc i args tpl tid n1 H9) (hhc n n0 e)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (hhc n n0 e) /\
               EvSubT (et_fun (uuc i args tpl tid n1 H9)) ett
           )
        ).
      {
        eapply evAccum.
        eassumption.
        apply H8.
        eassumption.
        eassumption.
        eassumption.
      }
      door.
      ++
        invc H11.
        (*
        left.
        repeat eexists.
        apply ggSub; eauto.
        (*
        +++
          left.
          eexists.
          econstructor.
        +++
          left.
          eexists.
          apply uuSub.
          eauto. *)
         *)
        
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +
      destruct_conjs.
       assert (
           (EvSub (hhc H10 H11 H9) (hhc n n0 e)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (hhc n n0 e) /\
               EvSubT (et_fun (hhc H10 H11 H9)) ett
           )
         ).
       {
         eapply evAccum.
         eassumption.
         apply H8.
         eassumption.
         eassumption.
         eassumption.
       }
       door.
      ++
        invc H15.
        right.
        repeat eexists.
        econstructor.
        eauto.
        (*
        apply hhSub.
        eassumption.
        eassumption. *)
      ++
        destruct_conjs.
        ff.
        invc H18.
        assert (EvSubT (uu i args tpl tid H12) e).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        
        right.
        repeat eexists.
        econstructor.
        eassumption.

  - (* ssc case *)

    (*
    assert (
      (exists e'', EvSub (uuc i args tpl tid n e'') st_ev) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) st_ev /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      eassumption.
      eassumption.
    }
    destruct H4.
     *)
    door.
    +
      destruct_conjs.

      assert (
           (EvSub (uuc i args tpl tid n H9) (ssc e'1 e'2)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ssc e'1 e'2) /\
               EvSubT (et_fun (uuc i args tpl tid n H9)) ett
           )
        ).
      {
        eapply evAccum.
        eassumption.
        apply H8.
        eassumption.
        eassumption.
        eassumption.
      }
      door.
      ++
        invc H11.
        +++
        left.
        repeat eexists.
        apply ssSubl; eauto.
        +++
          left.
          repeat eexists.
          apply ssSubr; eauto.
        (*
        +++
          left.
          eexists.
          econstructor.
        +++
          left.
          eexists.
          apply uuSub.
          eauto. *)
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +
      destruct_conjs.
       assert (
           (EvSub (hhc H10 H11 H9) (ssc e'1 e'2)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ssc e'1 e'2) /\
               EvSubT (et_fun (hhc H10 H11 H9)) ett
           )
         ).
       {
         eapply evAccum.
         eassumption.
         apply H8.
         eassumption.
         eassumption.
         eassumption.
       }
       door.
      ++
        invc H15.
        +++
        right.
        repeat eexists.
        apply ssSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ssSubr.
          eassumption.
          eassumption.
      ++
        destruct_conjs.
        ff.
        assert (EvSubT (uu i args tpl tid H12) H15).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        invc H18.
        +++
        
        
        right.
        repeat eexists.
        apply ssSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ssSubr.
          eassumption.
          eassumption.


  - (* ppc case *)

    (*
    assert (
      (exists e'', EvSub (uuc i args tpl tid n e'') st_ev) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) st_ev /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      eassumption.
      eassumption.
    }
    destruct H4.
     *)
    door.
    +
      destruct_conjs.

      assert (
           (EvSub (uuc i args tpl tid n H9) (ppc e'1 e'2)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ppc e'1 e'2) /\
               EvSubT (et_fun (uuc i args tpl tid n H9)) ett
           )
        ).
      {
        eapply evAccum.
        eassumption.
        apply H8.
        eassumption.
        eassumption.
        eassumption.
      }
      door.
      ++
        invc H11.
        +++
        left.
        repeat eexists.
        apply ppSubl; eauto.
        +++
          left.
          repeat eexists.
          apply ppSubr; eauto.
        (*
        +++
          left.
          eexists.
          econstructor.
        +++
          left.
          eexists.
          apply uuSub.
          eauto. *)
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +
      destruct_conjs.
       assert (
           (EvSub (hhc H10 H11 H9) (ppc e'1 e'2)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ppc e'1 e'2) /\
               EvSubT (et_fun (hhc H10 H11 H9)) ett
           )
         ).
       {
         eapply evAccum.
         eassumption.
         apply H8.
         eassumption.
         eassumption.
         eassumption.
       }
       door.
      ++
        invc H15.
        +++
        right.
        repeat eexists.
        apply ppSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ppSubr.
          eassumption.
          eassumption.
      ++
        destruct_conjs.
        ff.
        assert (EvSubT (uu i args tpl tid H12) H15).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        invc H18.
        +++
        
        
        right.
        repeat eexists.
        apply ppSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ppSubr.
          eassumption.
          eassumption.




(*
          
          
  - (* ppc case *)
    (*
    assert (
      (exists e'', EvSub (uuc i args tpl tid n e'') st_ev) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) st_ev /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      eassumption.
      eassumption.
    }
    destruct H4.
     *)
    door.
    +
      destruct_conjs.

      assert (
           (EvSub (uuc i args tpl tid n H4) (ppc e'1 e'2)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ppc e'1 e'2) /\
               EvSubT (et_fun (uuc i args tpl tid n H4)) ett
           )
        ).
      {
        eapply evAccum; eauto.
      }
      destruct H6.
      ++
        invc H6.
        +++
        left.
        repeat eexists.
        apply ppSubl; eauto.
        +++
          left.
          repeat eexists.
          apply ppSubr; eauto.
        (*
        +++
          left.
          eexists.
          econstructor.
        +++
          left.
          eexists.
          apply uuSub.
          eauto. *)
      ++
        destruct_conjs.
        ff.
        right.
        repeat eexists.
        eauto.
        eauto.

    +
      destruct_conjs.
       assert (
           (EvSub (hhc H5 H6 H4) (ppc e'1 e'2)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ppc e'1 e'2) /\
               EvSubT (et_fun (hhc H5 H6 H4)) ett
           )
         ).
       {
         eapply evAccum; eauto.
       }
       destruct H10.
      ++
        invc H10.
        +++
        right.
        repeat eexists.
        apply ppSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ppSubr.
          eassumption.
          eassumption.
      ++
        destruct_conjs.
        ff.
        assert (EvSubT (uu i args tpl tid H7) H10).
        {
          eapply evsubT_transitive.
          apply hhSubT.
          eassumption.
          eassumption.
        }
        invc H13.
        +++
        
        
        right.
        repeat eexists.
        apply ppSubl.
        eassumption.
        eassumption.
        +++
          right.
          repeat eexists.
          apply ppSubr.
          eassumption.
          eassumption.
Defined.
*)
Admitted.


Lemma appraisal_correct : forall t e' tr tr' p p' et ev bits ecc,
    well_formed_r t ->
    wf_ec (evc bits et) ->
    (*Ev_Shape e et -> *)
    Some e' = (reconstruct_ev ecc) -> (*fromSome mtc (reconstruct_ev ecc) ->*) (* = (Some e') -> *)
    copland_compile t
      {| st_ev := (evc bits et); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc;
                 st_trace := tr';
                 st_pl := p' |}) ->

    measEvent t p et ev ->
    
    (*build_app_comp_evC e' = app_res /\ *)
    appEvent_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    measEventFacts.
    evEventFacts.
    inv_events.
    ff.
    break_match; try solve_by_inversion.
    invc H1.
    (*
    assert (exists x, reconstruct_ev' bits et = Some x).
    {
      admit.
    }
    destruct_conjs.
    
    rewrite H1.
     *)
    
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
    eassumption.

    eapply copland_compile_at.
    eassumption.
    econstructor.
    eassumption.
    econstructor.
  - (* alseq case *)
    edestruct wf_lseq_pieces;[eauto | idtac].
    (* do_wf_pieces. *)
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.

    measEventFacts.
    do_pl_immut.
    do_pl_immut.
    subst.

    invc H6.

    
    inv_events.
     + (* t1 case *)
       (*clear H0. *)

       assert (
           (exists e'', EvSub (uuc i args tpl tid n e'') (fromSome mtc (reconstruct_ev ecc))) \/
           (exists ett p' bs et',
               EvSub (hhc p' bs ett) (fromSome mtc (reconstruct_ev ecc)) /\
               EvSubT (uu i args tpl tid et') ett)
         ).
              
       {
         eapply uu_preserved.
         apply H4.
         apply H5.
         rewrite <- H1.
         ff.
         eassumption.
         eassumption.
         eassumption.
         eassumption.
       }
       destruct H3.
       ++

       destruct_conjs.



       assert (
        exists e'', EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e'')
                     (build_app_comp_evC (fromSome mtc (reconstruct_ev ecc)))).
       {
         eapply uuc_app; eauto.
       }
       destruct_conjs.
       econstructor.
       rewrite <- H1 in *.
       eassumption.
       ++
         rewrite <- H1 in *.
         ff.
         destruct_conjs.

         eapply ahuc.
         eassumption.
         (*
         apply H9. *)
         eapply hhc_app; eauto.
         (*

         assert (EvSub (hhc H2 (checkHash H1 H2 H5) H1) (build_app_comp_evC (fromSome mtc (reconstruct_ev ecc)))).
         {
           eapply hhc_app; eauto.
         }

         eapply ahuc.
         eassumption.
         eassumption. *)
     + (* t2 case *)
       assert (appEvent_EvidenceC (umeas n p0 i args tpl tid)
                                  (build_app_comp_evC (e'))).
       {
         destruct ecc.
         destruct st_ev.
         eapply IHt2.
         eassumption.

         eapply wf_ec_preserved_by_cvm.
         eassumption.
         eassumption.
         


         
         eassumption.
         eassumption.
         (*
         
         
         2: {
           eassumption.
         }      
         eapply cvm_refines_lts_evidence.
         apply H3.
         eassumption.
         eassumption.
         tauto. *)
         econstructor.
         Check eval_aeval.
         assert (e2 = aeval t1 p et).
         {
           rewrite <- eval_aeval.
           
           eapply cvm_refines_lts_evidence.
           eassumption.
           eassumption.
         }
         subst.
         eassumption.
         econstructor.
       }
       eassumption.
       
         (*
         
         rewrite eval_aeval.
         eassumption. 
         econstructor.
       }
       eassumption. *)
    - (* abseq case *)
    (*
    do_wf_pieces. *)
    edestruct wf_bseq_pieces;[eauto | idtac].
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    ff.

    (*

    assert (exists x, reconstruct_ev' (firstn (et_size e0) (e ++ e1)) e0 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H1. 

    assert (exists x, reconstruct_ev' (skipn (et_size e0) (e ++ e1)) e2 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H6.
     *)
    
    
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H2.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc := evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo.
        unfold reconstruct_ev. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9. *)


      (*
      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)
      
      

      invc H2.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor.
            ff.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor.
            ff.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.






        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:=evc e e0) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.




        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
*)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:= evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
       assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
    + (* t2 case *)

      destruct s.
      ++
        ff.



        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.


        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor. ff.
            eassumption.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor. ff.
            eassumption.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
         *)
        

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2).
        eassumption.
        eassumption.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2).
        eassumption.
        eassumption.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.

    - (* abpar case *)
    (*
    do_wf_pieces. *)
    edestruct wf_bpar_pieces;[eauto | idtac].
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    ff.

    (*

    assert (exists x, reconstruct_ev' (firstn (et_size e0) (e ++ e1)) e0 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H1. 

    assert (exists x, reconstruct_ev' (skipn (et_size e0) (e ++ e1)) e2 = Some x).
    {
      admit.
    }
    destruct_conjs.
    rewrite H6.
     *)
    
    
    repeat ff.

    vmsts.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H2.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc := evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo.
        unfold reconstruct_ev. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9. *)


      (*
      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)
      
      

      invc H2.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor.
            ff.
            eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            unfold mt_evc in *.
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor.
            ff.
            eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.






        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:=evc e e0) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.




        
(*
         assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
*)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        eapply IHt1 with (ecc:= evc e e0).
        eassumption.
        eassumption.
        rewrite <- Heqo. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
       assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H1 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
    + (* t2 case *)

      destruct s.
      ++
        ff.



        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.

        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2) (bits:=[0]) (et:=mt).
        eassumption.
        econstructor. ff.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.


        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor. ff.
            eassumption.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm with (bits:=[0]) (et:=mt).
            econstructor. ff.
            eassumption.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2.
         *)
        

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2).
        eassumption.
        eassumption.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*
      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H2.
          rewrite <- H6.
          eapply More_lists.firstn_append.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          assert (wf_ec (evc e e0)).
          {
            eapply wf_ec_preserved_by_cvm; eauto.
          }
          invc H3.
          rewrite <- H7.
          eapply More_lists.skipn_append.
        }
        rewrite H2 in *; clear H2.
        rewrite H3 in *; clear H3.


        (*

        assert (firstn (et_size e0) (e ++ e1) = e).
        {
          admit.
        }
        assert (skipn (et_size e0) (e ++ e1) = e1).
        {
          admit.
        }
        rewrite H1 in *; clear H1.
        rewrite H2 in *; clear H2. *)

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        eapply IHt2 with (ecc:=evc e1 e2).
        eassumption.
        eassumption.
        rewrite <- Heqo0. tauto.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      (*

      assert (firstn (et_size e0) (e ++ e1) = e).
      {
        admit.
      }
      assert (skipn (et_size e0) (e ++ e1) = e1).
      {
        admit.
      }
      rewrite H8 in *. clear H8.
      rewrite H9 in *. clear H9.

      unfold reconstruct_ev in H2.
      rewrite H6 in H2.
      ff. *)

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
Defined.    

(*



        
    - (* abpar case *)
    (*
    do_wf_pieces. *)
    edestruct wf_bpar_pieces;[eauto | idtac].
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
    invc H5.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
      {
        eapply IHt1.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
      ++
        ff.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        econstructor.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.
    + (* t2 case *)

      destruct s.
      ++
        ff.

      
      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
      {
        eapply IHt2.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
      ++
        ff.

      
        assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
        econstructor.
        eassumption.
        econstructor.
      }

      invc H2.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ppSubr.
        eassumption.
Defined.
*)

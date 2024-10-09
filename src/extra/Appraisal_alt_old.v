Require Import Maps Event_system Term_system MonadVM ConcreteEvidenceT.
Require Import Impl_vm Helpers_VmSemantics VmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp.

Require Import StAM Appraisal_Defs Impl_appraisal_alt (*MonadAM*).

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Set Nested Proofs Allowed.

(*
Fixpoint reconstruct_EvCon (e:EvidenceTC) (et:EvidenceT): option EvidenceTCon :=
  match et with
  | mt_evt=>
    match e with
    | BitsV 0 => ret mtc
    | _ => None
    end
  | asp_evt i args tpl tid et' =>
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
  | nonce_evt nid =>
    bs <- peelOneBitsVval e ;;
    ret (nnc nid bs)
  | split_evt et1 et2 =>
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

(*
Lemma uuc_app: forall e' e'' i args tpl tid n,
    build_app_comp_evC et ls = Some res ->
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
*)

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

(*
Lemma evAccum: forall t p e e' e'' tr tr' p',

    well_formed_r t ->
    EvSub e'' e ->
    copland_compile t {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_trace := tr'; st_pl := p' |}) ->

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
      (ff; eauto).
    +
      right.
      repeat eexists.
      econstructor.

      
      apply evsub_etfun; eauto.
  -
    do_wf_pieces.
    ff.
    
    eapply IHt.
    eassumption.
    eassumption.
    apply copland_compile_at.
    eassumption.
  -
    ff.
    dosome.
    ff.
    vmsts.

    do_wf_pieces.

    assert (EvSub e'' st_ev \/
         (exists (ett : EvidenceT) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (et_fun e'') ett)).
    {
      eauto.
    }
    destruct H3.
    +

      assert (EvSub e'' e' \/
         (exists (ett : EvidenceT) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett)).
      {
        eauto.
    }
    destruct H4.
      ++
        eauto.
        (*
        eapply IHt2.
        eassumption.
        apply H3.
        eassumption. *)
      ++
        destruct_conjs.
        right.
        repeat eexists.
        eauto.
        eauto.
    +
      destruct_conjs.
      assert (EvSub (hhc H4 H5 H3) e' \/
         (exists (ett : EvidenceT) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun (hhc H4 H5 H3)) ett)).
    {
      eapply IHt2.
      eassumption.
      eassumption.
      eassumption.
    }
    destruct H8.
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
        exists H8.
        repeat eexists.
        eassumption.
        assert (EvSubT (et_fun e'') (hh H4 H3)).
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

    destruct s.
    +
      ff.
      assert (
           EvSub e'' st_ev0 \/
         (exists (ett : EvidenceT) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (et_fun e'') ett)
        ) by eauto.
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
           EvSub e'' st_ev \/
         (exists (ett : EvidenceT) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (et_fun e'') ett)
        ) by eauto.
      destruct H1.
      ++
        eauto.
        (*
        left.
        apply ssSubr; eauto. *)
      ++
        destruct_conjs.
        right.
        repeat (eexists; eauto).
        (*
        apply ssSubr.
        eassumption.
        eassumption. *)
    +
      ff.
      assert (
           EvSub e'' st_ev0 \/
         (exists (ett : EvidenceT) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (et_fun e'') ett)
        ) by eauto.
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
        eauto.
        eauto.
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

    destruct s.
    +
      ff.
      assert (
           EvSub e'' st_ev0 \/
         (exists (ett : EvidenceT) (p'0 bs : nat),
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
         (exists (ett : EvidenceT) (p'0 bs : nat),
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
         (exists (ett : EvidenceT) (p'0 bs : nat),
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
Defined.

Lemma uu_preserved': forall t p et n p0 i args tpl tid
                       e tr e' tr' p',

    well_formed_r t ->
    events t p et (umeas n p0 i args tpl tid) ->
    copland_compile t {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := e'; st_trace := tr'; st_pl := p' |}) ->

    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (asp_evt i args tpl tid et') ett)
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
      left.
      eexists.
      econstructor.
  -
    ff.
    invEvents.
    do_wf_pieces.
    assert (
         (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n0 e'')  (toRemote t n e)) \/
        (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
            EvSub (hhc p'0 bs ett)  (toRemote t n e) /\ EvSubT (asp_evt i args tpl tid et') ett)
      ).

    {
      eapply IHt.
           
    eassumption.
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

      assert (
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (asp_evt i args tpl tid et') ett)
        ).
      {
        eapply IHt1.
        eassumption.
        eassumption.
        eassumption.
      }
      destruct_conjs.
      destruct H0.
      ++
        destruct_conjs.
        assert (
            (EvSub (uuc i args tpl tid n H0) e') \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e' /\
                EvSubT (et_fun (uuc i args tpl tid n H0)) ett
            )
          ).
        {
          eapply evAccum; eauto.
        }
        clear H1.
        destruct H4.
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
            (EvSub (hhc H1 H4 H0) e') \/
            (exists ett p' bs,
                EvSub (hhc p' bs ett) e' /\
                EvSubT (et_fun (hhc H1 H4 H0)) ett
            )
          ).
        {
          eapply evAccum; eauto.
        }
        destruct H8.
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

          assert (EvSubT (asp_evt i args tpl tid H5) (hh H1 H0)).
          {
            apply hhSubT.
            eassumption.
          }

          
          

          eapply evsubT_transitive.
          apply H14.
          eassumption.
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      assert (
           (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') e') \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (asp_evt i args tpl tid et') ett)
        ).
      {
        eapply IHt2.
        eassumption.
        eassumption.
        eassumption.
      }
      destruct H0.
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

      assert (
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev0) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (asp_evt i args tpl tid et') ett)
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
        
          
      assert (
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev0) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (asp_evt i args tpl tid et') ett)
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
        
      assert (
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev0) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (asp_evt i args tpl tid et') ett)
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

      assert (
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (asp_evt i args tpl tid et') ett)
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
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (asp_evt i args tpl tid et') ett)
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
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (asp_evt i args tpl tid et') ett)
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
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev0) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (asp_evt i args tpl tid et') ett)
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
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev0) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (asp_evt i args tpl tid et') ett)
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
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev0) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev0 /\ EvSubT (asp_evt i args tpl tid et') ett)
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
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (asp_evt i args tpl tid et') ett)
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
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (asp_evt i args tpl tid et') ett)
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
            (exists e'' : EvidenceTC, EvSub (uuc i args tpl tid n e'') st_ev) \/
         (exists (ett : EvidenceT) (p'0 bs : nat) (et' : EvidenceT),
             EvSub (hhc p'0 bs ett) st_ev /\ EvSubT (asp_evt i args tpl tid et') ett)
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

Lemma uu_preserved: forall t1 t2 p et n p0 i args tpl tid
                      e tr st_ev st_trace p'
                      e' tr' p'',
    well_formed_r t1 ->
    well_formed_r t2 ->
    events t1 p et (umeas n p0 i args tpl tid) ->
    copland_compile t1 {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |}) ->
    
    copland_compile t2
                    {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |} =
    (Some tt, {| st_ev := e'; st_trace := tr'; st_pl := p'' |}) ->

    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (asp_evt i args tpl tid et') ett)
    ).
Proof.
  intros.
  assert (
      (exists e'', EvSub (uuc i args tpl tid n e'') st_ev) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) st_ev /\
          EvSubT (asp_evt i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
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
           (EvSub (uuc i args tpl tid n H4) mtc) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) mtc /\
               EvSubT (et_fun (uuc i args tpl tid n H4)) ett
           )
        ).
      {
        eapply evAccum; eauto.
      }
      destruct H6.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.
    +
      destruct_conjs.
       assert (
           (EvSub (hhc H5 H6 H4) mtc) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) mtc /\
               EvSubT (et_fun (hhc H5 H6 H4)) ett
           )
         ).
       {
         eapply evAccum; eauto.
       }
       destruct H10.
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
          EvSubT (asp_evt i args tpl tid et') ett)
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
           (EvSub (uuc i args tpl tid n1 H4) (nnc n n0)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (nnc n n0) /\
               EvSubT (et_fun (uuc i args tpl tid n1 H4)) ett
           )
        ).
      {
        eapply evAccum; eauto.
      }
      destruct H6.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion.
    +
      destruct_conjs.
       assert (
           (EvSub (hhc H5 H6 H4) (nnc n n0)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (nnc n n0) /\
               EvSubT (et_fun (hhc H5 H6 H4)) ett
           )
         ).
       {
         eapply evAccum; eauto.
       }
       destruct H10.
      ++
        solve_by_inversion.
      ++
        destruct_conjs.
        solve_by_inversion. 
      
  -
    (*
        
    assert (
      (exists e'', EvSub (uuc i args tpl tid n3 e'') st_ev) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) st_ev /\
          EvSubT (asp_evt i args tpl tid et') ett)
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
           (EvSub (uuc i args tpl tid n3 H4) (uuc n l n0 n1 n2 e')) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (uuc n l n0 n1 n2 e') /\
               EvSubT (et_fun (uuc i args tpl tid n3 H4)) ett
           )
        ).
      {
        eapply evAccum; eauto.
      }
      destruct H6.
      ++
        invc H6; eauto.
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
           (EvSub (hhc H5 H6 H4) (uuc n l n0 n1 n2 e')) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (uuc n l n0 n1 n2 e') /\
               EvSubT (et_fun (hhc H5 H6 H4)) ett
           )
         ).
       {
         eapply evAccum; eauto.
       }
       destruct H10.
      ++
        invc H10.
        right.
        repeat eexists.
        apply uuSub.
        eassumption.
        eassumption.
      ++
        destruct_conjs.
        ff.
        invc H13.
        assert (EvSubT (asp_evt i args tpl tid H7) H10).
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
          EvSubT (asp_evt i args tpl tid et') ett)
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
           (EvSub (uuc i args tpl tid n1 H4) (ggc n n0 e')) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ggc n n0 e') /\
               EvSubT (et_fun (uuc i args tpl tid n1 H4)) ett
           )
        ).
      {
        eapply evAccum; eauto.
      }
      destruct H6.
      ++
        invc H6.
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
           (EvSub (hhc H5 H6 H4) (ggc n n0 e')) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ggc n n0 e') /\
               EvSubT (et_fun (hhc H5 H6 H4)) ett
           )
         ).
       {
         eapply evAccum; eauto.
       }
       destruct H10.
      ++
        invc H10.
        right.
        repeat eexists.
        apply ggSub.
        eassumption.
        eassumption.
      ++
        destruct_conjs.
        ff.
        invc H13.
        assert (EvSubT (asp_evt i args tpl tid H7) H10).
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
          EvSubT (asp_evt i args tpl tid et') ett)
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
           (EvSub (uuc i args tpl tid n1 H4) (hhc n n0 e)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (hhc n n0 e) /\
               EvSubT (et_fun (uuc i args tpl tid n1 H4)) ett
           )
        ).
      {
        eapply evAccum; eauto.
      }
      destruct H6.
      ++
        invc H6.
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
           (EvSub (hhc H5 H6 H4) (hhc n n0 e)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (hhc n n0 e) /\
               EvSubT (et_fun (hhc H5 H6 H4)) ett
           )
         ).
       {
         eapply evAccum; eauto.
       }
       destruct H10.
      ++
        invc H10.
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
        invc H13.
        assert (EvSubT (asp_evt i args tpl tid H7) e).
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
          EvSubT (asp_evt i args tpl tid et') ett)
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
           (EvSub (uuc i args tpl tid n H4) (ssc e'1 e'2)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ssc e'1 e'2) /\
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
           (EvSub (hhc H5 H6 H4) (ssc e'1 e'2)) \/
           (exists ett p' bs,
               EvSub (hhc p' bs ett) (ssc e'1 e'2) /\
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
        assert (EvSubT (asp_evt i args tpl tid H7) H10).
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
          EvSubT (asp_evt i args tpl tid et') ett)
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
        assert (EvSubT (asp_evt i args tpl tid H7) H10).
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

Lemma appraisal_correct : forall t bits bits' et et' tr tr' p p' ev app_res,
    well_formed_r t ->
    (*Ev_Shape e et -> *)
    copland_compile t
      {| st_ev := (evc bits et); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := (evc bits' et');
                 st_trace := tr';
                 st_pl := p' |}) ->

    measEvent t p et ev ->
    
    (*build_app_comp_evC e' = app_res /\ *)
    build_app_comp_evC (aeval t p et) bits' = Some app_res ->
    appEvent_EvidenceTC ev app_res.
Proof.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    measEventFacts.
    evEventFacts.
    inv_events.
    ff.
    repeat break_match; try solve_by_inversion.
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
    
    4:
    {
      eassumption.
    }
    eassumption.
    rewrite <- H3.
    
    Check copland_compile_at.

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

    invc H5.

    
    inv_events.
     + (* t1 case *)
       clear H0.

       assert (
           (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
           (exists ett p' bs et',
               EvSub (hhc p' bs ett) e' /\
               EvSubT (asp_evt i args tpl tid et') ett)
         ).
              
       {
         eapply uu_preserved.
         apply H3.
         apply H4.
         eassumption.
         eassumption.
         eassumption.
       }
       destruct H1.
       ++

       destruct_conjs.



       assert (
        exists e'', EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e'')
                     (build_app_comp_evC e')).
       {
         eapply uuc_app; eauto.
       }
       destruct_conjs.
       econstructor.
       eassumption.
       ++
         destruct_conjs.

         assert (EvSub (hhc H2 (checkHash H1 H2 H5) H1) (build_app_comp_evC e')).
         {
           eapply hhc_app; eauto.
         }

         eapply ahuc.
         eassumption.
         eassumption.
     + (* t2 case *)
       assert (appEvent_EvidenceTC (umeas n p0 i args tpl tid)
                                  (build_app_comp_evC e')).
       {
         eapply IHt2.
         eassumption.
         2: {
           eassumption.
         }         
         eapply cvm_refines_lts_EvidenceT.
         apply H3.
         eassumption.
         eassumption.
         tauto.
         econstructor.
         rewrite eval_aeval.
         eassumption.
         econstructor.
       }
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
    invc H5.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.

      
        assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.

      
        assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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

      
        assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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

      
        assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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


(*
Lemma appraisal_correct : forall t e e' tr tr' p p' et ev,
    well_formed_r t ->
    Ev_Shape e et ->
    copland_compile t
      {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := e';
                 st_trace := tr';
                 st_pl := p' |}) ->

    measEvent t p et ev ->
    
    (*build_app_comp_evC e' = app_res /\ *)
    appEvent_EvidenceTC ev (build_app_comp_evC e').
Proof.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    measEventFacts.
    evEventFacts.
    inv_events.
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

    invc H5.

    
    inv_events.
     + (* t1 case *)
       clear H1.

       assert (
           (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
           (exists ett p' bs et',
               EvSub (hhc p' bs ett) e' /\
               EvSubT (asp_evt i args tpl tid et') ett)
         ).
              
       {
         eapply uu_preserved.
         apply H3.
         apply H4.
         eassumption.
         eassumption.
         eassumption.
       }
       destruct H1.
       ++

       destruct_conjs.



       assert (
        exists e'', EvSub (uuc i args tpl tid (checkASP i args tpl tid n) e'')
                     (build_app_comp_evC e')).
       {
         eapply uuc_app; eauto.
       }
       destruct_conjs.
       econstructor.
       eassumption.
       ++
         destruct_conjs.

         assert (EvSub (hhc H2 (checkHash H1 H2 H5) H1) (build_app_comp_evC e')).
         {
           eapply hhc_app; eauto.
         }

         eapply ahuc.
         eassumption.
         eassumption.
     + (* t2 case *)
       assert (appEvent_EvidenceTC (umeas n p0 i args tpl tid)
                                  (build_app_comp_evC e')).
       {
         eapply IHt2.
         eassumption.
         2: {
           eassumption.
         }         
         eapply cvm_refines_lts_EvidenceT.
         apply H3.
         eassumption.
         eassumption.
         tauto.
         econstructor.
         rewrite eval_aeval.
         eassumption.
         econstructor.
       }
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
    invc H5.

    
    inv_events;
      ff.
    + (* t1 case *)
      destruct s.
      ++
        ff.

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.

      
        assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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
        apply ssSubr.
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        apply ssSubr.
        eassumption.
      ++
        ff.

      
        assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev0)).
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

      
      assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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

      
        assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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

      
        assert (appEvent_EvidenceTC (umeas n1 p0 i args tpl tid) (build_app_comp_evC st_ev)).
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

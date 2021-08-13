Require Import Maps Event_system Term_system MonadVM ConcreteEvidence.
Require Import Impl_vm Helpers_VmSemantics VmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp.

Require Import StAM Appraisal_Defs Impl_appraisal (*MonadAM*).

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Require Import Lia.

(*
Require Import Impl_appraisal_alt. *)

Set Nested Proofs Allowed.

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
  induction e1; intros;
    repeat ff;
    repeat jkjke.
Defined.

(*
Inductive wf_ec : EvC -> Prop :=
| wf_ec_c: forall ls et,
    length ls = et_size et ->
    wf_ec (evc ls et).
*)

Ltac dest_evc :=
  repeat
    match goal with
    | [H: EvC |-  _ ] => destruct H
    end.

Ltac find_wfec :=
  repeat 
    match goal with
    | [H: context [well_formed_r ?t -> _](*
                   wf_ec _ ->
                   copland_compile _ _ _ = _ ->
                   wf_ec _]*),
          H2: well_formed_r ?t,
              H3: wf_ec ?e,
                  H4: copland_compile ?t
                                      {| st_ev := ?e; st_trace := _; st_pl := _ |} =
                      (_, {| st_ev := ?e'; st_trace := _; st_pl := _ |})
       |- _ ] => 
      assert_new_proof_by
        (wf_ec e')
        
        ltac:(eapply H; [apply H2 | apply H3 | apply H4])
    end.

Ltac inv_wfec :=
  repeat
    match goal with
    | [H: wf_ec _ |-  _ ] => invc H
    end.

Lemma wfec_split: forall e s,
    wf_ec e ->
    wf_ec (splitEv_l s e) /\ wf_ec (splitEv_r s e).
Proof.
  intros.
  split;
    destruct s; ff; try unfold mt_evc; ff;
      econstructor; ff.
Defined.

Ltac do_wfec_split :=
  match goal with
  | [H: context[splitEv_l ?s ?e],
        H2: context[splitEv_r ?s ?e],
            H3: wf_ec ?e
     |- _] =>
    
    assert_new_proof_by
      (wf_ec (splitEv_l s e) /\ wf_ec (splitEv_r s e))
      ltac: (eapply wfec_split; apply H3)
  end; destruct_conjs.

Lemma wf_ec_preserved_by_cvm : forall e e' t1 tr tr' p p',
    well_formed_r t1 ->
    wf_ec e ->
    copland_compile t1
                    {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt,
     {| st_ev := e'; st_trace := tr'; st_pl := p' |}) ->
    wf_ec (e').
Proof.
  intros.
  generalizeEverythingElse t1.
  induction t1; intros.
  -
    destruct a; ff;
      invc H0;
      try (
          econstructor;
          ff;
          try tauto;
          try congruence).  
  -
    ff.
    do_wf_pieces.

    eapply IHt1;
      try eassumption.

    apply copland_compile_at;
      try eassumption.
  -
    repeat ff.
    vmsts.
    do_wf_pieces.
  -
    repeat ff; vmsts; subst.
    do_wf_pieces.

    do_wfec_split.

    find_wfec;
      inv_wfec;
      ff;
      econstructor;
      ff; repeat jkjke';
        eapply app_length.

  -
    repeat ff; vmsts; subst.
    do_wf_pieces.

    do_wfec_split.

    find_wfec;
      inv_wfec;
      ff;
      econstructor;
      ff; repeat jkjke';
        eapply app_length.   
Defined.

Ltac do_wfec_preserved :=
  repeat
    match goal with
    | [H: well_formed_r ?t,
          H2: wf_ec ?stev,
              H3: copland_compile ?t
                                  {| st_ev := ?stev; st_trace := _; st_pl := _ |} =
                  (Some tt,
                   {| st_ev := ?stev'; st_trace := _; st_pl := _ |})
       |- _ ] =>
      assert_new_proof_by (wf_ec stev')
                          ltac:(eapply wf_ec_preserved_by_cvm; [apply H | apply H2 | apply H3])
                                 
    end.

Lemma cvm_evidence_size : forall t tr tr' bits bits' et et' p p',
    well_formed_r t ->
    copland_compile t (mk_st (evc bits et) tr p) = (Some tt, (mk_st (evc bits' et') tr' p')) ->
    Ev_Shape' bits et ->
    (*
    Term_Defs.eval (unanno t) p es = e's -> *)
    (*et' = (Term_Defs.eval (unanno t) p et) /\ *)
    Ev_Shape' bits' (Term_Defs.eval (unanno t) p et).

Proof.
  intros.
  unfold Ev_Shape' in *.
  assert (et' = (Term_Defs.eval (unanno t) p et)).
  {
    eapply cvm_refines_lts_evidence; eauto.
  }
  jkjke'.
  assert (wf_ec (evc bits et)).
  {
    econstructor.
    tauto.
  }
  
  do_wfec_preserved.
  invc H4.
  tauto.
Defined.

Lemma some_recons' : forall e x,
    length e = S x ->
    exists bs ls', peel_bs e = Some (bs, ls').
Proof.
  intros.
  destruct e;
    ff; eauto.
Defined.

Ltac do_some_recons' :=
  match goal with
  | [H: length ?e = S _ |- _ ] =>
    edestruct some_recons'; [apply H | idtac]
                              
  end; destruct_conjs; jkjke.

Ltac do_rcih :=
  match goal with
  | [H: context[reconstruct_ev' _ _]
               

     |- context[reconstruct_ev' ?e' ?et] ] =>
    assert_new_proof_by
      (exists x, Some x = reconstruct_ev' e' et)
      ltac:(eapply H with (e:=e');
            try (eapply peel_fact; eauto; tauto);
            try (econstructor; first [eapply firstn_long | eapply skipn_long]; try eauto; try lia))      
  end.

Lemma some_recons : forall e,
    wf_ec e ->
    exists ee, Some ee = reconstruct_ev e.
Proof.
  intros.
  destruct e.
  generalizeEverythingElse e0.
  induction e0; intros;
    try (ff; eauto; tauto);
    try
      ( inv_wfec; ff;
        do_some_recons');
    try (
        repeat do_rcih;
        destruct_conjs;
        repeat jkjke');
    try ( inv_wfec; ff;
          repeat do_rcih;
          destruct_conjs;
          repeat jkjke').
  assert (e = []).
  { destruct e; try solve_by_inversion. }
  ff.
  eauto.
  destruct e; try solve_by_inversion.
  ff.
  destruct e; try solve_by_inversion.
  ff.
Defined.

Ltac do_somerecons :=
  repeat
    match goal with
    | [H: wf_ec ?e
       |- _ ] =>
      assert_new_proof_by
        (exists x, Some x = reconstruct_ev e)
        ltac:(eapply some_recons; apply H)     
    end; destruct_conjs.

Ltac door :=
  match goal with
  | [H: _ \/ _  |- _] =>
    destruct H
  end; destruct_conjs.

Ltac do_evsub_ih :=
  match goal with
  | [H: copland_compile ?t1 {| st_ev := _; st_trace := _; st_pl := _ |} =
        (Some tt, {| st_ev := ?stev; st_trace := _; st_pl := _ |}),
        
        H2: copland_compile ?t2 {| st_ev := ?stev'; st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?v = reconstruct_ev ?stev

     |- context[EvSub ?e'' _ \/ _]] =>
    
    assert_new_proof_by
      (EvSub e'' v \/
       (exists (ett : Evidence) (p'0 bs : nat),
           EvSub (hhc p'0 bs ett) v /\ EvSubT (et_fun e'') ett))
      eauto
  end.

Ltac do_evsubh_ih :=
  match goal with
  | [H: EvSub (hhc ?H2 ?H3 ?H4) _

     |- context[EvSub _ ?e' \/ _]] =>
    
    assert_new_proof_by
      (EvSub (hhc H2 H3 H4) e' \/
       (exists (ett : Evidence) (p'0 bs : nat),
           EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun (hhc H2 H3 H4)) ett))
      eauto
  end.

Ltac do_hh_sub :=
  match goal with
  | [H: context[(hh ?H2 ?H3)]

     |- context[EvSubT ?e'' _]] =>
    
    assert_new_proof_by
      (EvSubT e'' (hh H2 H3))
      ltac: (eapply evsubT_transitive; eauto)
  end.

Lemma wfec_firstn: forall e0 e1 e2,
    wf_ec (evc e0 e1) ->
    firstn (et_size e1) (e0 ++ e2) = e0.
Proof.
  intros.
  inv_wfec.
  jkjke'.
  eapply More_lists.firstn_append.
Defined.

Ltac do_wfec_firstn :=
  match goal with
  | [H: context[(firstn (et_size ?e1) (?e0 ++ ?e2))],
        H2: wf_ec (evc ?e0 ?e1)

     |- _] =>
    
    assert_new_proof_by
      (firstn (et_size e1) (e0 ++ e2) = e0)
      ltac: (eapply wfec_firstn; apply H2)
  end.

Lemma wfec_skipn: forall e0 e1 e2,
    wf_ec (evc e0 e1) ->
    skipn (et_size e1) (e0 ++ e2) = e2.
Proof.
  intros.
  inv_wfec.
  jkjke'.
  eapply More_lists.skipn_append.
Defined.

Ltac do_wfec_skipn :=
  match goal with
  | [H: context[(skipn (et_size ?e1) (?e0 ++ ?e2))],
        H2: wf_ec (evc ?e0 ?e1)

     |- _] =>
    
    assert_new_proof_by
      (skipn (et_size e1) (e0 ++ e2) = e2)
      ltac: (eapply wfec_skipn; apply H2)
  end.

Lemma fold_recev: forall e0 e1,
    reconstruct_ev' e0 e1 = reconstruct_ev (evc e0 e1).
Proof.
  ff.
  tauto.
Defined.

Ltac clear_skipn_firstn :=
  match goal with
  | [H: firstn _ _ = _,
        H2: skipn _ _ = _ |- _]
    => rewrite H in *; clear H;
      rewrite H2 in *; clear H2
  end.

Inductive term_sub : AnnoTerm -> AnnoTerm -> Prop :=
| termsub_refl: forall t: AnnoTerm, term_sub t t
| aatt_sub: forall t t' r p,
    term_sub t' t ->
    term_sub t' (aatt r p t)
| alseq_subl: forall t' t1 t2 r,
    term_sub t' t1 ->
    term_sub t' (alseq r t1 t2)
| alseq_subr: forall t' t1 t2 r,
    term_sub t' t2 ->
    term_sub t' (alseq r t1 t2)
| abseq_subl: forall t' t1 t2 r s,
    term_sub t' t1 ->
    term_sub t' (abseq r s t1 t2)
| abseq_subr: forall t' t1 t2 r s,
    term_sub t' t2 ->
    term_sub t' (abseq r s t1 t2)
| abpar_subl: forall t' t1 t2 r s,
    term_sub t' t1 ->
    term_sub t' (abpar r s t1 t2)
| abpar_subr: forall t' t1 t2 r s,
    term_sub t' t2 ->
    term_sub t' (abpar r s t1 t2).

Definition none_none_term (t:AnnoTerm): Prop :=
  (exists t1 t2 r,
      t = abseq r (NONE,NONE) t1 t2)
  \/
  (exists t1 t2 r,
      t = abpar r (NONE,NONE) t1 t2).

Definition not_none_none (t:AnnoTerm) :=
  forall t',
    none_none_term t' ->
  ~ (term_sub t' t).
             

Lemma evAccum: forall t p (e e' e'':EvidenceC) tr tr' p' (ecc ecc':EvC),

    well_formed_r t ->
    not_none_none t ->
    wf_ec ecc ->
    Some e =  (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->
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
      repeat ff;
      try jkjke';
      try unfold cons_uu in *;
      try unfold cons_gg in *;
      (repeat ff; try eauto).
    +
      right.
      repeat eexists.
      econstructor.
      assert (e1 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.

      apply evsub_etfun; eauto.
  - (* aatt case *)
    do_wf_pieces.
    ff.
    unfold not_none_none in H0.
    
    eapply IHt.
    eassumption.
    2: {
      apply H1.
    }
    2: {
      eassumption. }
    2: {
    
      eassumption. }
    2: {
      eassumption. }
    2: {
      apply copland_compile_at.
      eassumption.
    }
    unfold not_none_none.
    intros.
    unfold not. intros.
    specialize H0 with (t':=t').
    concludes.
    unfold not in *.
    apply H0.
    econstructor.
    eassumption.

  - (* alseq case *)
    ff.
    dosome.
    vmsts.

    do_wf_pieces.

    do_wfec_preserved.

    do_somerecons.


    (*
Ltac do_evsub_ih :=
  match goal with
  | [H: copland_compile ?t1 {| st_ev := _; st_trace := _; st_pl := _ |} =
        (Some tt, {| st_ev := ?stev; st_trace := _; st_pl := _ |}),
        
        H2: copland_compile ?t2 {| st_ev := ?stev'; st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}),
            H3: Some ?v = reconstruct_ev ?stev

     |- context[EvSub ?e'' _ \/ _]] =>
    
    assert_new_proof_by
      (EvSub e'' v \/
       (exists (ett : Evidence) (p'0 bs : nat),
           EvSub (hhc p'0 bs ett) v /\ EvSubT (et_fun e'') ett))
      eauto
  end.
     *)

    assert (not_none_none t1).
    {
      unfold not_none_none in *.
      intros.
      unfold not in *.
      intros.
      specialize H0 with (t':=t').
      apply H0.
      eassumption.
      econstructor.
      eassumption. }
    assert (not_none_none t2).
    {
      unfold not_none_none in *.
      intros.
      unfold not in *.
      intros.
      specialize H0 with (t':=t').
      apply H0.
      eassumption.
      apply alseq_subr.
      eassumption. }

    (*
    unfold not_none_none in *.


    assert
      (EvSub e'' H10 \/
       (exists (ett:Evidence) (p'0 bs: nat),
           EvSub (hhc p'0 bs ett) H10 /\ EvSubT (et_fun e'') ett)).
    {
      eapply IHt1.
      eassumption.
      intros.
      specialize H0 with (t':=t').
      concludes.
      unfold not in *; intros.
      apply H0.
      econstructor.
      eassumption.
      3: { eassumption. }
      3: { eassumption. }
      3: { eassumption. }
      eassumption.
      eassumption.
    }
     *)

    do_evsub_ih.
    
    
    door.
    +
      eapply IHt2 with (ecc:=st_ev); eauto.

      (*
      intros.
      specialize H0 with (t':=t').
      unfold not in *.
      intros.
      apply H0.
      eassumption.
      apply alseq_subr.
      eassumption. *)
    +

      


      
      do_evsubh_ih.
      
      door.
      ++
        right.
        repeat (eexists; eauto).
      ++
        destruct_conjs.
        ff.
        
        right.
        repeat (eexists; eauto).
        do_hh_sub.
        eapply evsubT_transitive; eauto.
  - (* abseq case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
    subst.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.
    
    clear_skipn_firstn.

    do_wfec_preserved.

    do_somerecons.

    assert (not_none_none t1).
    {
      unfold not_none_none in *.
      intros.
      unfold not in *.
      intros.
      specialize H0 with (t':=t').
      apply H0.
      eassumption.
      econstructor.
      eassumption. }
    assert (not_none_none t2).
    {
      unfold not_none_none in *.
      intros.
      unfold not in *.
      intros.
      specialize H0 with (t':=t').
      apply H0.
      eassumption.
      apply abseq_subr.
      eassumption. }

    destruct s; destruct s; destruct s0;

      try (
      ff;
      try unfold mt_evc in *;
      repeat jkjke';
      ff;
      rewrite fold_recev in *;
      do_evsub_ih;
      
      ff;
      
      door; destruct_conjs;
        try eauto;
        try (right; repeat (eexists; eauto))
        ).

    unfold not_none_none in *.
    specialize H0 with (t':= (abseq (n,n0) (NONE, NONE) t1 t2)).
    assert (~
       term_sub (abseq (n, n0) (NONE, NONE) t1 t2)
       (abseq (n, n0) (NONE, NONE) t1 t2)).
    apply H0.
    unfold none_none_term.
    eauto.
    unfold not in H22.
    exfalso.
    apply H22.
    econstructor.



  - (* abpar case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.
    subst.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.
    
    clear_skipn_firstn.

    do_wfec_preserved.

    do_somerecons.

    assert (not_none_none t1).
    {
      unfold not_none_none in *.
      intros.
      unfold not in *.
      intros.
      specialize H0 with (t':=t').
      apply H0.
      eassumption.
      econstructor.
      eassumption. }
    assert (not_none_none t2).
    {
      unfold not_none_none in *.
      intros.
      unfold not in *.
      intros.
      specialize H0 with (t':=t').
      apply H0.
      eassumption.
      apply abpar_subr.
      eassumption. }

    destruct s; destruct s; destruct s0;

      try (
      ff;
      try unfold mt_evc in *;
      repeat jkjke';
      ff;
      rewrite fold_recev in *;
      do_evsub_ih;
      
      ff;
      
      door; destruct_conjs;
        try eauto;
        try (right; repeat (eexists; eauto))
        ).

    unfold not_none_none in *.
    specialize H0 with (t':= (abpar (n,n0) (NONE, NONE) t1 t2)).
    assert (~
       term_sub (abpar (n, n0) (NONE, NONE) t1 t2)
       (abpar (n, n0) (NONE, NONE) t1 t2)).
    apply H0.
    unfold none_none_term.
    eauto.
    unfold not in H22.
    exfalso.
    apply H22.
    econstructor.
Defined.

Ltac do_evaccum :=
  repeat 
    match goal with
    | [ H: well_formed_r ?t,
           H2: wf_ec ?ecc,
               H3: Some ?e = reconstruct_ev ?ecc,
                   H4: Some ?e' = reconstruct_ev ?ecc',
                       H5: EvSub ?e'' ?e,
                           H6: copland_compile ?t
                                               {| st_ev := ?ecc; st_trace := _; st_pl := _ |} =
                               (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |})

        |- _] =>
      
      assert_new_proof_by
        (EvSub e'' e' \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett))
        ltac: (eapply evAccum; [apply H | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
    end.         

Ltac do_evsub_ihhh' :=
  match goal with
  | [H: copland_compile ?t1
                        {| st_ev := ?ee; st_trace := _; st_pl := _ |} =
        (Some tt, {| st_ev := ?stev; st_trace := _; st_pl := _ |}),
        
       (* H2: copland_compile ?t2
                            {| st_ev := _(*?stev'*); st_trace := _; st_pl := _ |} =
            (Some tt, {| st_ev := _; st_trace := _; st_pl := _ |}), *)
            H3: Some _ = reconstruct_ev ?ee,
                H4: Some ?v' = reconstruct_ev ?stev,
                IH: forall _, _ -> _ ,(*context[forall _, well_formed_r ?t1 -> _], *)
       Hf: well_formed_r ?t1,
       Hwf: wf_ec ?ee,
       Hev: events ?t1 _ _ _
       

     |-  (exists e'' : EvidenceC, EvSub (uuc ?i ?args ?tpl ?tid ?n e'') _) \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) _ /\ EvSubT (uu ?i ?args ?tpl ?tid et') ett)
          (*context[EvSub _(*(uuc ?i ?args ?tpl ?tid ?n _)*) _ \/ _]*)
    ] => 

      

    assert_new_proof_by 
      (
        (exists e'' : EvidenceC, EvSub (uuc i args tpl tid n e'') v') \/
        (exists (ett : Evidence) (p'0 bs : nat) (et' : Evidence),
            EvSub (hhc p'0 bs ett) v' /\ EvSubT (uu i args tpl tid et') ett)
      )

      (*
          assert_new_proof_by
            (exists ee, EvSub (uuc i args tpl tid n ee) v \/
             (exists (ett : Evidence) (p'0 bs : nat) (et':Evidence),
                 EvSub (hhc p'0 bs ett) v /\ EvSubT (uu i args tpl tid et') ett)) 
       *)
      ltac: (eapply IH; [apply Hf | apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
      (*ltac:(ff; repeat jkjke'; eauto)*)
       
      
  end.

Lemma uu_preserved': forall t p et n p0 i args tpl tid
                       e tr e' tr' p' ecc ecc',

    well_formed_r t ->
    wf_ec ecc ->
    Some e = (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->
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
  -
    ff.
    invEvents.
    do_wf_pieces.

    eapply IHt; eauto.
    apply copland_compile_at; eauto.
  -
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)
     
      do_wfec_preserved.
      do_somerecons.

      repeat do_evsub_ihhh'.

      door.
      ++
        destruct_conjs.

        repeat jkjke'.
        repeat ff.

        do_evaccum.
        
        clear H12.
        door.
        +++
          left.
          eauto.
        +++
          destruct_conjs.
          ff.
          right.
          repeat (eexists; eauto).

      ++
        repeat jkjke'.
        repeat ff.
        
        do_evaccum.

        door.
        +++
          right.
          repeat (eexists; eauto).
        +++
          destruct_conjs.
          ff.
          right.
          repeat eexists.
          eauto.

          eapply evsubT_transitive.
          eapply hhSubT.
          eassumption.
          eassumption.
          
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      do_wfec_preserved.
      do_somerecons.

      repeat do_evsub_ihhh'.

      clear H14.
      door.
      ++
        eauto.
      ++
        destruct_conjs;
        right;
        repeat (eexists; eauto).


  - (* abseq case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
      try (rewrite fold_recev in * );
      try do_somerecons;
      do_evsub_ihhh';

      door; repeat jkjke'; ff;
        try eauto;
        try (destruct_conjs;
             right;
             repeat (eexists; eauto)).

  - (* abpar case *)
    do_wf_pieces.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents;

      do_wfec_split;
      do_wfec_preserved;
      do_wfec_firstn;
      do_wfec_skipn;
      clear_skipn_firstn;
      do_wfec_preserved;
      repeat do_pl_immut;
      do_somerecons;
      repeat jkjke'; ff;
      try (rewrite fold_recev in * );
      try do_somerecons;
      do_evsub_ihhh';

      door; repeat jkjke'; ff;
        try eauto;
        try (destruct_conjs;
             right;
             repeat (eexists; eauto)).
Defined.


Lemma uu_preserved: forall t1 t2 p et n p0 i args tpl tid
                      e tr st_ev st_trace p'
                      e' tr' p'' ecc,
    well_formed_r t1 ->
    well_formed_r t2 ->
    wf_ec e ->
    Some e' = (reconstruct_ev ecc) ->
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

  ff.
  do_wfec_preserved.
  do_somerecons.
  
  assert (
      (exists e'', EvSub (uuc i args tpl tid n e'') H9) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) H9 /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      4: { eassumption. }
      4: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
    }
    door;
      do_evaccum.
  +
    clear H16.
    door; eauto.

    right;
      (repeat eexists; eauto).
  +
    clear H20.
    door; ff.
    ++
    right;
      repeat (eexists; eauto).

    ++
      assert (EvSubT (uu i args tpl tid H17) H20).
      {
        eapply evsubT_transitive.
        apply hhSubT.
        eassumption.
        eassumption.
      }
      
      right; 
        repeat (eexists; eauto).
Defined.

Lemma appraisal_correct : forall t e' tr tr' p p' ecc ev ee,
    well_formed_r t ->
    wf_ec ee ->
    Some e' = (reconstruct_ev ecc) ->
    copland_compile t
                    {| st_ev := ee; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc;
                 st_trace := tr';
                 st_pl := p' |}) ->

    measEvent t p (get_et ee) ev ->
    appEvent_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    
    measEventFacts.
    evEventFacts.
    destruct ee.
    inv_events.
    ff.
    break_match; try solve_by_inversion.
    invc H1.
    
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
    
    do_wf_pieces.
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.

    measEventFacts.
    repeat do_pl_immut.
    subst.
    invc H6.
    inv_events.
    + (* t1 case *)

      edestruct uu_preserved.
      apply H4.
      apply H5.
      5: { eassumption. }
      4: { eassumption. }
      eassumption.
      jkjke'.
      eauto.

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
      destruct_conjs.
      eapply ahuc.
      eassumption.
      eapply hhc_app; eauto.
      
    + (* t2 case *)

      do_wfec_preserved.
      destruct ecc.
      destruct st_ev.
      
      eapply IHt2.
      eassumption.
      3: { eassumption. }
      eassumption.
      eassumption.
      econstructor.
      destruct ee.
      ff.
      assert (e2 = aeval t1 p e4).
      {
        rewrite <- eval_aeval.
        eapply cvm_refines_lts_evidence.
        eassumption.
        eassumption.
      }
      subst.
      eassumption.
      econstructor.
      
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
    
    repeat ff.

    measEventFacts.
    repeat do_pl_immut.
    subst.
    invc H2.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)

      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        destruct ee; ff.

        rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; ff.
          econstructor.
      }
      
      invc H8.
      +++
        econstructor.
        econstructor.
        
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.

    + (* t1 case *)


      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {      
        destruct ee; ff.

        rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; ff.
          econstructor.
      }

      invc H8.
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
    do_wf_pieces.
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    ff.

    measEventFacts.
    ff.
    do_pl_immut.
    do_pl_immut.
    subst.
    invc H2.

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)

      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e3))).
      {
        destruct ee; ff.

        rewrite fold_recev in *.
          
          eapply IHt1.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; ff.
          econstructor.
      }

      invc H8.
      +++
        econstructor.
        econstructor.   
        eassumption.
      +++
        eapply ahuc.
        eassumption.
        econstructor.
        eassumption.

    + (* t1 case *)

      assert (appEvent_EvidenceC (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {
        destruct ee; ff.

        rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; ff.
          econstructor.
      }

      invc H8.
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

Require Import Appraisal_AltImpls_Eq Impl_appraisal_alt.

Definition get_bits (e:EvC): list BS :=
  match e with
  | evc ls _ => ls
  end.
    

Lemma appraisal_correct_alt : forall t e' tr tr' p p' bits' et' ev ee,
    well_formed_r t ->
    wf_ec ee ->
    copland_compile t
                    {| st_ev := ee; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := (evc bits' et');
                 st_trace := tr';
                 st_pl := p' |}) ->

    measEvent t p (get_et ee) ev ->
    Some e' = Impl_appraisal_alt.build_app_comp_evC et' bits' ->
    appEvent_EvidenceC ev e'.
Proof.
  intros.
  ff.
  do_wfec_preserved.
  do_somerecons.
  erewrite appraisal_alt.
  eapply appraisal_correct.
  eassumption.
  3: { eassumption. }
  eassumption.
  2: { eassumption. }
  2: { eassumption. }
  3: { tauto. }
  eassumption.
  eassumption.
Defined.

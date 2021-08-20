Require Import Maps Event_system Term_system MonadVM ConcreteEvidence.
Require Import Impl_vm Helpers_VmSemantics VmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp.

Require Import StAM Appraisal_Defs Impl_appraisal (*MonadAM*).

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad. 

Require Import Lia Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

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
    none_none_term t'  -> 
    ~ (term_sub t' t).

Definition hash_sig_term (t:AnnoTerm): Prop :=
  exists r r1 r2 t1 t2,
  t = alseq r t1 t2 /\
  term_sub (aasp r1 SIG) t1 /\
  term_sub (aasp r2 HSH) t2.

Definition not_hash_sig_term (t:AnnoTerm) :=
  forall t',
    hash_sig_term t'  -> 
    ~ (term_sub t' t).

Definition hash_sig_ev (e:EvidenceC): Prop :=
  exists p p' bs et et',
    e = hhc p bs et /\ 
    EvSubT (gg p' et') et.

Definition not_hash_sig_ev (e:EvidenceC) :=
  forall e',
    hash_sig_ev e' ->
    ~ (EvSub e' e).

Definition gg_sub (e:EvidenceC) :=
  exists p bs e'' e', e' = ggc p bs e'' /\
                 EvSub e' e.

Definition hsh_subt (t:AnnoTerm) :=
  exists r, term_sub (aasp r HSH) t.

Definition not_hash_sig_term_ev (t:AnnoTerm) (e:EvidenceC): Prop :=
  not_hash_sig_term t /\
  not_hash_sig_ev e /\
  ~ ((gg_sub e) /\ (hsh_subt t)).

Lemma not_none_alseq_pieces: forall r t1 t2,
    not_none_none (alseq r t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply alseq_subr.
    eassumption.
Defined.

Lemma not_none_abseq_pieces: forall r s t1 t2,
    not_none_none (abseq r s t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply abseq_subr.
    eassumption.
Defined.

Lemma not_none_abpar_pieces: forall r s t1 t2,
    not_none_none (abpar r s t1 t2) ->
    not_none_none t1 /\ not_none_none t2.
Proof.
  unfold not_none_none in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply abpar_subr.
    eassumption.
Defined.

Lemma not_none_aatt_pieces: forall r q t1,
    not_none_none (aatt r q t1) ->
    not_none_none t1.
Proof.
  intros.
  unfold not_none_none in *.
  intros.
  unfold not. intros.
  specialize H with (t':=t').
  concludes.
  unfold not in *.
  apply H.
  econstructor.
  eassumption.
Defined.

Lemma not_hshsig_alseq_pieces: forall r t1 t2,
    not_hash_sig_term (alseq r t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  unfold not_hash_sig_term in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply alseq_subr.
    eassumption.
Defined.

Lemma not_hshsig_abseq_pieces: forall r s t1 t2,
    not_hash_sig_term (abseq r s t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  unfold not_hash_sig_term in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply abseq_subr.
    eassumption.
Defined.

Lemma not_hshsig_abpar_pieces: forall r s t1 t2,
    not_hash_sig_term (abpar r s t1 t2) ->
    not_hash_sig_term t1 /\ not_hash_sig_term t2.
Proof.
  unfold not_hash_sig_term in *.
  intros.
  split.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    econstructor.
    eassumption.
  -
    unfold not in *.
    intros.
    specialize H with (t':=t').
    apply H.
    eassumption.
    apply abpar_subr.
    eassumption.
Defined.

Lemma not_hshsig_aatt_pieces: forall r q t1,
    not_hash_sig_term (aatt r q t1) ->
    not_hash_sig_term t1.
Proof.
  intros.
  unfold not_hash_sig_term in *.
  intros.
  unfold not. intros.
  specialize H with (t':=t').
  concludes.
  unfold not in *.
  apply H.
  econstructor.
  eassumption.
Defined.


Ltac do_not_none_alseq_pieces :=
  match goal with
  | [H: not_none_none (alseq _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_alseq_pieces; apply H)
  end.

Ltac do_not_none_abseq_pieces :=
  match goal with
  | [H: not_none_none (abseq _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_abseq_pieces; apply H)
  end.

Ltac do_not_none_abpar_pieces :=
  match goal with
  | [H: not_none_none (abpar _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1 /\ not_none_none t2)
      ltac:(eapply not_none_abpar_pieces; apply H)
  end.

Ltac do_not_none_aatt_pieces :=
  match goal with
  | [H: not_none_none (aatt _ _ ?t1)

     |- _] =>
    
    assert_new_proof_by
      (not_none_none t1)
      ltac:(eapply not_none_aatt_pieces; apply H)
  end.

Ltac do_not_none :=
  try do_not_none_aatt_pieces;
  try do_not_none_alseq_pieces;
  try do_not_none_abseq_pieces;
  try do_not_none_abpar_pieces;
  destruct_conjs.


Ltac do_not_hshsig_alseq_pieces :=
  match goal with
  | [H: not_hash_sig_term (alseq _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_alseq_pieces; apply H)
  end.

Ltac do_not_hshsig_abseq_pieces :=
  match goal with
  | [H: not_hash_sig_term (abseq _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_abseq_pieces; apply H)
  end.

Ltac do_not_hshsig_abpar_pieces :=
  match goal with
  | [H: not_hash_sig_term (abpar _ _ ?t1 ?t2)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1 /\ not_hash_sig_term t2)
      ltac:(eapply not_hshsig_abpar_pieces; apply H)
  end.

Ltac do_not_hshsig_aatt_pieces :=
  match goal with
  | [H: not_hash_sig_term (aatt _ _ ?t1)

     |- _] =>
    
    assert_new_proof_by
      (not_hash_sig_term t1)
      ltac:(eapply not_hshsig_aatt_pieces; apply H)
  end.

Ltac do_not_hshsig :=
  try do_not_hshsig_aatt_pieces;
  try do_not_hshsig_alseq_pieces;
  try do_not_hshsig_abseq_pieces;
  try do_not_hshsig_abpar_pieces;
  destruct_conjs.

Lemma evsubt_preserved: forall t e e' et et' tr tr' p p' ett,
    copland_compile t {| st_ev := e et; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := evc e' et'; st_trace := tr'; st_pl := p' |}) ->
    EvSubT ett et ->
    EvSubT ett et'.
Proof.
Admitted.

Lemma ggsub: forall t ecc tr p e e0 tr' p' r,

    well_formed_r t ->
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := evc e e0; st_trace := tr'; st_pl := p' |}) ->

    term_sub (aasp r SIG) t ->
    exists pp et', EvSubT (gg pp et') e0.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; repeat ff.
  -
    eauto.
  -
    do_wf_pieces.
    invc H1.
    eapply IHt.
    eassumption.
    jkjke'.
    apply copland_compile_at.
    eassumption.
    eassumption.
  -
    do_wf_pieces.
    vmsts.
    destruct st_ev.
    
    
    invc H1.
    +
      assert (exists p et, EvSubT (gg p et) e2) by eauto.
      destruct_conjs.

      exists H1. exists H3.

      eapply evsubt_preserved; eauto.
    +
      eauto.
  -
    do_wf_pieces.
    vmsts.
    repeat ff.
    destruct st_ev.

    invc H1.
    +
      ff.

      assert (exists p et, EvSubT (gg p et) e2) by eauto.
      destruct_conjs.

      exists H1. exists H3.
      apply ssSublT.
      eassumption.
    +
      ff.

      assert (exists p et, EvSubT (gg p et) e4) by eauto.
      destruct_conjs.

      exists H1. exists H3.
      apply ssSubrT.
      eassumption.
  -
    do_wf_pieces.
    vmsts.
    repeat ff.
    destruct st_ev.

    invc H1.
    +
      ff.

      assert (exists p et, EvSubT (gg p et) e2) by eauto.
      destruct_conjs.

      exists H1. exists H3.
      apply ppSublT.
      eassumption.
    +
      ff.

      assert (exists p et, EvSubT (gg p et) e4) by eauto.
      destruct_conjs.

      exists H1. exists H3.
      apply ppSubrT.
      eassumption.
Defined.


Lemma evsub_transitive: forall e e' e'',
    EvSub e e' ->
    EvSub e' e'' ->
    EvSub e e''.
Proof.
Admitted.

(*
Lemma hshsig_ev_term: forall t p (e' :EvidenceC) tr tr' p' (ecc ecc':EvC),

    (*well_formed_r t -> 
    not_none_none t -> 
    wf_ec ecc -> 
    Some e =  (reconstruct_ev ecc) -> *)
    well_formed_r t ->
    hash_sig_term t ->
    Some e' = (reconstruct_ev ecc') ->
    (*EvSub e'' e -> *)
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    (exists e'', 
        hash_sig_ev e'' /\
        EvSub e'' e').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    repeat ff;
      try (
          invc H0;
          destruct_conjs;
          solve_by_inversion).
  -
    repeat ff.
    invc H0.
    destruct_conjs.
    solve_by_inversion.
  -
    do_wf_pieces.
    repeat ff.
    invc H0.
    destruct_conjs.
    invc H7.
    vmsts.
    ff.

    destruct st_ev.

    assert (exists pp et', EvSubT (gg pp et') e0).
    {
      eapply ggsub.
      apply H3.
      eassumption.
      eassumption.
    }

    destruct_conjs.

    destruct ecc'.

    assert (exists p et, EvSubT (hh p et) e2 /\
                    EvSubT (gg H7 H10) et).
    {
      admit.
    }
    destruct_conjs.

    unfold hash_sig_ev.

    assert (exists bs, EvSub (hhc H12 bs H13) e').
    admit.
    destruct_conjs.

    
    repeat eexists.
    eassumption.



    eapply evsub_transitive.
    eassumption.
    econstructor.

  -
    repeat ff.
    invc H0.
    repeat ff.
    destruct_conjs.
    solve_by_inversion.
  -
    repeat ff.
    invc H0.
    repeat ff.
    destruct_conjs.
    solve_by_inversion.
Admitted.
*)

    
(*
Lemma hshsig_ev_term: forall t p (e' :EvidenceC) tr tr' p' (ecc ecc':EvC),

    (*well_formed_r t -> 
    not_none_none t -> 
    wf_ec ecc -> 
    Some e =  (reconstruct_ev ecc) -> *)
    well_formed_r t ->
    hash_sig_term t ->
    Some e' = (reconstruct_ev ecc') ->
    (*EvSub e'' e -> *)
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    (exists e'', 
        hash_sig_ev e'' /\
        EvSub e'' e').
Proof.
 *)

Lemma not_ev: forall t e,
    not_hash_sig_term_ev t e ->
    not_hash_sig_ev e.
Proof.
  intros.
  cbv in H.
  destruct_conjs.
  cbv.
  destruct_conjs.
  intros.
  destruct_conjs.
  subst.
  eapply H0.
  repeat eexists.
  eassumption.
  eassumption.
Defined.

Lemma hshsig_ev_term_contra: forall t p (e e' :EvidenceC) tr tr' p' (ecc ecc':EvC),

    (*well_formed_r t -> 
    not_none_none t -> 
    wf_ec ecc -> 
     *)

    well_formed_r t ->

    (*not_hash_sig_term t ->
    not_hash_sig_ev e ->
     *)
    not_hash_sig_term_ev t e ->
    
    Some e =  (reconstruct_ev ecc) ->
    Some e' = (reconstruct_ev ecc') ->

    (*EvSub e'' e -> *)
    copland_compile t {| st_ev := ecc; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    not_hash_sig_ev e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros; repeat ff.
  -
    jkjke'.
    ff.
    unfold not_hash_sig_term_ev in *.
    destruct_conjs.
    eassumption.
  -
    unfold cons_uu in *.
    ff.
    ff.
    assert (not_hash_sig_ev e2).
    {
      eapply not_ev; eauto.
    }

    Lemma not_hshsig_uuc: forall e' n l n1 n2 x,
      not_hash_sig_ev e' ->
      not_hash_sig_ev (uuc n l n1 n2 x e').
    Proof.
    Admitted.

    eapply not_hshsig_uuc; eauto.
  -
    repeat ff.
    assert (not_hash_sig_ev e).
    {
      eapply not_ev; eauto.
    }
    rewrite fold_recev in *.
    assert ((evc (get_bits ecc) (get_et ecc)) = ecc).
    {
      destruct ecc.
      ff.
    }
    rewrite H3 in *; clear H3.
    jkjke'.
    ff.

    Lemma not_hshsig_ggc: forall e' n bs,
      not_hash_sig_ev e' ->
      not_hash_sig_ev (ggc n bs e').
    Proof.
    Admitted.

    eapply not_hshsig_ggc; eauto.
  -
    assert (not_hash_sig_ev e).
    {
      eapply not_ev; eauto.
    }

    assert (~ (gg_sub e)).
    {
      cbv in H0.
      destruct_conjs.
      unfold not; intros.
      eapply H4.
      split.
      2: {
        repeat eexists.
        econstructor.
      }
      cbv in H5.
      eauto.
    }
    unfold not in *.
    
    
        
      

    destruct ecc.
    ff.

    cbv; intros.
    destruct_conjs.
    subst.
    invc H5.

    invc H11.
    +
    repeat ff.
    eapply H3. cbv.
    repeat eexists. econstructor.
    +
    repeat ff.
    eapply H3. cbv.
    repeat eexists.
    econstructor.
    admit.
    +
      assert (exists p bs et', e = ggc p bs et').
      {
        admit.
      }
      destruct_conjs.
      subst.
      eapply H3.
      econstructor.
      eauto.
    +
      assert (exists bs, e = hhc p0 bs e').
      {
        admit.
      }
      destruct_conjs.
      subst.
      cbv in H2.
      eapply H2.
      repeat eexists.
      eassumption.
      econstructor.
    +
      assert (exists e1 e2, e = ssc e1 e2).
      {
        admit.
      }
      destruct_conjs.
      subst.
      assert (not_hash_sig_ev (ssc H5 H7)).
      {
        eapply not_ev; eauto.
      }

      (*
      assert (not_hash_sig_ev H5).
      admit.

      assert (not_hash_sig_ev H7).
      admit.
       *)
      

      repeat ff.
      eapply H3.
      econstructor.
      repeat eexists.
      apply ssSubl.
      admit.
    +
      assert (exists e1 e2, e = ssc e1 e2).
      {
        admit.
      }
      destruct_conjs.
      subst.
      assert (not_hash_sig_ev (ssc H5 H7)).
      {
        eapply not_ev; eauto.
      }

      (*
      assert (not_hash_sig_ev H5).
      admit.

      assert (not_hash_sig_ev H7).
      admit.
       *)
      

      repeat ff.
      eapply H3.
      econstructor.
      repeat eexists.
      apply ssSubr.
      admit.
    +
      assert (exists e1 e2, e = ppc e1 e2).
      {
        admit.
      }
      destruct_conjs.
      subst.
      assert (not_hash_sig_ev (ppc H5 H7)).
      {
        eapply not_ev; eauto.
      }

      (*
      assert (not_hash_sig_ev H5).
      admit.

      assert (not_hash_sig_ev H7).
      admit.
       *)
      

      repeat ff.
      eapply H3.
      econstructor.
      repeat eexists.
      apply ppSubl.
      admit.
    +
      assert (exists e1 e2, e = ppc e1 e2).
      {
        admit.
      }
      destruct_conjs.
      subst.
      assert (not_hash_sig_ev (ppc H5 H7)).
      {
        eapply not_ev; eauto.
      }

      (*
      assert (not_hash_sig_ev H5).
      admit.

      assert (not_hash_sig_ev H7).
      admit.
       *)
      

      repeat ff.
      eapply H3.
      econstructor.
      repeat eexists.
      apply ppSubr.
      admit.

  - (* aatt case *)
    do_wf_pieces.
    assert (not_hash_sig_term_ev t e).
    {
      admit.
    }
    
    eapply IHt.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    apply copland_compile_at.
    eassumption.
  -
    do_wf_pieces.
    ff.
    vmsts.
    ff.
    destruct ecc; destruct st_ev.

    
    assert (exists e, Some e = reconstruct_ev (evc e2 e3)).
    {
      admit.
    }
    destruct_conjs.

    Lemma sig_term_ev_lseq: forall r t1 t2 e e0 e1 e2 e3 tr tr' p p' H5,
      not_hash_sig_term_ev (alseq r t1 t2) e ->
      copland_compile t1 {| st_ev := evc e0 e1; st_trace := tr; st_pl := p |} =
      (Some tt, {| st_ev := evc e2 e3; st_trace := tr'; st_pl := p' |}) ->
      Some e  = reconstruct_ev (evc e0 e1) ->
      Some H5 = reconstruct_ev (evc e2 e3) ->
      not_hash_sig_term_ev t1 e /\
      not_hash_sig_term_ev t2 H5.
    Proof.
      intros.
      unfold not_hash_sig_term_ev in H.
      destruct_conjs.
      unfold not_hash_sig_term in H.

      Lemma termsub_transitive: forall t t' t'',
              term_sub t t' ->
              term_sub t' t'' ->
              term_sub t t''.
            Admitted.
      
      split.
      -
        cbv.
        split.
        +
          intros.
          destruct_conjs.
          subst.
          unfold not in *.
          eapply H4.
          split.
          2: {
            econstructor.
            eapply termsub_transitive with (t':=t1).
            eapply termsub_transitive with (t':=(alseq (n, n0) H8 H6)).
            apply alseq_subr.
            eassumption.
            eassumption.
            econstructor.
            econstructor.
          }

          admit.
        +
          split.
          ++
            
          
        
          
            eapply termsub_transitive.
            eassumption.
            eapply termsub_transitive with (t' := t1).
            eapply termsub_transitive.
            eassumption.
            apply alseq_subl.
            

            eapply termsub_transitive.
            eassumption.
            
            
          
          eapply H.
          destruct_conjs.
        
    Admitted.

    edestruct sig_term_ev_lseq.
    eassumption.
    eassumption.
    eassumption.
    eassumption.

    
    

    assert (not_hash_sig_ev H5).
    {
      eapply IHt1; eauto.
    }

    eapply IHt2.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
  -
    
    













      (*
  -
    
    destruct ecc; ff.
    jkjke'.
    ff.
    cbv.
    intros.
    destruct_conjs.
    ff.
    cbv in H1.
    eapply H1.
    repeat eexists.
    eassumption.
    invc H4.
    +
      ff.
    +
      ff.
  -
    destruct ecc.
    ff.

    Lemma mid_ecc: forall e e0 e1 p bs,
      Some e = reconstruct_ev' e0 e1 ->
      not_hash_sig_ev e ->
      not_hash_sig_ev (hhc p bs e1).
    Proof.
      intros.
      generalizeEverythingElse e.
      induction e; intros; ff.
      -
        assert (e1 = mt).
        { admit. }
        subst.
        cbv.
        intros.
        destruct_conjs.
        subst.
        invc H2.
        invc H8.
      -
        assert (e1 = nn n).
        {
          admit.
        }
        subst.
        cbv.
        intros.
        destruct_conjs.
        invc H2.
        invc H10.
        invc H8.
      -
        assert (exists et', e1 = uu n l n0 n1 et').
        {
          admit.
        }
        destruct_conjs.
        subst.
        cbv.
        intros.
        destruct_conjs.
        invc H3.
        invc H11.
        invc H9.
        ff.
        ff.

        assert (not_hash_sig_ev (hhc 1 2 H1)).
        {
          eapply IHe.
          jkjke'.
          unfold not_hash_sig_ev in *.
          intros.
          unfold not in *; intros.
          eapply H0.
          eassumption.
          apply uuSub.
          eassumption.
        }

        unfold not_hash_sig_ev in H.
        unfold not in *.
        eapply H with (e' := hhc 1 2 H1).
        cbv.
        repeat eexists.
        eassumption.
        econstructor.
      -

        assert (not_hash_sig_ev e).
        {
          admit.
        }

        assert (exists et', e1 = gg n et').
        {
          admit.
        }
        destruct_conjs.
        subst.

        assert (exists bits,
                   Some e = reconstruct_ev' bits H2).
        {
          repeat ff.
          repeat eexists.
          jkjke'.
        }
        destruct_conjs.

        edestruct IHe with (e1:= H2) (e':= hhc 1 2 H2).
        eassumption.
        eassumption.
        econstructor.
        repeat eexists.
        
        
        assert (exists et', not_hash_sig_ev (hhc 1 2 (gg n et'))).
        {
          
          repeat ff.

          assert (not_hash_sig_ev (hhc 3 4 H2)).
          {
            eapply IHe.
            jkjke'.
            eassumption.
          }

          unfold not_hash_sig_ev in H0.
          unfold not in H0.
          exfalso.
          eapply H0.


          
          unfold not in *.
          exfalso.
          


          (*


          
          exists H1.
          subst.
          repeat ff.
          eapply IHe.
          repeat ff.
          eapply IHe.
          
          
          admit.
        }
        destruct_conjs.
        unfold not_hash_sig_ev in H2.
        unfold not in *.
        exfalso.
        eapply H2 with (e':=(hhc 1 2 (gg n H1))).
        econstructor.
        repeat eexists. econstructor.
        econstructor.
        

        assert (exists et', e1 = gg n et').
        {
          admit.
        }
        destruct_conjs.
        subst.
        repeat ff.

        assert (not_hash_sig_ev e2).
          {
            admit.
          }


          

          eapply IHe.

        assert (not_hash_sig_ev (hhc 1 2 H1)).
        {
          
          
          eapply IHe.
          jkjke'.
          eassumption.
        }

        unfold not_hash_sig_ev in H2.
        unfold not in H2.
        unfold not_hash_sig_ev in H.
        unfold not in *.
        unfold not_hash_sig_ev.
        unfold not.
        intros.
        invc H4.
        eapply H2.
        eassumption.
        invc H4.
        eassumption.
        exfalso.
        eapply H2 with (e':= hhc 1 2 H1).
        cbv.
        repeat eexists.
        
        


        
        eapply IHe.
        jkjke'.
        subst.
        repeat ff.
        assert (not_hash_sig_ev e2).
        {
          admit.
        }
        eapply IHe.
        

        cbv.
        intros.
        destruct_conjs.
        subst.
        
        cbv.
        intros.
        destruct_conjs.
        invc H3.
        invc H11.
        invc H9.
        ff.
        ff.

        assert (not_hash_sig_ev (hhc 1 2 H1)).
        {
          eapply IHe.
          jkjke'.
          unfold not_hash_sig_ev in *.
          intros.
          unfold not in *; intros.
          eapply H0.
          eassumption.
          apply ggSub.
          eassumption.
        }

        unfold not_hash_sig_ev in H.
        unfold not in *.
        eapply H with (e' := hhc 1 2 H1).
        cbv.
        repeat eexists.
        eassumption.
        econstructor.

*)
          
          
        
        
        
        
        
    Admitted.

    eapply mid_ecc; eauto.
*)

Admitted.

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
      destruct ecc.
      ff.
      assert (e2 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.
      jkjke'.
      ff.
    +
      destruct ecc.
      ff.
      assert (e1 = et_fun e).
      {
        eapply etfun_reconstruct; eauto.
      }
      subst.
      right.
      repeat eexists.
      econstructor.
      apply evsub_etfun; eauto.
      
  - (* aatt case *)
    do_wf_pieces.
    do_not_none.
    ff.
    
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
    eassumption.

  - (* alseq case *)
    ff.
    dosome.
    vmsts.

    do_wf_pieces.

    do_wfec_preserved.

    do_somerecons.

    do_not_none.

    do_evsub_ih.
    
    door.
    +
      eapply IHt2 with (ecc:=st_ev); eauto.
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

    do_not_none.
    
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
    {
    apply H0.
    unfold none_none_term.
    left.
    eauto.
    }
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

    do_not_none.
    
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
    (*
    left.
    eauto. *)
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
                               (Some tt, {| st_ev := ?ecc'; st_trace := _; st_pl := _ |}),
                               H7: not_none_none ?t

        |- _] =>
      
      assert_new_proof_by
        (EvSub e'' e' \/
         (exists (ett : Evidence) (p'0 bs : nat),
             EvSub (hhc p'0 bs ett) e' /\ EvSubT (et_fun e'') ett))
        ltac: (eapply evAccum; [apply H | apply H7 | apply H2 | apply H3 | apply H4 | apply H5 | apply H6])
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
       Hnn: not_none_none ?t1,
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
      ltac: (eapply IH; [apply Hf | apply Hnn| apply Hwf | apply H3 | apply H4 | apply Hev | apply H])
      (*ltac:(ff; repeat jkjke'; eauto)*)
       
      
  end.

Lemma uu_preserved': forall t p et n p0 i args tpl tid
                       e tr e' tr' p' ecc ecc',

    well_formed_r t ->
    not_none_none t ->
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
    do_not_none.

    eapply IHt; eauto.
    apply copland_compile_at; eauto.
  -
    do_wf_pieces.
    do_not_none.
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

        (*
        clear H12. *)
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

      clear H17.
      door.
      ++
        eauto.
      ++
        destruct_conjs;
        right;
        repeat (eexists; eauto).


  - (* abseq case *)
    do_wf_pieces.
    do_not_none.
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
    do_not_none.
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
    not_none_none t1 ->
    not_none_none t2 ->
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
      (exists e'', EvSub (uuc i args tpl tid n e'') H11) \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) H11 /\
          EvSubT (uu i args tpl tid et') ett)
      ).
    {
      eapply uu_preserved'.
      apply H.
      eassumption.
      4: { eassumption. }
      4: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
    }
    door;
      do_evaccum.
  +
    
    clear H18.
    door; eauto.

    right;
      (repeat eexists; eauto).
  +
    clear H22.
    door; ff.
    ++
    right;
      repeat (eexists; eauto).

    ++
      assert (EvSubT (uu i args tpl tid H19) H22).
      {
        eapply evsubT_transitive.
        apply hhSubT.
        eassumption.
        eassumption.
      }
      
      right; 
        repeat (eexists; eauto).
Defined.

Ltac sigEventFacts :=
  match goal with
  | [H: sigEvent _ _ _ _ |- _] => invc H
  end.

Ltac sigEventPFacts :=
  match goal with
  | [H: sigEventP _ |- _] => invc H
  end.



(*
Lemma sig_hsh_contra': forall t1 t2 r e tr p st_ev st_trace st_pl
                         ecc' tr' p' H9 a b c p0 H2 (*n H19*) ,
    (*not_hsh_sig (alseq r t1 t2) -> *)

    (*
    events t1 p et (sign n p0 (et_fun H19)) -> *)
    
    copland_compile t1 {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl |}) ->
    
    copland_compile t2 {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    Some H9 = reconstruct_ev ecc' ->

    EvSub (hhc a b H2) H9 ->
    EvSubT (gg p0 c) H2 ->

    (
      (exists t1', hash_sig_term t1' /\ term_sub t1' t1) \/
      (exists t2', hash_sig_term t2' /\ term_sub t2' t2) \/
      hash_sig_term (alseq r t1 t2)).
Proof.
  intros.


  
  generalizeEverythingElse H9.
  induction H9; intros.
  -
    repeat ff.
  -
    repeat ff.
  -
    (*
    invc H3.
    Locate reconstruct_ev. *)
    assert (exists et' bits, ecc' = (evc bits (uu n l n0 n1 et'))).
    {
      admit.
    }
    destruct_conjs.
    subst.
    repeat ff.
    rewrite fold_recev in *.
    invc H3.

    edestruct IHEvidenceC.
    3: {
      symmetry.
      eassumption.
    }
    3: { eassumption. }
    3: { eassumption. }
    apply H.

    admit.
    destruct_conjs.
    eauto.
    door.
    eauto.
    eauto.
  -
    assert (exists et' bits, ecc' = (evc bits (gg n et'))).
    {
      admit.
    }
    destruct_conjs.
    subst.
    repeat ff.
    rewrite fold_recev in *.
    invc H3.

    edestruct IHEvidenceC.
    3: {
      symmetry.
      eassumption.
    }
    3: { eassumption. }
    3: { eassumption. }
    apply H.

    admit.
    destruct_conjs.
    eauto.
    door.
    eauto.
    eauto.
  -
    assert (exists bits et', ecc' = (evc bits (hh n et'))).
    {
      admit.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H3.

    destruct e0. destruct st_ev.

    assert (EvSubT (gg p0 c) e2).
    {

      HERE


   


    
    admit.
  -
    assert (exists bits et1 et2 , ecc' = (evc bits (ss et1 et2))).
    {
      admit.
    }
    destruct_conjs.
    subst.
    repeat ff.
    rewrite fold_recev in *.
    invc H3.
    Check wfec_firstn.
    ++

      edestruct IHEvidenceC1 with (r:=r).
      3: { symmetry. eassumption. }
      3: { eassumption. }
      3: { eassumption. }
      
      apply H.
      admit.
      eauto.
      door; eauto.
    ++
      edestruct IHEvidenceC2 with (r:=r).
      3: { symmetry. eassumption. }
      3: { eassumption. }
      3: { eassumption. }
      
      apply H.
      admit.
      eauto.
      door; eauto.

  -
    assert (exists bits et1 et2 , ecc' = (evc bits (pp et1 et2))).
    {
      admit.
    }
    destruct_conjs.
    subst.
    repeat ff.
    rewrite fold_recev in *.
    invc H3.
    Check wfec_firstn.
    ++

      edestruct IHEvidenceC1 with (r:=r).
      3: { symmetry. eassumption. }
      3: { eassumption. }
      3: { eassumption. }
      
      apply H.
      admit.
      eauto.
      door; eauto.
    ++
      edestruct IHEvidenceC2 with (r:=r).
      3: { symmetry. eassumption. }
      3: { eassumption. }
      3: { eassumption. }
      
      apply H.
      admit.
      eauto.
      door; eauto.
      Unshelve.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
    
Admitted.

Lemma sig_hsh_contra: forall t1 t2 r e tr p st_ev st_trace st_pl
                        ecc' tr' p' H9 a b c p0 H2,
    not_hsh_sig (alseq r t1 t2) ->
    
    copland_compile t1 {| st_ev := e; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl |}) ->
    
    copland_compile t2 {| st_ev := st_ev; st_trace := st_trace; st_pl := st_pl |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    Some H9 = reconstruct_ev ecc' ->

    EvSub (hhc a b H2) H9 ->
    EvSubT (gg p0 c) H2 ->
    False.
Proof.
  intros.
  unfold not_hsh_sig in *.
  unfold not in *.

  assert (
      (exists t1', hash_sig_term t1' /\ term_sub t1' t1) \/
      (exists t2', hash_sig_term t2' /\ term_sub t2' t2) \/
      hash_sig_term (alseq r t1 t2)).
  {
    eapply sig_hsh_contra'; eauto.
  }

  door.
  eapply H.
  apply H7.
  econstructor.
  eassumption.

  door.
  eapply H.
  apply H7.
  Locate term_sub.
  apply alseq_subr.
  eassumption.

  eapply H.
  eassumption.
  econstructor.
Defined.
*)

Lemma gg_preserved': forall t p et n p0 et'
                       tr e e' tr' p' bits ecc',

    well_formed_r t ->
    not_none_none t ->
    not_hash_sig_term t ->
    (*not_hash_sig_ev e' -> *)
    wf_ec (evc bits et) ->
    not_hash_sig_ev e ->
    Some e = (reconstruct_ev (evc bits et)) ->
    Some e' = (reconstruct_ev ecc') ->
    (*events t p et (umeas n p0 i args tpl tid) -> *)
    events t p et (sign n p0 et') ->
    copland_compile t {| st_ev := (evc bits et); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc'; st_trace := tr'; st_pl := p' |}) ->

    (
      (exists bits e'', EvSub (ggc p0 (do_sig (MonadVM.encodeEv (evc bits et')) p0) e'') e' /\
                   et_fun e'' = et'
      )

      (* \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (gg p0 et') ett) *)
    ).

    (*

    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid et') ett) 
    ). *)
Proof.

  
  intros.

  (*
  destruct ecc'.
  assert (e2 = Term_Defs.eval (unanno t) p e0).
  { eapply cvm_refines_lts_evidence.
    eassumption.
    eassumption.
  } *)
  
  generalizeEverythingElse t.
  
  induction t; intros.
  -
    subst.
    destruct a; try (ff; tauto).
    +
      (*
    destruct ecc.
    unfold get_bits in *.
    unfold get_et in *. *)
    ff.
    invEvents.
    ff.

    repeat eexists.
    econstructor.
    rewrite fold_recev in *.
    Check etfun_reconstruct.
    symmetry.
    
    eapply etfun_reconstruct; eauto.

  -
    ff.
    invEvents.
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.

    eapply IHt; eauto.
    apply copland_compile_at; eauto.
  -
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.
    ff.
    dosome.
    ff.
    vmsts.
    ff.

    invEvents.
    + (* t1 case *)
     
      do_wfec_preserved.
      do_somerecons.

      assert (not_hash_sig_ev H15).
      {
        eapply hshsig_ev_term_contra.
        apply H8.
        eauto.
        apply H3.
        2: { eassumption. }
        2: { eassumption. }
        eassumption.
        
      }
      
      (*
      Check evAccum.

      edestruct evAccum.
      7: { apply Heqp1. }
      eassumption.
      eassumption.
      eassumption.
      eassumption.
      eassumption.
       *)
      

      edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      5: { eassumption. }
      3: { eassumption. }
      eassumption.
      repeat jkjke'.
      repeat ff.
      repeat jkjke'.
      repeat ff.
      2: { eassumption. }
      eassumption.

      (*

      

      assert (exists bs e'',
                 EvSub (ggc p0 

      eapply IHt1.
      eassumption.
      eassumption.
      2: {
        eassumption. }
      2: { eassumption. }
      2: { eassumption.

      repeat do_evsub_ihhh'. *)
      destruct_conjs.

      (*
      door.
      ++

      
        destruct_conjs. *)

        repeat jkjke'.
        repeat ff.

        do_evaccum.

        (*
        clear H12. *)
        door.
      +++
        eauto.
        (*
          left.
          eauto. *)
      +++
        ff.
        assert (not_hash_sig_ev H14).
        {
          eapply hshsig_ev_term_contra; eauto.
        }

        unfold not_hash_sig_ev in H28.
        specialize H28 with (e':=(hhc H24 H25 H5)).
        unfold not in *.
        exfalso.
        apply H28.
        econstructor.
        repeat eexists.
        eassumption.
        eassumption.
        

          

          
        (*
        admit.  (* TODO: eliminate this case with well_formedness conditions on t1/t2 *)
         *)
        

        (*
          destruct_conjs.
          ff.
          repeat (eexists; eauto).
          e
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
         *)
        
          
    + (* t2 case *)

      do_pl_immut.
      do_pl_immut.
      subst.

      do_wfec_preserved.
      do_somerecons.
      destruct st_ev.
      destruct ecc'.

      assert (e1 = (aeval t1 p et)).
        {
          rewrite <- eval_aeval.
          eapply cvm_refines_lts_evidence.
          eassumption.
          eassumption.
        }
        subst.

      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      5: { eassumption. }
      3: { eassumption. }
      4: { 
        
        
        

        eassumption.
      }
      eassumption.
      2: { eassumption. }

      eapply hshsig_ev_term_contra.
      apply H8.
      eauto.
      3: { eassumption. }
      3: { eassumption. }
      2: { eassumption. }
      repeat jkjke'; repeat ff.
      repeat jkjke'; repeat ff.
      
      
        


      (*

      repeat do_evsub_ihhh'. *)

      (*
      clear H17.
      door.
      ++ *)
      repeat jkjke'; repeat ff.
      eauto.

      (*
      ++
        destruct_conjs;
        right;
        repeat (eexists; eauto). *)


  - (* abseq case *)
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.
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
      try do_evsub_ihhh'.

    +
      

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.

      assert (not_hash_sig_ev e4).
      {
        
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H8.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        2: { eassumption. }
        destruct s.
        destruct s; destruct s0; ff.
        repeat jkjke'; repeat ff.
        repeat jkjke'; repeat ff.
        repeat jkjke'; repeat ff.
        cbv.
        intros.
        invc H15.
        destruct_conjs.
        solve_by_inversion.

        cbv.
        intros.
        invc H15.
        destruct_conjs.
        solve_by_inversion.
      }

      assert (not_hash_sig_ev e5).
      {
                repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H9.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        2: { eassumption. }
        destruct s.
        destruct s; destruct s0; ff.
        repeat jkjke'; repeat ff.

        cbv.
        intros.
        invc H16.
        destruct_conjs.
        solve_by_inversion.


        
        repeat jkjke'; repeat ff.
        
        cbv.
        intros.
        invc H16.
        destruct_conjs.
        solve_by_inversion.
      }
      

      destruct s; destruct s; destruct s0; ff.
      ++
        

      edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      apply H5.
      2: { eassumption. }
      eassumption.
      2: {
        eassumption.
      }
      2: {
      eassumption. }
      eassumption.

      destruct_conjs.
      eauto.
      ++
        edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      apply H5.
      2: { eassumption. }
      eassumption.
      2: {
        eassumption.
      }
      2: {
      eassumption. }
      eassumption.

      destruct_conjs.
      eauto.

      ++
        edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      apply H5.
      4: { eassumption. }
      4: {
        eassumption.
      }
      2: {
        ff. tauto.
      }

      cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
      eassumption.

      destruct_conjs.
      eauto.

      ++
                edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      apply H5.
      4: { eassumption. }
      4: {
        eassumption.
      }
      2: {
        ff. tauto.
      }

      cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
      eassumption.

      destruct_conjs.
      eauto.



    +
            repeat jkjke'; ff.
      repeat jkjke'; repeat ff.

      assert (not_hash_sig_ev e4).
      {
        
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H8.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        2: { eassumption. }
        destruct s.
        destruct s; destruct s0; ff.
        repeat jkjke'; repeat ff.
        repeat jkjke'; repeat ff.
        repeat jkjke'; repeat ff.
        cbv.
        intros.
        invc H15.
        destruct_conjs.
        solve_by_inversion.

        cbv.
        intros.
        invc H15.
        destruct_conjs.
        solve_by_inversion.
      }

      assert (not_hash_sig_ev e5).
      {
                repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H9.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        2: { eassumption. }
        destruct s.
        destruct s; destruct s0; ff.
        repeat jkjke'; repeat ff.

        cbv.
        intros.
        invc H16.
        destruct_conjs.
        solve_by_inversion.


        
        repeat jkjke'; repeat ff.
        
        cbv.
        intros.
        invc H16.
        destruct_conjs.
        solve_by_inversion.
      }
      

      destruct s; destruct s; destruct s0; ff.
      ++
        

      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      apply H6.
      2: { eassumption. }
      eassumption.
      2: {
        eassumption.
      }
      2: {
      eassumption. }
      eassumption.

      destruct_conjs.
      eauto.
      ++
                edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      apply H6.
      4: { eassumption. }
      4: {
        eassumption.
      }
      2: {
        ff. tauto.
      }

      cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
      eassumption.

      destruct_conjs.
      eauto.
        



      ++
                

      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      apply H6.
      2: { eassumption. }
      eassumption.
      2: {
        eassumption.
      }
      2: {
      eassumption. }
      eassumption.

      destruct_conjs.
      eauto.
      ++


        
        edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      apply H6.
      4: { eassumption. }
      4: {
        eassumption.
      }
      2: {
        ff. tauto.
      }

      cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
      eassumption.

      destruct_conjs.
      eauto.



  - (* abseq case *)
    do_wf_pieces.
    do_not_none.
    
    do_not_hshsig.
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
      try do_evsub_ihhh'.

    +
      

      repeat jkjke'; ff.
      repeat jkjke'; repeat ff.

      assert (not_hash_sig_ev e4).
      {
        
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H8.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        2: { eassumption. }
        destruct s.
        destruct s; destruct s0; ff.
        repeat jkjke'; repeat ff.
        repeat jkjke'; repeat ff.
        repeat jkjke'; repeat ff.
        cbv.
        intros.
        invc H15.
        destruct_conjs.
        solve_by_inversion.

        cbv.
        intros.
        invc H15.
        destruct_conjs.
        solve_by_inversion.
      }

      assert (not_hash_sig_ev e5).
      {
                repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H9.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        2: { eassumption. }
        destruct s.
        destruct s; destruct s0; ff.
        repeat jkjke'; repeat ff.

        cbv.
        intros.
        invc H16.
        destruct_conjs.
        solve_by_inversion.


        
        repeat jkjke'; repeat ff.
        
        cbv.
        intros.
        invc H16.
        destruct_conjs.
        solve_by_inversion.
      }
      

      destruct s; destruct s; destruct s0; ff.
      ++
        

      edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      apply H5.
      2: { eassumption. }
      eassumption.
      2: {
        eassumption.
      }
      2: {
      eassumption. }
      eassumption.

      destruct_conjs.
      eauto.
      ++
        edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      apply H5.
      2: { eassumption. }
      eassumption.
      2: {
        eassumption.
      }
      2: {
      eassumption. }
      eassumption.

      destruct_conjs.
      eauto.

      ++
        edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      apply H5.
      4: { eassumption. }
      4: {
        eassumption.
      }
      2: {
        ff. tauto.
      }

      cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
      eassumption.

      destruct_conjs.
      eauto.

      ++
                edestruct IHt1.
      eassumption.
      eassumption.
      eassumption.
      apply H5.
      4: { eassumption. }
      4: {
        eassumption.
      }
      2: {
        ff. tauto.
      }

      cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
      eassumption.

      destruct_conjs.
      eauto.



    +
            repeat jkjke'; ff.
      repeat jkjke'; repeat ff.

      assert (not_hash_sig_ev e4).
      {
        
        repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H8.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        2: { eassumption. }
        destruct s.
        destruct s; destruct s0; ff.
        repeat jkjke'; repeat ff.
        repeat jkjke'; repeat ff.
        repeat jkjke'; repeat ff.
        cbv.
        intros.
        invc H15.
        destruct_conjs.
        solve_by_inversion.

        cbv.
        intros.
        invc H15.
        destruct_conjs.
        solve_by_inversion.
      }

      assert (not_hash_sig_ev e5).
      {
                repeat jkjke'; repeat ff.
        repeat rewrite fold_recev in *.
        eapply hshsig_ev_term_contra.
        apply H9.
        eassumption.
        3: { eassumption. }
        3: { eassumption. }
        2: { eassumption. }
        destruct s.
        destruct s; destruct s0; ff.
        repeat jkjke'; repeat ff.

        cbv.
        intros.
        invc H16.
        destruct_conjs.
        solve_by_inversion.


        
        repeat jkjke'; repeat ff.
        
        cbv.
        intros.
        invc H16.
        destruct_conjs.
        solve_by_inversion.
      }
      

      destruct s; destruct s; destruct s0; ff.
      ++
        

      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      apply H6.
      2: { eassumption. }
      eassumption.
      2: {
        eassumption.
      }
      2: {
      eassumption. }
      eassumption.

      destruct_conjs.
      eauto.
      ++
                edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      apply H6.
      4: { eassumption. }
      4: {
        eassumption.
      }
      2: {
        ff. tauto.
      }

      cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
      eassumption.

      destruct_conjs.
      eauto.
        



      ++
                

      edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      apply H6.
      2: { eassumption. }
      eassumption.
      2: {
        eassumption.
      }
      2: {
      eassumption. }
      eassumption.

      destruct_conjs.
      eauto.
      ++


        
        edestruct IHt2.
      eassumption.
      eassumption.
      eassumption.
      apply H6.
      4: { eassumption. }
      4: {
        eassumption.
      }
      2: {
        ff. tauto.
      }

      cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
      eassumption.

      destruct_conjs.
      eauto.
Defined.






      
        
        
      (*
        unfold splitEv_l in Heqp0.
        destruct s; destruct s0; ff.
        +
          eassumption.
        +
          eassumption.
          
          
          
          

        
      3: { eassumption.

      door; repeat jkjke'; ff;
        try eauto;
        try (destruct_conjs;
             right;
             repeat (eexists; eauto)).

  - (* abpar case *)
    do_wf_pieces.
    do_not_none.
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
Admitted.
*)

(*
Lemma gg_preserved: forall t1 t2 p et n p0  et'
                      bits tr st_ev st_trace p'
                      e' tr' p'' ecc,
    well_formed_r t1 ->
    well_formed_r t2 ->
    not_none_none t1 ->
    not_none_none t2 ->
    not_hsh_sig t1 ->
    not_hsh_sig t2 ->
    wf_ec (evc bits et) ->
    Some e' = (reconstruct_ev ecc) ->
    (*events t1 p et (umeas n p0 i args tpl tid) -> *)
    events t1 p et (sign n p0 et') ->
    copland_compile t1 {| st_ev := (evc bits et); st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |}) ->
    
    copland_compile t2
                    {| st_ev := st_ev; st_trace := st_trace; st_pl := p' |} =
    (Some tt, {| st_ev := ecc; st_trace := tr'; st_pl := p'' |}) ->

    (
      (exists bits e'', EvSub (ggc p0 (do_sig (MonadVM.encodeEv (evc bits et')) p0) e'') e' /\
      (et_fun e'' = et'))

      (* \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (gg p0 et') ett) *)
    ).
    (*
    (
      (exists e'', EvSub (uuc i args tpl tid n e'') e') \/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) e' /\
          EvSubT (uu i args tpl tid et') ett)
    ). *)
Proof.

  intros.

  ff.
  do_wfec_preserved.
  do_somerecons.
    assert (
        (exists bits e'', EvSub (ggc p0 (do_sig (MonadVM.encodeEv (evc bits et')) p0) e'') H13 /\
      et_fun e'' = et' )).

        (*\/
      (exists ett p' bs et',
          EvSub (hhc p' bs ett) H11 /\
          EvSubT (gg p0 et') ett)
      ). *)
    {
      eapply gg_preserved'.
      apply H.
      eassumption.
      eassumption.
      4: { eassumption. }
      eassumption.
      eassumption.
      eassumption.
    }
    destruct_conjs.

    do_evaccum.
    clear H22.
    door.
  +
    ff.
    repeat eexists.
    eassumption.
    repeat jkjke'.
  +
    repeat jkjke'.
    repeat ff.
    (*
    admit. (* TODO: eliminate this case with well_formedness conditions on t1/t2 *)
     *)

    assert (
              (exists t1', hash_sig_term t1' /\ term_sub t1' t1) \/
              (exists t2', hash_sig_term t2' /\ term_sub t2' t2) \/
              hash_sig_term (alseq (0,0) t1 t2)).
    { admit. }

    door.
    ++

      unfold not_hsh_sig in H3.
      unfold not in *.
      exfalso.
      eapply H3.
      eassumption.
      eassumption.
    ++
      door.
      +++
      
      unfold not_hsh_sig in H4.
      unfold not in *.
      exfalso.
      eapply H4.
      eassumption.
      eassumption.
      +++
        unfold hash_sig_term in *.
        destruct_conjs.
        repeat ff.
        assert (hash_sig_term (alseq (0,0) H28 H29)).
        {
          admit.
        }
        unfold not_hsh_sig in *.
        unfold not in *.
        exfalso.
        eapply H6.
        
        unfold 
        
      
        eapply sig_hsh_contra.
        apply H1.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
        eauto.
Defined.
    (*
  +
    clear H22.
    door; ff.
    ++
    right;
      repeat (eexists; eauto).

    ++
      assert (EvSubT (gg p0 H19) H22).
      {
        eapply evsubT_transitive.
        apply hhSubT.
        eassumption.
        eassumption.
      }
      
      right; 
        repeat (eexists; eauto).
     *)


*)

Lemma ggc_app: forall p0 x e H4 e',
    EvSub (ggc p0 (do_sig (MonadVM.encodeEv (evc x e)) p0) H4) e' ->
    exists e'' sigbs,
      EvSub
        (ggc p0 (checkSig H4 p0 sigbs) e'')
        (build_app_comp_evC e'). (* /\ (et_fun H4 = e). *)
    (*
    exists e'' ec,
      EvSub
        (ggc p0 (checkSig ec p0 (do_sig (MonadVM.encodeEv (evc x e)) p0)) e'')
        (build_app_comp_evC e') /\ (Some ec = reconstruct_ev (evc x e)). *)
Proof.
  intros.
  generalizeEverythingElse e'.
  induction e'; intros;
    ff.
  (*
    try evSubFacts; eauto.
    try evsub_ih.
   *)
  -
    evSubFacts.
    edestruct IHe'; eauto.
    destruct_conjs.
    subst.
    repeat eexists.
    eauto.
  -
    (*
    unfold checkSig in *. *)
    ff.
    invc H.
    +
      (*
      assert (wf_ec (evc x e)). admit.
      do_somerecons. *)
      exists ((build_app_comp_evC e')).
      (*eexists.*)
      exists ((do_sig (MonadVM.encodeEv (evc x e)) n)).
      econstructor.
    +
      edestruct IHe'; eauto.
      destruct_conjs.
      subst.
      repeat eexists.
      eauto.
  -
    evSubFacts.
    +
    edestruct IHe'1; eauto.
    destruct_conjs.
    subst.
    repeat eexists.
    eauto.
    +
      edestruct IHe'2; eauto.
      destruct_conjs.
      subst.
      repeat eexists.
      eauto.
  -
        evSubFacts.
    +
    edestruct IHe'1; eauto.
    destruct_conjs.
    subst.
    repeat eexists.
    eauto.
    +
      edestruct IHe'2; eauto.
      destruct_conjs.
      subst.
      repeat eexists.
      eauto.
Defined.

Lemma appraisal_correct_sig : forall t e e' tr tr' p p' ecc ev ee,
    well_formed_r t ->
    not_none_none t ->
    not_hash_sig_term t ->
    not_hash_sig_ev e ->
    wf_ec ee ->
    Some e = (reconstruct_ev ee) ->
    Some e' = (reconstruct_ev ecc) ->
    copland_compile t
                    {| st_ev := ee; st_trace := tr; st_pl := p |} =
    (Some tt, {| st_ev := ecc;
                 st_trace := tr';
                 st_pl := p' |}) ->

    sigEvent t p (get_et ee) ev ->
    appEvent_Sig_EvidenceC ev (build_app_comp_evC e').
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  - (* aasp case *)
    sigEventFacts.
    sigEventPFacts.
    destruct ee.
    inv_events.
    ff.
    break_match; try solve_by_inversion.
    invc H5.
    ff.
    assert (e0 = et_fun e2).
    {
      rewrite fold_recev in *.
      eapply etfun_reconstruct; eauto.
    }
    subst.
    
    repeat econstructor.
  -
    sigEventFacts.
    sigEventPFacts.
    invEvents.
    vmsts.
    ff.
    do_wf_pieces.
    do_not_none.
    do_not_hshsig.
    eapply IHt.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
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
    do_not_none.
    do_not_hshsig.
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.

    sigEventFacts.
    repeat do_pl_immut.
    subst.
    sigEventPFacts.
     do_wfec_preserved.
      do_somerecons.
    inv_events.
    + (* t1 case *)

      destruct ee.

      Check gg_preserved'.

      edestruct gg_preserved' with (t:= alseq r t1 t2).
      eassumption.
      eassumption.
      eassumption.
      3: {
        eassumption. }
      eassumption.
      3: { eassumption. }
      repeat jkjke'; repeat ff.
      2: {
        simpl.
        cbn.
        monad_unfold.
        rewrite Heqp0.
        ff.
      }
      eassumption.

      destruct_conjs.

      edestruct ggc_app.
      eassumption.

      
(*
      assert (exists e'' ec,
                 EvSub (ggc p0
                            (checkSig ec p0 (do_sig (MonadVM.encodeEv (evc x e)) p0))
                            e''
                       )
                       (build_app_comp_evC e') /\
                 (et_fun ec = e)
             ).
      {
        eapply ggc_app; eauto.
      }
 *)
      
      destruct_conjs.

      (*
      assert (e = et_fun H11).
      {
        congruence.
      } *)
      subst.
      econstructor.
      repeat jkjke'.
      repeat ff.
            (*
      eassumption.
      destruct_conjs.
      assert 
      econstructor.
      

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
      eapply hhc_app; eauto. *)
    
      


      
    + (* t2 case *)

      do_wfec_preserved.
      destruct ecc.
      destruct st_ev.
      
      eapply IHt2.
      eassumption.
      eassumption.
      eassumption.
      4: { eassumption. }
      4: { eassumption. }
      2: { eassumption. }
      2: { eassumption. }
      repeat jkjke'; repeat ff.
      eapply hshsig_ev_term_contra.
      apply H8.
      assumption.
      4: { eassumption. }
      2: { eassumption. }
      eassumption.
      eassumption.

      destruct ee.
      ff.
      assert (e4 = aeval t1 p e6).
      {
        rewrite <- eval_aeval.
        eapply cvm_refines_lts_evidence.
        eassumption.
        eassumption.
      }
      subst.
      econstructor.
      eassumption.
      econstructor.
  - (* abseq case *)
    do_wf_pieces.
    do_not_none.
    do_not_hshsig.
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    
    repeat ff.

    sigEventFacts.
    sigEventPFacts.
    repeat do_pl_immut.
    subst.

    (*
    invc H3. *)

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)


      assert (appEvent_Sig_EvidenceC (sign n1 p0 e6) (build_app_comp_evC e4)).
      {
        destruct ee; ff.

        rewrite fold_recev in *.

        assert (exists ee, Some ee = reconstruct_ev (splitEv_l s (evc e7 e8))).
        {
          destruct s.
          destruct s; destruct s0; ff.
          eauto.
          eauto.
          eauto.
          eauto.
        }
        destruct_conjs.
        assert (not_hash_sig_ev H16).
        {
          destruct s; destruct s; destruct s0; ff.
          jkjke'. ff.
          jkjke'. ff.
          cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
          cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
        }
        
          
          eapply IHt1.
          eassumption.
          eassumption.
          eassumption.
          5: { eassumption. }
          4: { jkjke. }
          2: { eassumption. }
          2: { eassumption. }
          eassumption.
          econstructor.
          destruct s; destruct s; ff.
          econstructor.
      }

      invc H16.
      econstructor.
      eauto.

    + (* t2 case *)

      assert (appEvent_Sig_EvidenceC (sign n1 p0 e6) (build_app_comp_evC e5)).
      {
        destruct ee; ff.

        rewrite fold_recev in *.

        assert (exists ee, Some ee = reconstruct_ev (splitEv_r s (evc e7 e8))).
        {
          destruct s.
          destruct s; destruct s0; ff.
          eauto.
          eauto.
          eauto.
          eauto.
        }
        destruct_conjs.
        assert (not_hash_sig_ev H16).
        {
          destruct s; destruct s; destruct s0; ff.
          jkjke'. ff.
          cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
          jkjke'. ff.
          cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
        }
          
          eapply IHt2.
          eassumption.
          eassumption.
          eassumption.
          5: { eassumption. }
          4: { jkjke'. }
          2: { eassumption. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; destruct s0; ff.
          econstructor.
      }
      
      
      invc H16.
      +++
        econstructor.
        apply ssSubr.
        eassumption.


  -
    do_wf_pieces.
    do_not_none.
    do_not_hshsig.
    vmsts.
    simpl in *.
    subst.
    ff.
    ff.
    vmsts.
    simpl in *.
    subst.
    
    repeat ff.

    sigEventFacts.
    sigEventPFacts.
    repeat do_pl_immut.
    subst.

    (*
    invc H3. *)

    do_wfec_split.

    do_wfec_preserved.

    do_wfec_firstn.
    do_wfec_skipn.

    clear_skipn_firstn.

    rewrite fold_recev in *.

    inv_events.
    + (* t1 case *)


      assert (appEvent_Sig_EvidenceC (sign n1 p0 e6) (build_app_comp_evC e4)).
      {
        destruct ee; ff.

        rewrite fold_recev in *.

        assert (exists ee, Some ee = reconstruct_ev (splitEv_l s (evc e7 e8))).
        {
          destruct s.
          destruct s; destruct s0; ff.
          eauto.
          eauto.
          eauto.
          eauto.
        }
        destruct_conjs.
        assert (not_hash_sig_ev H16).
        {
          destruct s; destruct s; destruct s0; ff.
          jkjke'. ff.
          jkjke'. ff.
          cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
          cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
        }
        
          
          eapply IHt1.
          eassumption.
          eassumption.
          eassumption.
          5: { eassumption. }
          4: { jkjke. }
          2: { eassumption. }
          2: { eassumption. }
          eassumption.
          econstructor.
          destruct s; destruct s; ff.
          econstructor.
      }

      invc H16.
      econstructor.
      eauto.

    + (* t2 case *)

      assert (appEvent_Sig_EvidenceC (sign n1 p0 e6) (build_app_comp_evC e5)).
      {
        destruct ee; ff.

        rewrite fold_recev in *.

        assert (exists ee, Some ee = reconstruct_ev (splitEv_r s (evc e7 e8))).
        {
          destruct s.
          destruct s; destruct s0; ff.
          eauto.
          eauto.
          eauto.
          eauto.
        }
        destruct_conjs.
        assert (not_hash_sig_ev H16).
        {
          destruct s; destruct s; destruct s0; ff.
          jkjke'. ff.
          cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
          jkjke'. ff.
          cbv. intros. invc H17. destruct_conjs. solve_by_inversion.
        }
          
          eapply IHt2.
          eassumption.
          eassumption.
          eassumption.
          5: { eassumption. }
          4: { jkjke'. }
          2: { eassumption. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; destruct s0; ff.
          econstructor.
      }
      
      
      invc H16.
      +++
        econstructor.
        apply ppSubr.
        eassumption.
Defined.

Lemma appraisal_correct : forall t e' tr tr' p p' ecc ev ee,
    well_formed_r t ->
    not_none_none t ->
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
    invc H2.
    
    repeat econstructor.

  - (* aatt case *)
    measEventFacts.
    evEventFacts.
    invEvents.
    vmsts.
    ff.
    do_wf_pieces.
    do_not_none.
    eapply IHt.
    eassumption.
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
    do_not_none.
    vmsts.
    simpl in *.
    subst.
    repeat ff.

    vmsts.

    measEventFacts.
    repeat do_pl_immut.
    subst.
    invc H9.
    inv_events.
    + (* t1 case *)

      edestruct uu_preserved.
      apply H5.
      apply H6.
      eassumption.
      eassumption.
      4: { eassumption. }
      4: { eassumption. }
      eassumption.
      eassumption.
      eassumption.

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
    
    do_wf_pieces.
    do_not_none.
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
    invc H3.

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
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; destruct s; ff.
          econstructor.
      }
      
      invc H11.
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

      assert (appEvent_EvidenceC
                (umeas n1 p0 i args tpl tid) (build_app_comp_evC (e4))).
      {      
        destruct ee; ff.

        rewrite fold_recev in *.
          
          eapply IHt2.
          eassumption.
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; destruct s0; ff.
          econstructor.
      }

      invc H11.
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
    do_not_none.
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
    invc H3.

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
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; destruct s; ff.
          econstructor.
      }

      invc H11.
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
          eassumption.
          2: { jkjke'. }
          2: { eassumption. }
          eassumption.
          econstructor. ff.
          destruct s; destruct s0; ff.
          econstructor.
      }

      invc H11.
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

Require Import Impl_appraisal_alt Appraisal_AltImpls_Eq.
    

Lemma appraisal_correct_alt : forall t e' tr tr' p p' bits' et' ev ee,
    well_formed_r t ->
    not_none_none t ->
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
  eassumption.
  3: { eassumption. }
  eassumption.
  2: { eassumption. }
  2: { eassumption. }
  3: { tauto. }
  eassumption.
  eassumption.
Defined.

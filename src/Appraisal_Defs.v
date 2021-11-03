Require Import Term_Defs Term Maps ConcreteEvidence OptMonad Auto More_lists Appraisal_Evidence MonadVM.

(* Require Import Impl_appraisal (*MonadAM*). *)

Require Import AutoApp StructTactics.

Require Import List.
Import ListNotations.

Require Import Lia Coq.Program.Tactics.

Definition checkASP (params:ASP_PARAMS) (bs:BS) : option BS.
Admitted.

Definition checkASPF (params:ASP_PARAMS) (bs:BS) : BS := fromSome default_bs (checkASP params bs).

Definition checkSigBits (ls:EvBits) (p:Plc) (sig:BS) : option BS.
Admitted.

Definition checkSigBitsF (ls:EvBits) (p:Plc) (sig:BS) : BS :=
  fromSome default_bs (checkSigBits ls p sig).

Definition checkNonce (nid:nat) (val:BS) : option BS.
Admitted.

Definition checkNonceF (nid:nat) (val:BS) : BS :=
  fromSome default_bs (checkNonce nid val).

Definition checkSig (e:EvidenceC) (p:Plc) (sig:BS) : option BS :=
  checkSigBits (encodeEv e) p sig.

Definition checkSigF (e:EvidenceC) (p:Plc) (sig:BS) : BS :=
  fromSome default_bs (checkSig e p sig).

Fixpoint checkHash (e:Evidence) (p:Plc) (hash:BS) : option BS :=
  match e with
  | gg _ _ => None
  | mt => ret default_bs (* TODO: implement reconstruct_hash and ignore mt *)
  | nn _ => ret default_bs (* TODO: reconstruct_hash will grab nonce value here *)
  | uu _  _ e' => checkHash e' p hash
  | hh _ e' => checkHash e' p hash
  | ss e1 e2 =>
    res1 <- checkHash e1 p hash ;;
    res2 <- checkHash e2 p hash ;;
    ret default_bs
  | pp e1 e2 =>
    res1 <- checkHash e1 p hash ;;
    res2 <- checkHash e2 p hash ;;
    ret default_bs
  end.

Definition checkHashF (e:Evidence) (p:Plc) (hash:BS) : BS :=
  fromSome default_bs (checkHash e p hash).
(*

Definition checkHash (e:Evidence) (p:Plc) (hash:BS) : BS :=
  fromSome 0 None.
  (*
  fromSome 0 (checkHash' e p hash). *)
 *)

(*
Admitted.
 *)

Inductive evidenceEvent: Ev -> Prop :=
| uev: forall n p i args tpl tid, evidenceEvent (umeas n p i args tpl tid).

Definition measEvent (t:AnnoTerm) (p:Plc) (e:Evidence) (ev:Ev) : Prop :=
  events t p e ev /\ evidenceEvent ev.

Inductive sigEventP: Ev -> Prop :=
| sev: forall n p e, sigEventP (sign n p e).

Definition sigEvent (t:AnnoTerm) (p:Plc) (e:Evidence) (ev:Ev) : Prop :=
  events t p e ev /\ sigEventP ev.

Inductive appEvent_EvidenceC : Ev -> EvidenceC -> Prop :=
| aeuc: forall i args tpl tid e e' n p,
    EvSub (uuc (asp_paramsC i args tpl tid) p (checkASPF (asp_paramsC i args tpl tid) (do_asp (asp_paramsC i args tpl tid) p n)) e') e ->
    appEvent_EvidenceC (umeas n p i args tpl tid) e
| ahuc: forall i args tpl tid e' et n p pi bs e,
    EvSubT (uu (asp_paramsC i args tpl tid) p e') et ->
    EvSub (hhc pi (checkHashF et pi bs) et) e ->
    appEvent_EvidenceC (umeas n p i args tpl tid) e.

Inductive appEvent_Sig_EvidenceC: Ev -> EvidenceC -> Prop :=
| asigc: forall n p e e' e'' ee,
    EvSub (ggc p (checkSigF e' p (do_sig ee p n)) e'') e ->
    appEvent_Sig_EvidenceC (sign n p (et_fun e')) e.

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

Inductive reaches_HSH : AnnoTerm -> Prop :=
| rh_hsh: forall r, reaches_HSH (aasp r (HSH))
| rh_aatt: forall r p t,
    reaches_HSH t ->
    reaches_HSH (aatt r p t)
| rh_lseql: forall r t1 t2,
    reaches_HSH t1 ->
    reaches_HSH (alseq r t1 t2)
| rh_lseqr: forall r t1 t2,
    reaches_HSH t2 ->
    reaches_HSH (alseq r t1 t2)
| rh_bseql: forall r sp2 t1 t2,
    reaches_HSH t1 ->
    reaches_HSH (abseq r (ALL,sp2) t1 t2)
| rh_bseqr: forall r sp1 t1 t2,
    reaches_HSH t2 ->
    reaches_HSH (abseq r (sp1,ALL) t1 t2)
| rh_bparl: forall r sp2 t1 t2,
    reaches_HSH t1 ->
    reaches_HSH (abpar r (ALL,sp2) t1 t2)
| rh_bparr: forall r sp1 t1 t2,
    reaches_HSH t2 ->
    reaches_HSH (abpar r (sp1,ALL) t1 t2).
Hint Constructors reaches_HSH : core.

Definition hash_sig_term (t:AnnoTerm): Prop :=
  exists r r1 t1 t2,
  t = alseq r t1 t2 /\
  term_sub (aasp r1 SIG) t1 /\
  reaches_HSH t2.
  (*
  term_sub (aasp r2 HSH) t2. *)

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
  ((gg_sub e) -> ~ (reaches_HSH t)).

Lemma inv_recon_mt: forall ls et,
    reconstruct_evP (evc ls et) mtc ->
    et = mt.
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try solve_by_inversion.
Defined.

Ltac do_inv_recon_mt :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) mtc

     |- _] =>
    assert_new_proof_by (et = mt) ltac:(eapply inv_recon_mt; apply H)
  end;
  subst.

Lemma inv_recon_mt': forall ls e,
    reconstruct_evP (evc ls mt) e ->
    e = mtc.
Proof.
  intros.
  invc H.
  repeat ff; try solve_by_inversion.
Defined.

Ltac do_inv_recon_mt' :=
  match goal with
  | [H: reconstruct_evP (evc _ mt) ?e

     |- _] =>
    assert_new_proof_by (e = mtc) ltac:(eapply inv_recon_mt'; apply H)
  end;
  subst.


Lemma inv_recon_nn: forall ls et n n0,
    reconstruct_evP (evc ls et) (nnc n n0) ->
    et = nn n /\ ls = [n0].
Proof.
  intros.
  invc H.
  destruct et; repeat ff; destruct ls; try solve_by_inversion.
Defined.

Ltac do_inv_recon_nn :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (nnc ?n ?nval)

     |- _] =>
    assert_new_proof_by (et = nn n /\ ls = [nval]) ltac:(eapply inv_recon_nn; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_uu: forall ls et params n2 p ec,
    reconstruct_evP (evc ls et) (uuc params p n2 ec)  ->
    (exists ls' et', et = uu params p et' /\
                ls = n2 :: ls'). (* /\
                wf_ec (evc ls' et')). *)
Proof.
  intros.
  invc H.
  repeat ff.
  destruct et; repeat ff; try solve_by_inversion.
  
  repeat eexists.
  destruct ls; ff.
Defined.

Ltac do_inv_recon_uu :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (uuc ?params ?p ?uval _)

     |- _] =>
    assert_new_proof_by (exists ls' et', et = uu params p et' /\
                        ls = uval :: ls')
                        ltac:(eapply inv_recon_uu; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_gg: forall ls et n n0 ec,
    reconstruct_evP (evc ls et) (ggc n n0 ec) ->
    (exists ls' et', et = gg n et' /\
                ls = n0 :: ls').
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try solve_by_inversion.

  repeat eexists.
  destruct ls; ff.
Defined.

Ltac do_inv_recon_gg :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (ggc ?n ?n0 _)

     |- _] =>
    assert_new_proof_by (exists ls' et', et = gg n et' /\
                                    ls = n0 :: ls')
                        ltac:(eapply inv_recon_gg; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_hh: forall ls et n n0 et',
    reconstruct_evP (evc ls et) (hhc n n0 et') ->
    (et = hh n et' ) /\ ls = [n0].
Proof.
  intros.
  invc H.
  destruct et; repeat ff; destruct ls; try solve_by_inversion.
Defined.

Ltac do_inv_recon_hh :=
  match goal with
  | [H: reconstruct_evP (evc ?ls ?et) (hhc ?n ?hval ?et')

     |- _] =>
    assert_new_proof_by (et = hh n et' /\ ls = [hval])
                        ltac:(eapply inv_recon_hh; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_ss: forall ls et ec1 ec2,
    reconstruct_evP (evc ls et) (ssc ec1 ec2) ->
    (exists et1 et2, et = ss et1 et2).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Ltac do_inv_recon_ss :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) (ssc _ _)

     |- _] =>
    assert_new_proof_by (exists et1 et2, et = ss et1 et2)
                        ltac:(eapply inv_recon_ss; apply H)
  end;
  destruct_conjs;
  subst.

Lemma inv_recon_pp: forall ls et ec1 ec2,
    reconstruct_evP (evc ls et) (ppc ec1 ec2) ->
    (exists et1 et2, et = pp et1 et2).
Proof.
  intros.
  invc H.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Ltac do_inv_recon_pp :=
  match goal with
  | [H: reconstruct_evP (evc _ ?et) (ppc _ _)

     |- _] =>
    assert_new_proof_by (exists et1 et2, et = pp et1 et2)
                        ltac:(eapply inv_recon_pp; apply H)
  end;
  destruct_conjs;
  subst.

Ltac do_inv_recon :=
  try do_inv_recon_mt;
  try do_inv_recon_mt';
  try do_inv_recon_nn;
  try do_inv_recon_uu;
  try do_inv_recon_gg;
  try do_inv_recon_hh;
  try do_inv_recon_ss;
  try do_inv_recon_pp.

Lemma nhse_uuc: forall params n2 n3 e,
    not_hash_sig_ev (uuc params n2 n3 e) ->
    not_hash_sig_ev e.
Proof.
  intros.
  unfold not_hash_sig_ev in *.
  intros.
  unfold not in *; intros.
  eapply H.
  eassumption.
  econstructor.
  eassumption.
Defined.

Ltac do_nhse_uuc:=
  match goal with
  | [H: not_hash_sig_ev (uuc _ _ _ ?e)
     |- _] =>
    assert_new_proof_by (not_hash_sig_ev e) ltac:(eapply nhse_uuc; apply H)
  end.

Lemma nhse_ggc: forall n n0 e,
    not_hash_sig_ev (ggc n n0 e) ->
    not_hash_sig_ev e.
Proof.
  intros.
  unfold not_hash_sig_ev in *.    
  unfold not in *; intros.
  eapply H.
  eassumption.
  econstructor.
  eassumption.
Defined.

Ltac do_nhse_ggc:=
  match goal with
  | [H: not_hash_sig_ev (ggc _ _ ?e)
     |- _] =>
    assert_new_proof_by (not_hash_sig_ev e) ltac:(eapply nhse_ggc; apply H)
  end.

Lemma nhse_hhc: forall n n0 e x y,
    not_hash_sig_ev (hhc n n0 e) ->
    ~ (EvSubT (gg x y) e).
Proof.
  intros.
  unfold not_hash_sig_ev in *.    
  unfold not in *; intros.
  eapply H.
  econstructor.
  repeat eexists.
  eassumption.
  econstructor.
Defined.

Lemma nhse_hhc': forall n n0 n1 e x y,
    not_hash_sig_ev (hhc n n0 e) ->
    EvSubT (gg x y) (hh n1 e) ->
    False.
Proof.
  intros.
  eapply nhse_hhc.
  eassumption.
  invc H0.
  eassumption.
Defined.

Ltac do_nhse_hhc_contra:=
  match goal with
  | [H: not_hash_sig_ev (hhc _ _ ?e),
        H2: EvSubT (gg _ _) (hh _ ?e)
     |- _] =>
    assert_new_proof_by (False) ltac:(eapply nhse_hhc'; [apply H | apply H2])
  end;
  solve_by_inversion.

Lemma nhse_ssc: forall e1 e2,
    not_hash_sig_ev (ssc e1 e2) ->
    not_hash_sig_ev e1 /\ not_hash_sig_ev e2.
Proof.
  intros.
  unfold not_hash_sig_ev in *.
  unfold not in *; intros.
  split; intros.
  -
    eapply H.
    eassumption.
    econstructor.
    eassumption.
  -
    eapply H.
    eassumption.
    apply ssSubr.
    eassumption.
Defined.

Ltac do_nhse_ssc:=
  match goal with
  | [H: not_hash_sig_ev (ssc ?e1 ?e2)
     |- _] =>
    assert_new_proof_by (not_hash_sig_ev e1 /\
                         not_hash_sig_ev e2) ltac:(eapply nhse_ssc; apply H)
  end; destruct_conjs.


Lemma nhse_ppc: forall e1 e2,
    not_hash_sig_ev (ppc e1 e2) ->
    not_hash_sig_ev e1 /\ not_hash_sig_ev e2.
Proof.
  intros.
  unfold not_hash_sig_ev in *.
  unfold not in *; intros.
  split; intros.
  -
    eapply H.
    eassumption.
    econstructor.
    eassumption.
  -
    eapply H.
    eassumption.
    apply ppSubr.
    eassumption.
Defined.

Ltac do_nhse_ppc:=
  match goal with
  | [H: not_hash_sig_ev (ppc ?e1 ?e2)
     |- _] =>
    assert_new_proof_by (not_hash_sig_ev e1 /\
                         not_hash_sig_ev e2) ltac:(eapply nhse_ppc; apply H)
  end; destruct_conjs.


Ltac do_nhse :=
  try do_nhse_uuc;
  try do_nhse_hhc_contra;
  try do_nhse_ggc;
  try do_nhse_ssc;
  try do_nhse_ppc.

Lemma recon_inv_uu: forall n2 n3 H2 H3 e params,
    reconstruct_evP
      (evc (n3 :: H2) (uu params n2 H3))
      (uuc params n2 n3 e) ->
    reconstruct_evP (evc H2 H3) e.
Proof.
  intros.
  invc H.
  repeat ff.
  econstructor.
  symmetry.
  tauto.
Defined.

Ltac do_recon_inv_uu :=
  match goal with
  | [H: reconstruct_evP
          (evc (_ :: ?H2) (uu _ _ ?H3))
          (uuc _ _ _ ?e)
     |- _] =>
    assert_new_proof_by (reconstruct_evP (evc H2 H3) e) ltac:(eapply recon_inv_uu; apply H)
  end.

Lemma recon_inv_gg: forall sig ls p et e,
    reconstruct_evP
      (evc (sig :: ls) (gg p et))
      (ggc p sig e) ->
    reconstruct_evP (evc ls et) e.
Proof.
  intros.
  invc H.
  repeat ff.
  econstructor.
  symmetry.
  tauto.
Defined.

Ltac do_recon_inv_gg :=
  match goal with
  | [H: reconstruct_evP
          (evc (_ :: ?ls) (gg _ ?et))
          (ggc _ _ ?e)
     |- _] =>
    assert_new_proof_by (reconstruct_evP (evc ls et) e) ltac:(eapply recon_inv_gg; apply H)
  end.

Lemma recon_inv_ss: forall ls H1 H2 ec1 ec2,
    reconstruct_evP (evc ls (ss H1 H2)) (ssc ec1 ec2) ->
    reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
    reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2.
Proof.
  intros.
  invc H.
  repeat ff.
  split;
    econstructor;
    try 
      symmetry; eassumption.
Defined.

Lemma recon_inv_pp: forall ls H1 H2 ec1 ec2,
    reconstruct_evP (evc ls (pp H1 H2)) (ppc ec1 ec2) ->
    reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
    reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2.
Proof.
  intros.
  invc H.
  repeat ff.
  split;
    econstructor;
    try 
      symmetry; eassumption.
Defined.

Ltac do_recon_inv_ss :=
  match goal with
  | [H: reconstruct_evP
          (evc ?ls (ss ?H1 ?H2))
          (ssc ?ec1 ?ec2)
     |- _] =>
    assert_new_proof_by
      (reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
       reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2)
      ltac:(eapply recon_inv_ss; apply H)
  end; destruct_conjs.

Ltac do_recon_inv_pp :=
  match goal with
  | [H: reconstruct_evP
          (evc ?ls (pp ?H1 ?H2))
          (ppc ?ec1 ?ec2)
     |- _] =>
    assert_new_proof_by
      (reconstruct_evP (evc (firstn (et_size H1) ls) H1) ec1 /\
       reconstruct_evP (evc (skipn (et_size H1) ls) H2)  ec2)
      ltac:(eapply recon_inv_pp; apply H)
  end; destruct_conjs.

Ltac do_recon_inv :=
  try do_recon_inv_uu;
  try do_recon_inv_gg;
  try do_recon_inv_ss;
  try do_recon_inv_pp.

Lemma etfun_reconstruct: forall e e0 e1,
    reconstruct_evP (evc e0 e1) e ->
    e1 = et_fun e.
Proof.
  intros.
  generalizeEverythingElse e1.
  induction e1; intros e e0 H;
    do_inv_recon;
    ff;
    invc H;
    repeat ff;
    rewrite fold_recev in *;
    do_wrap_reconP;
    repeat jkjke.
Defined.

Ltac dest_evc :=
  repeat
    match goal with
    | [H: EvC |-  _ ] => destruct H
    end.

Ltac inv_wfec :=
  repeat
    match goal with
    | [H: wf_ec _ |-  _ ] => invc H
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

Lemma some_reconsP : forall e,
    wf_ec e ->
    exists ee, reconstruct_evP e ee.
Proof.
  intros.
  edestruct some_recons.
  eassumption.
  eexists.
  econstructor.
  eassumption.
Defined.

Ltac do_somerecons :=
  repeat
    match goal with
    | [H: wf_ec ?e
       |- _ ] =>
      assert_new_proof_by
        (exists x, reconstruct_evP e x)
        ltac:(eapply some_reconsP; apply H)     
    end; destruct_conjs.

Ltac measEventFacts :=
  match goal with
  | [H: measEvent _ _ _ _ |- _] => invc H
  end.

Ltac evEventFacts :=
  match goal with
  | [H: evidenceEvent _ |- _] => invc H
  end.

Ltac invEvents :=
  match goal with
  | [H: events _ _ _ _  |- _] => invc H
  end.

Lemma recon_encodeEv : forall ls et ec,
    wf_ec (evc ls et) -> 
    reconstruct_evP (evc ls et) ec ->
    ls = encodeEv ec.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    ff.
    do_inv_recon.
    inv_wfec.
    destruct ls; try solve_by_inversion.
  (* TODO: exclude mt case? *)
  -
    ff.
    do_inv_recon.
    tauto.
  -
    ff.
    do_inv_recon.
    do_recon_inv.
    inv_wfec.
    repeat ff.

    edestruct IHec.
    2: {
      eassumption.
      
    }
    econstructor.
    eassumption.
    tauto.
  -
    ff.
    do_inv_recon.
    do_recon_inv.
    inv_wfec.
    repeat ff.
    edestruct IHec.
    2: {
      eassumption.
    }

    econstructor.
    eassumption.
    tauto.
  -
    ff.
    do_inv_recon.
    tauto.  
  -
    ff.
    do_inv_recon.

    do_recon_inv.

    inv_wfec.
    ff.
    
    jkjke'.
    jkjke'.
    rewrite firstn_skipn.
    tauto.

    econstructor.
    eapply firstn_long. lia.

    econstructor.
    eapply skipn_long. lia.

  -
    ff.
    do_inv_recon.
    do_recon_inv.
    inv_wfec.
    ff.
    
    jkjke'.
    jkjke'.
    rewrite firstn_skipn.
    tauto.

    econstructor.
    eapply firstn_long. lia.

    econstructor.
    eapply skipn_long. lia.
Defined.

Lemma wf_recon: forall e et ec,
    reconstruct_evP (evc e et) ec ->
    wf_ec (evc e et).
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    do_inv_recon.
    invc H.
    repeat ff.
    econstructor.
    tauto.
  -
    do_inv_recon.
    econstructor.
    tauto.
  -
    do_inv_recon.
    do_recon_inv.
    assert (wf_ec (evc H0 H1)) by eauto.
    inv_wfec.
    econstructor.
    ff.
    lia.
  -
    do_inv_recon.
    do_recon_inv.
    assert (wf_ec (evc H0 H1)) by eauto.
    inv_wfec. 
    econstructor.
    ff.
    lia.

  -
    do_inv_recon.
    econstructor.
    tauto.
  -
    do_inv_recon.
    do_recon_inv.

    assert (wf_ec (evc (firstn (et_size H0) e) H0)) as HH.
    {
      eapply IHec1.
      eassumption.
    }
    
    assert (wf_ec (evc (skipn (et_size H0) e) H1)) as HH'.
    {
      eapply IHec2.
      econstructor.
      ff.
    }
    inv_wfec.
    
    econstructor.
    ff.

    rewrite <- H6.
    rewrite <- H5.

    assert (e = (firstn (et_size H0) e) ++ (skipn (et_size H0) e)) as HH.
    
    { rewrite firstn_skipn.
      tauto.
    }
    rewrite HH at 1.
    eapply app_length.

  -
    do_inv_recon.
    do_recon_inv.

    assert (wf_ec (evc (firstn (et_size H0) e) H0)) as HH.
    {
      eapply IHec1.
      eassumption.
    }
    
    assert (wf_ec (evc (skipn (et_size H0) e) H1)) as HH'.
    {
      eapply IHec2.
      econstructor.
      ff.
    }
    inv_wfec.
    
    econstructor.
    ff.

    rewrite <- H6.
    rewrite <- H5.

    assert (e = (firstn (et_size H0) e) ++ (skipn (et_size H0) e)) as HH.
    
    { rewrite firstn_skipn.
      tauto.
    }
    rewrite HH at 1.
    eapply app_length.
Defined.

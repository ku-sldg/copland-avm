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

Require Import Impl_appraisal_alt.

Set Nested Proofs Allowed.


Check Impl_appraisal_alt.build_app_comp_evC.
Check Impl_appraisal.build_app_comp_evC.

Lemma inv_recon_mt: forall ls et,
    reconstruct_ev' ls et = Some mtc ->
    et = mt.
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
Defined.

Lemma inv_recon_nn: forall ls et n n0,
    reconstruct_ev' ls et = Some (nnc n n0) ->
    et = nn n.
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
Defined.

Lemma inv_recon_uu: forall ls et n l n0 n1 n2 ec,
    reconstruct_ev' ls et = Some (uuc n l n0 n1 n2 ec) ->
    (exists et', et = uu n l n0 n1 et').
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Lemma inv_recon_gg: forall ls et n n0 ec,
    reconstruct_ev' ls et = Some (ggc n n0 ec) ->
    (exists et', et = gg n et').
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Lemma inv_recon_hh: forall ls et n n0 et',
    reconstruct_ev' ls et = Some (hhc n n0 et') ->
    (et = hh n et' ).
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
Defined.

Lemma inv_recon_ss: forall ls et ec1 ec2,
    reconstruct_ev' ls et = Some (ssc ec1 ec2) ->
    (exists et1 et2, et = ss et1 et2).
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Lemma inv_recon_pp: forall ls et ec1 ec2,
    reconstruct_ev' ls et = Some (ppc ec1 ec2) ->
    (exists et1 et2, et = pp et1 et2).
Proof.
  intros.
  destruct et; repeat ff; try solve_by_inversion.
  eauto.
Defined.

Lemma recon_encodeEv : forall ls et ec,
    wf_ec (evc ls et) -> 
    reconstruct_ev' ls et = Some ec ->
    ls = encodeEv ec.
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    ff.
    assert (et = mt).
    {
      eapply inv_recon_mt; eauto.
    }
    subst.
    invc H.
    ff.
    destruct ls; try solve_by_inversion.
  (* TODO: exclude mt case? *)
  -
    ff.
    assert (et = nn n).
    {
      eapply inv_recon_nn; eauto.
    }
    subst.
    repeat ff.
    destruct ls; try solve_by_inversion.

    (*
    invc H.
    ff.
    assert (e = []).
    destruct e; try solve_by_inversion.
    ff. *)
  -
    ff.
    assert (exists et', et = uu n l n0 n1 et').
    {
      eapply inv_recon_uu; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H.
    ff.
    edestruct IHec with (ls := e).
    2: {
      eassumption.
    }
    econstructor.
    destruct ls; try solve_by_inversion.
    unfold peel_bs in *.
    ff.
  -
    ff.
    assert (exists et', et = gg n et').
    {
      eapply inv_recon_gg; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H.
    ff.
    edestruct IHec with (ls := e).
    2: {
      eassumption.
    }
    econstructor.
    destruct ls; try solve_by_inversion.
    unfold peel_bs in *.
    ff.
  -
    ff.
    assert (et = hh n e).
    {
      eapply inv_recon_hh; eauto.
    }
    subst.
    repeat ff.
    invc H.
    ff.
    destruct ls; try solve_by_inversion.
  -
    ff.
    assert (exists et1 et2, et = ss et1 et2).
    {
      eapply inv_recon_ss; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H.
    ff.

    assert ((firstn (et_size H1) ls) = encodeEv ec1).
    { eapply IHec1 with (et:= H1).
      econstructor.
      eapply firstn_long.
      lia.
      eassumption.
    }

    assert ((skipn (et_size H1) ls) = encodeEv ec2).
    {
      eapply IHec2 with (et := H2).
      econstructor.
      eapply skipn_long.
      lia.
      eassumption.
    }
    jkjke'.
    jkjke'.
    Search firstn.
    rewrite firstn_skipn.
    tauto.
    -
      ff.
    assert (exists et1 et2, et = pp et1 et2).
    {
      eapply inv_recon_pp; eauto.
    }
    destruct_conjs.
    subst.
    repeat ff.
    invc H.
    ff.

    assert ((firstn (et_size H1) ls) = encodeEv ec1).
    { eapply IHec1 with (et:= H1).
      econstructor.
      eapply firstn_long.
      lia.
      eassumption.
    }

    assert ((skipn (et_size H1) ls) = encodeEv ec2).
    {
      eapply IHec2 with (et := H2).
      econstructor.
      eapply skipn_long.
      lia.
      eassumption.
    }
    jkjke'.
    jkjke'.
    Search firstn.
    rewrite firstn_skipn.
    tauto.
Defined.

Lemma wf_recon: forall e et ec,
    reconstruct_ev' e et = Some ec ->
    wf_ec (evc e et).
Proof.
  intros.
  generalizeEverythingElse ec.
  induction ec; intros.
  -
    assert (et = mt).
    eapply inv_recon_mt; eauto.
    subst.
    repeat ff.
    econstructor.
    tauto.
  -
    assert (et = nn n) by (eapply inv_recon_nn; eauto).
    subst.
    repeat ff.
    econstructor.
    ff.
    destruct e; try solve_by_inversion.
  -
    assert (exists et', et = uu n l n0 n1 et').
    { eapply inv_recon_uu; eauto. }
    destruct_conjs.
    subst.
    repeat ff.
    assert (wf_ec (evc e0 H0)) by eauto.
    econstructor.
    ff.
    invc H.
    destruct e; try solve_by_inversion.
    ff.
    lia.
  -
    assert (exists et', et = gg n et').
    { eapply inv_recon_gg; eauto. }
    destruct_conjs.
    subst.
    repeat ff.
    assert (wf_ec (evc e0 H0)) by eauto.
    econstructor.
    ff.
    invc H.
    destruct e; try solve_by_inversion.
    ff.
    lia.
  -
    assert (et = hh n e).
    { eapply inv_recon_hh; eauto.
    }
    subst.
    repeat ff.
    
    
    econstructor.
    ff.
    destruct e0; try solve_by_inversion.
  -
    assert (exists et1 et2, et = ss et1 et2).
    { eapply inv_recon_ss; eauto. }
    destruct_conjs.
    subst.
    repeat ff.

    assert (wf_ec (evc (firstn (et_size H0) e) H0)) by eauto.

    assert (wf_ec (evc (skipn (et_size H0) e) H1)) by eauto.

    invc H; invc H2.
    econstructor.
    ff.
    rewrite <- H4.
    rewrite <- H3.
    Search firstn.
    Search firstn.
    assert (e = (firstn (et_size H0) e) ++ (skipn (et_size H0) e)).
    
    { rewrite firstn_skipn.
      tauto.
    }
    rewrite H at 1.
    Check app_length.
    eapply app_length.
  -
    assert (exists et1 et2, et = pp et1 et2).
    { eapply inv_recon_pp; eauto. }
    destruct_conjs.
    subst.
    repeat ff.

    assert (wf_ec (evc (firstn (et_size H0) e) H0)) by eauto.

    assert (wf_ec (evc (skipn (et_size H0) e) H1)) by eauto.

    invc H; invc H2.
    econstructor.
    ff.
    rewrite <- H4.
    rewrite <- H3.
    Search firstn.
    Search firstn.
    assert (e = (firstn (et_size H0) e) ++ (skipn (et_size H0) e)).
    
    { rewrite firstn_skipn.
      tauto.
    }
    rewrite H at 1.
    Check app_length.
    eapply app_length.
Defined.


Lemma appraisal_alt : forall ec1 ec2 ec2' ls et,

  Some ec1 = Impl_appraisal_alt.build_app_comp_evC et ls ->
  Some ec2 = Impl_appraisal.reconstruct_ev (evc ls et) ->
  ec2' = Impl_appraisal.build_app_comp_evC ec2 ->
  ec1 = ec2'.
Proof.
  intros.
  generalizeEverythingElse ec2.
  induction ec2; intros.
  -
    ff.
    subst.
    assert (et = mt).
    { eapply inv_recon_mt; eauto. }
    subst.
    ff.
  -
    ff.
    subst.
    assert (et = nn n).
    { eapply inv_recon_nn; eauto. }
    subst.
    repeat ff.
  -
    ff.
    subst.
    ff.
    assert (exists et', et = uu n l n0 n1 et').
    { eapply inv_recon_uu; eauto. }
    destruct_conjs.
    subst.
    repeat ff.

    assert (e0 = (Impl_appraisal.build_app_comp_evC e1)).
    {
      eapply IHec2.
      jkjke.
      jkjke.
      tauto.
    }
    subst.
    congruence.
  -
    ff.
    subst.
    ff.
    assert (exists et', et = gg n et').
    { eapply inv_recon_gg; eauto. }
    destruct_conjs.
    subst.
    repeat ff.

    assert (e0 = (Impl_appraisal.build_app_comp_evC e1)).
    {
      eapply IHec2.
      jkjke.
      jkjke.
      tauto.
    }
    subst.
    unfold checkSig.
    assert (checkSigBits e n n1 =
            checkSigBits (encodeEv e1) n n1).
    {
      assert (e = encodeEv e1).
      {
        eapply recon_encodeEv.
        2: { eassumption. }

        eapply wf_recon; eauto.
      }
      congruence.
    }
    congruence.
  -
    ff.
    subst.
    assert (et = hh n e).
    { eapply inv_recon_hh; eauto.
    }
    subst.
    repeat ff.
  -
    ff.
    assert (exists et1 et2, et = ss et1 et2).
    { eapply inv_recon_ss; eauto. }
    destruct_conjs.
    subst.
    repeat ff.

    assert (e = (Impl_appraisal.build_app_comp_evC e1))
           by eauto.

    assert (e0 = (Impl_appraisal.build_app_comp_evC e2))
      by eauto.
    
    congruence.
  -
    ff.
    assert (exists et1 et2, et = pp et1 et2).
    { eapply inv_recon_pp; eauto. }
    destruct_conjs.
    subst.
    repeat ff.

    assert (e = (Impl_appraisal.build_app_comp_evC e1))
           by eauto.

    assert (e0 = (Impl_appraisal.build_app_comp_evC e2))
      by eauto.
    
    congruence.
Defined.


(*
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
*)

Require Import Maps Event_system Term_system MonadVM ConcreteEvidence.
Require Import Impl_vm Helpers_VmSemantics VmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp.

Require Import StAM Appraisal_Defs Impl_appraisal Impl_appraisal_alt (*MonadAM*).

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Require Import Lia.

Set Nested Proofs Allowed.


Lemma appraisal_alt : forall ec1 ec2 ec2' ls et,

  Some ec1 = Impl_appraisal_alt.build_app_comp_evC et ls ->
  Some ec2 = reconstruct_ev (evc ls et) ->
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
    unfold checkNonceF.
    jkjke.
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
    unfold checkASPF.
    jkjke.
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
    unfold checkSigF.
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
    rewrite <- H.
    rewrite Heqo1.
    ff.
  -
    ff.
    subst.
    assert (et = hh n e).
    { eapply inv_recon_hh; eauto.
    }
    subst.
    repeat ff.
    unfold checkHashF.
    jkjke.
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

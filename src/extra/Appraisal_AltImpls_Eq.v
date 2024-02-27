Require Import Event_system Term_system ConcreteEvidence Appraisal_Evidence.
Require Import Cvm_Impl Helpers_CvmSemantics CvmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp Defs.

Require Import Appraisal_Defs Impl_appraisal Impl_appraisal_alt (*MonadAM*).

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Require Import Lia.

Lemma appraisal_alt : forall ec1 ec2 ec2' ls et,

  Some ec1 = Impl_appraisal.build_app_comp_evC et ls ->
  reconstruct_evP (evc ls et) ec2 ->
  ec2' = Impl_appraisal_alt.build_app_comp_evC ec2 ->
  ec1 = ec2'.
Proof.
  intros.
  generalizeEverythingElse ec2.
  induction ec2; intros.
  -
    do_inv_recon.
    ff.
  -
    do_inv_recon.
    repeat ff.
    unfold OptMonad_Coq.bind in *.
    unfold OptMonad_Coq.ret in *.
    repeat ff.
    unfold checkNonceF.
    jkjke.
  -
    do_inv_recon.
    repeat ff.
    unfold OptMonad_Coq.bind in *.
    unfold OptMonad_Coq.ret in *.
    repeat ff.
    
    repeat ff.

    assert (e = (Impl_appraisal_alt.build_app_comp_evC ec2)).
    {
      eapply IHec2.
      jkjke.
      invc H0.
      repeat ff.
      unfold OptMonad_Coq.bind in *.
      unfold OptMonad_Coq.ret in *.
      repeat ff.
      econstructor.
      ff.
      tauto.
    }
    subst.
    unfold checkASPF.
    jkjke.
  -
    do_inv_recon.
    do_recon_inv.
    
    repeat ff.
    unfold OptMonad_Coq.bind in *.
    unfold OptMonad_Coq.ret in *.
    repeat ff.

    assert (e = (Impl_appraisal_alt.build_app_comp_evC ec2)) by eauto.
    subst.
    unfold checkSig.
    unfold checkSigF.
    unfold checkSig.
    assert (checkSigBits H2 p b =
            checkSigBits (encodeEv ec2) p b).
    {
      assert (H2 = encodeEv ec2).
      {
        eapply recon_encodeEv.
        eapply wf_recon.
        eassumption.
        eassumption.
      }
      subst.
      tauto.
    }
    rewrite <- H.
    rewrite Heqo0.
    cbn in *.
    tauto.
  -
    do_inv_recon.
    repeat ff.
    unfold OptMonad_Coq.bind in *.
    unfold OptMonad_Coq.ret in *.
    repeat ff.
    unfold checkHashF.
    jkjke.
  -
    do_inv_recon.
    do_recon_inv. 
    repeat ff.
    unfold OptMonad_Coq.bind in *.
    unfold OptMonad_Coq.ret in *.
    repeat ff.
    assert (e = (Impl_appraisal_alt.build_app_comp_evC ec2_1)) by eauto.
    assert (e0 = (Impl_appraisal_alt.build_app_comp_evC ec2_2)) by eauto. 
    congruence.

  -
    do_inv_recon.
    do_recon_inv.
    repeat ff.
    unfold OptMonad_Coq.bind in *.
    unfold OptMonad_Coq.ret in *.
    repeat ff.
    assert (e = (Impl_appraisal_alt.build_app_comp_evC ec2_1)) by eauto.   
    assert (e0 = (Impl_appraisal_alt.build_app_comp_evC ec2_2)) by eauto.
    congruence.
Defined.

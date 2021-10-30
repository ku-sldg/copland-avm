Require Import Maps Event_system Term_system MonadVM ConcreteEvidence Appraisal_Evidence.
Require Import Impl_vm Helpers_VmSemantics VmSemantics.
Require Import Axioms_Io External_Facts Auto AutoApp.

Require Import Appraisal_Defs Impl_appraisal Impl_appraisal_alt (*MonadAM*).

Require Import Coq.Arith.Peano_dec.

Require Import StructTactics OptMonad.

Require Import Coq.Program.Tactics Coq.Program.Equality.

Require Import List.
Import ListNotations.

Require Import Lia.

Lemma appraisal_alt : forall ec1 ec2 ec2' ls et,

  Some ec1 = Impl_appraisal_alt.build_app_comp_evC et ls ->
  reconstruct_evP (evc ls et) ec2 ->
  ec2' = Impl_appraisal.build_app_comp_evC ec2 ->
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
    unfold checkNonceF.
    jkjke.
  -
    do_inv_recon.
    
    repeat ff.

    assert (e = (Impl_appraisal.build_app_comp_evC ec2)).
    {
      eapply IHec2.
      jkjke.
      invc H0.
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

    assert (e = (Impl_appraisal.build_app_comp_evC ec2)) by eauto.
    subst.
    unfold checkSig.
    unfold checkSigF.
    unfold checkSig.
    assert (checkSigBits H2 n n0 =
            checkSigBits (encodeEv ec2) n n0).
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
    ff.
  -
    do_inv_recon.
    repeat ff.
    unfold checkHashF.
    jkjke.
  -
    do_inv_recon.
    do_recon_inv. 
    repeat ff.
    assert (e = (Impl_appraisal.build_app_comp_evC ec2_1)) by eauto.
    assert (e0 = (Impl_appraisal.build_app_comp_evC ec2_2)) by eauto. 
    congruence.

  -
    do_inv_recon.
    do_recon_inv.
    repeat ff.
    assert (e = (Impl_appraisal.build_app_comp_evC ec2_1)) by eauto.   
    assert (e0 = (Impl_appraisal.build_app_comp_evC ec2_2)) by eauto.
    congruence.
Defined.

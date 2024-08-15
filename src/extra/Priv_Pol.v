Require Import Term_Defs Term Eqb_EvidenceT.

Require Import StructTactics.

Require Import PeanoNat Coq.Program.Tactics.


(*
Inductive EvSubT: EvidenceT -> EvidenceT -> Prop :=
| evsub_refl_t : forall e : EvidenceT, EvSubT e e
| uuSubT: forall e e' i tid l tpl,
    EvSubT e e' ->
    EvSubT e (asp_evt i l tpl tid e')
| ggSubT: forall e e' p,
    EvSubT e e' ->
    EvSubT e (gg p e')
| nnSubT: forall e e' i,
    EvSubT e e' ->
    EvSubT e (nonce_evt i e').
*)

Inductive req_EvidenceT: AnnoTerm -> Plc -> Plc -> EvidenceT -> EvidenceT -> Prop :=
| is_req_EvidenceT: forall annt t pp p q i e e',
    events annt pp e (req i p q t e') ->
    req_EvidenceT annt pp q e e'.

Fixpoint check_req (t:AnnoTerm) (pp:Plc) (q:Plc) (e:EvidenceT) (e':EvidenceT): bool :=
  match t with
  | aatt r rp t' => (eqb_EvidenceT e e' && (Nat.eqb q rp)) || (check_req t' rp q e e')
  | alseq r t1 t2 => (check_req t1 pp q e e') || (check_req t2 pp q (aeval t1 pp e) e')
  | abseq r s t1 t2 =>
    (check_req t1 pp q (splitEv_T_l s e) e') || (check_req t2 pp q (splitEv_T_r s e) e')
  | abpar r s t1 t2 =>
    (check_req t1 pp q (splitEv_T_l s e) e') || (check_req t2 pp q (splitEv_T_r s e) e')
  | _ => false
  end.

Lemma req_implies_check: forall t pp q e e',
    req_EvidenceT t pp q e e' -> check_req t pp q e e' = true.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a.
    +
      cbn.
      inversion H.
      solve_by_inversion.
    +
      cbn.
      inversion H.
      solve_by_inversion.
    +     
      cbn.
      inversion H.
      solve_by_inversion.
    +     
      cbn.
      inversion H.
      solve_by_inversion.
  -
    
    invc H.
    invc H0; subst; cbn.
    +
      rewrite Bool.orb_true_iff.
      left.
      rewrite Bool.andb_true_iff.
      split.
      ++
        rewrite eqb_eq_EvidenceT.
        tauto.
      ++
        apply Nat.eqb_refl.
    +
      rewrite Bool.orb_true_iff.
      right.
      eapply IHt.
      econstructor.
      eassumption.
  -
    cbn.
    invc H.
    invc H0.
    +
      rewrite Bool.orb_true_iff.
      left.
      eapply IHt1.
      econstructor.
      eassumption.
    +
      rewrite Bool.orb_true_iff.
      right.
      eapply IHt2.
      econstructor.
      eassumption.
  -
    cbn.
    invc H.
    invc H0.
    +
      rewrite Bool.orb_true_iff.
      left.
      eapply IHt1.
      econstructor.
      eassumption.
    +
      rewrite Bool.orb_true_iff.
      right.
      eapply IHt2.
      econstructor.
      eassumption.
  -
    cbn.
    invc H.
    invc H0.
    +
      rewrite Bool.orb_true_iff.
      left.
      eapply IHt1.
      econstructor.
      eassumption.
    +
      rewrite Bool.orb_true_iff.
      right.
      eapply IHt2.
      econstructor.
      eassumption.  
Defined.

Lemma check_implies_req: forall t pp q e e',
    check_req t pp q e e' = true -> req_EvidenceT t pp q e e'.
Proof.
  intros.
  generalizeEverythingElse t.
  induction t; intros.
  -
    destruct a;
      cbn; try solve_by_inversion.
  -
    cbn in *.
      rewrite Bool.orb_true_iff in H.
      destruct H.
      +
        rewrite Bool.andb_true_iff in H.
        destruct_conjs.
        econstructor.
        rewrite eqb_eq_EvidenceT in *.

        apply EqNat.beq_nat_true in H0.
        subst.
        eauto.
      +
        
        assert (req_EvidenceT t n q e e') by eauto.
        invc H0.
        econstructor.
        econstructor.
        eassumption.
  -
    cbn in *. 
    rewrite Bool.orb_true_iff in H.
    destruct_conjs.
    destruct H.
    +
      assert (req_EvidenceT t1 pp q e e') by eauto.
      invc H0.
      econstructor.
      apply evtslseql.
      eassumption.
    +
      assert (req_EvidenceT t2 pp q (aeval t1 pp e) e') by eauto.
      invc H0.
      econstructor.
      apply evtslseqr.
      eassumption.
  -
    cbn in *.
    rewrite Bool.orb_true_iff in H.
    destruct_conjs.
    destruct H.
    +
      assert (req_EvidenceT t1 pp q (splitEv_T_l s e) e') by eauto.
      invc H0.
      econstructor.
      apply evtsbseql.
      eassumption.
    +
      assert (req_EvidenceT t2 pp q (splitEv_T_r s e) e') by eauto.
      invc H0.
      econstructor.
      apply evtsbseqr.
      eassumption.
  -
    cbn in *.
    rewrite Bool.orb_true_iff in H.
    destruct_conjs.
    destruct H.
    +
      assert (req_EvidenceT t1 pp q (splitEv_T_l s e) e') by eauto.
      invc H0.
      econstructor.
      apply evtsbparl.
      eassumption.
    +
      assert (req_EvidenceT t2 pp q (splitEv_T_r s e) e') by eauto.
      invc H0.
      econstructor.
      apply evtsbparr.
      eassumption.
Defined.


(*

(* priv_pol p e --> allow place p to receive EvidenceT with shape e *)
Definition priv_pol := Plc -> EvidenceT -> Prop.

Check priv_pol.

Definition satisfies_policy (t:AnnoTerm) (pp:Plc) (ee:EvidenceT)
           (q:Plc) (es:EvidenceT) (pol:priv_pol) :=
  req_EvidenceT t pp ee q es -> (pol q es).

Definition test_term: Term := att 1 (asp CPY).
Definition test_term_anno := annotated test_term.
Compute test_term_anno.

Definition test_init_EvidenceT := asp_evt 1 [] 42 442 mt_evt.
Definition test_init_EvidenceT2 := asp_evt 2 [] 42 442 mt_evt.

Definition test_pol (p:Plc) (e:EvidenceT) :=
  match (p,e) with
  | (1, (asp_evt 1 [] 42 442 mt_evt)) => False
  | _ => True
  end.
    
    

Example test_term_satisfies_test_pol: forall pp ee q,
    satisfies_policy test_term_anno pp ee q mt_evttest_pol.
Proof.
  intros.
  cbn.
  unfold test_init_EvidenceT.
  unfold satisfies_policy.
  intros.
  unfold test_pol.
  cbv.
  intros.
  invc H.
  inv H1.
  auto.
  invc H1.
  auto.
  solve_by_inversion.
Qed.
*)
